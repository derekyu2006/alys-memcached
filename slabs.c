/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
/*
 * Slabs memory allocation, based on powers-of-N. Slabs are up to 1MB in size
 * and are divided into chunks. The chunk sizes start off at the size of the
 * "item" structure plus space for a small key and value. They increase by
 * a multiplier factor from there, up to half the maximum slab size. The last
 * slab size is always 1MB, since that's the maximum item size allowed by the
 * memcached protocol.
 */
#include "memcached.h"
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/resource.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <signal.h>
#include <assert.h>
#include <pthread.h>

//#define DEBUG_SLAB_MOVER

typedef struct {
  unsigned int size;  // 分配item的大小
  unsigned int perslab;   // 每个slab分配多少的item

  void *slots;       // 指向空闲的item链表
  unsigned int sl_curr;   // 空闲的item个数.

  unsigned int slabs;   // 已经分配了内存的slabs个数

  void **slab_list;     // slab数组, 每一个元素就是一个slab分配器, 这些分配器都分配相同尺寸的内存
  unsigned int list_size; //slab数组的大小, list_size >= slabs

  size_t requested; // 本slabclass_t分配出去的字节数
} slabclass_t;

// 数组元素虽然有MAX_NUMBER_OF_SLAB_CLASSES个，但实际上并不是全部都使用的。
// 实际使用的元素个数由power_largest指明
static slabclass_t slabclass[MAX_NUMBER_OF_SLAB_CLASSES];
static int power_largest; // slabclass数组中,已经使用了的元素个数
static size_t mem_limit = 0; // 用户设置的内存最大限制
static size_t mem_malloced = 0;

static bool mem_limit_reached = false;

//如果程序要求预先分配内存，而不是到了需要的时候才分配内存，那么
static void *mem_base = NULL; // mem_base就指向那块预先分配的内存.
static void *mem_current = NULL; // mem_current指向还可以使用的内存的开始位置.
static size_t mem_avail = 0; // mem_avail指明还有多少内存是可以使用的.

/**
 * Access to the slab allocator is protected by this lock
 */
static pthread_mutex_t slabs_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t slabs_rebalance_lock = PTHREAD_MUTEX_INITIALIZER;

static int do_slabs_newslab(const unsigned int id);
static void *memory_allocate(size_t size);
static void do_slabs_free(void *ptr, const size_t size, unsigned int id);

static void slabs_preallocate (const unsigned int maxslabs);

// 根据所申请的内存大小，确定好要向slabclass数组的哪个元素申请内存了
unsigned int slabs_clsid(const size_t size) {
  int res = POWER_SMALLEST;

  if (size == 0 || size > settings.item_size_max)
    return 0;
  // 因为slabclass数组中各个元素能分配的item大小是升序的
  // 所以从小到大直接判断即可在数组找到最小但又能满足的元素
  while (size > slabclass[res].size)
    if (res++ == power_largest)
      return power_largest;
  return res;
}

// 参数factor是扩容因子，默认值是1.25
// slab_sizes存放了指定每一类slab分配器分配item的大小.
void slabs_init(const size_t limit, const double factor, const bool prealloc, const uint32_t *slab_sizes) {
  int i = POWER_SMALLEST - 1; // 默认为0.
  // size由两部分组成: item结构体本身和这个item对应的数据
  unsigned int size = sizeof(item) + settings.chunk_size;

  mem_limit = limit; // 用户设置或者默认的内存最大限制

  if (prealloc) { // 如果开启了预分配而不是在需要的时候分配.
    mem_base = malloc(mem_limit);
    if (mem_base != NULL) {
      mem_current = mem_base;
      mem_avail = mem_limit;
    } else {
      fprintf(stderr, "Warning: Failed to allocate requested memory in"
          " one large chunk.\nWill allocate in smaller chunks\n");
    }
  }

  memset(slabclass, 0, sizeof(slabclass));

  while (++i < MAX_NUMBER_OF_SLAB_CLASSES-1) {
    if (slab_sizes != NULL) {
      if (slab_sizes[i-1] == 0)
        break;
      size = slab_sizes[i-1];
    } else if (size >= settings.slab_chunk_size_max / factor) { // 超出了规定的最大值.
      break;
    }

    // 保证8字节内存对齐.
    if (size % CHUNK_ALIGN_BYTES)
      size += CHUNK_ALIGN_BYTES - (size % CHUNK_ALIGN_BYTES);

    slabclass[i].size = size; // 每一个item的大小
    // 这样就可以计算出每一个slab_page可以分配多少个slab.
    slabclass[i].perslab = settings.slab_page_size / slabclass[i].size;
    if (slab_sizes == NULL)
      size *= factor;
  }

  power_largest = i;
  slabclass[power_largest].size = settings.slab_chunk_size_max;
  slabclass[power_largest].perslab = settings.slab_page_size / settings.slab_chunk_size_max;

  /* for the test suite:  faking of how much we've already malloc'd */
  {
    char *t_initial_malloc = getenv("T_MEMD_INITIAL_MALLOC");
    if (t_initial_malloc) {
      mem_malloced = (size_t)atol(t_initial_malloc);
    }

  }

  if (prealloc) {
    slabs_preallocate(power_largest);
  }
}

static void slabs_preallocate (const unsigned int maxslabs) {
  int i;
  unsigned int prealloc = 0;

  for (i = POWER_SMALLEST; i < MAX_NUMBER_OF_SLAB_CLASSES; i++) {
    if (++prealloc > maxslabs)
      return;
    if (do_slabs_newslab(i) == 0) { // 为每一个slabclass_t分配一个内存页
      fprintf(stderr, "Error while preallocating slab memory!\n"
        "If using -L or other prealloc options, max memory must be "
        "at least %d megabytes.\n", power_largest);
      exit(1);
    }
  }
}

static int grow_slab_list(const unsigned int id) {
  slabclass_t *p = &slabclass[id];
  if (p->slabs == p->list_size) {
    size_t new_size =  (p->list_size != 0) ? p->list_size * 2 : 16;
    void *new_list = realloc(p->slab_list, new_size * sizeof(void *));
    if (new_list == 0) return 0;
    p->list_size = new_size;
    p->slab_list = new_list;
  }
  return 1;
}

static void split_slab_page_into_freelist(char *ptr, const unsigned int id) {
  slabclass_t *p = &slabclass[id];
  int x;
  // 将ptr指向的内存划分成一个个的item. 一共划成perslab个并将这些item前后连起来
  // do_slabs_free函数本来是worker线程向内存池归还内存时调用的。但在这里
  // 新申请的内存也可以当作是向内存池归还内存。把内存注入内存池中
  for (x = 0; x < p->perslab; x++) {
    do_slabs_free(ptr, 0, id);
    ptr += p->size; // size是item的大小
  }
}

/* Fast FIFO queue */
static void *get_page_from_global_pool(void) {
  slabclass_t *p = &slabclass[SLAB_GLOBAL_PAGE_POOL];
  if (p->slabs < 1) {
    return NULL;
  }
  char *ret = p->slab_list[p->slabs - 1];
  p->slabs--;
  return ret;
}

static int do_slabs_newslab(const unsigned int id) {
  slabclass_t *p = &slabclass[id];
  slabclass_t *g = &slabclass[SLAB_GLOBAL_PAGE_POOL];
  int len = (settings.slab_reassign || settings.slab_chunk_size_max != settings.slab_page_size)
    ? settings.slab_page_size : p->size * p->perslab;
  char *ptr;

  if ((mem_limit && mem_malloced + len > mem_limit && p->slabs > 0
     && g->slabs == 0)) {
    mem_limit_reached = true;
    MEMCACHED_SLABS_SLABCLASS_ALLOCATE_FAILED(id);
    return 0;
  }

  if ((grow_slab_list(id) == 0) || (((ptr = get_page_from_global_pool()) == NULL) &&
                                    ((ptr = memory_allocate((size_t)len)) == 0))) {
    MEMCACHED_SLABS_SLABCLASS_ALLOCATE_FAILED(id);
    return 0;
  }

  memset(ptr, 0, (size_t)len);
  // 将这块内存切成一个个的item，当然item的大小有id所控制
  split_slab_page_into_freelist(ptr, id);

  // 将分配得到的内存页交由slab_list掌管
  p->slab_list[p->slabs++] = ptr;
  MEMCACHED_SLABS_SLABCLASS_ALLOCATE(id);

  return 1;
}

/* This calculation ends up adding sizeof(void *) to the item size. */
static void *do_slabs_alloc_chunked(const size_t size, slabclass_t *p, unsigned int id) {
  void *ret = NULL;
  item *it = NULL;
  int x;
  int csize = p->size - sizeof(item_chunk);
  unsigned int chunks_req = size / csize;
  if (size % csize != 0)
    chunks_req++;
  while (p->sl_curr < chunks_req) {
    if (do_slabs_newslab(id) == 0)
      break;
  }

  if (p->sl_curr >= chunks_req) {
    item_chunk *chunk = NULL;

    /* Configure the head item in the chain. */
    it = (item *)p->slots;
    p->slots = it->next;
    if (it->next) it->next->prev = 0;

    /* Squirrel away the "top chunk" into h_next for now */
    it->h_next = (item *)p->slots;
    assert(it->h_next != 0);
    chunk = (item_chunk *) it->h_next;

    /* roll down the chunks, marking them as such. */
    for (x = 0; x < chunks_req-1; x++) {
      chunk->it_flags &= ~ITEM_SLABBED;
      chunk->it_flags |= ITEM_CHUNK;
      /* Chunks always have a direct reference to the head item */
      chunk->head = it;
      chunk->size = p->size - sizeof(item_chunk);
      chunk->used = 0;
      chunk = chunk->next;
    }

    /* The final "next" is now the top of the slab freelist */
    p->slots = chunk;
    if (chunk && chunk->prev) {
      /* Disconnect the final chunk from the chain */
      chunk->prev->next = 0;
      chunk->prev = 0;
    }

    it->it_flags &= ~ITEM_SLABBED;
    it->it_flags |= ITEM_CHUNKED;
    it->refcount = 1;
    p->sl_curr -= chunks_req;
    ret = (void *)it;
  } else {
    ret = NULL;
  }

  return ret;
}

// 向slabclass申请一个item。在调用该函数之前，已经调用slabs_clsid函数确定
// 本次申请是向哪个slabclass_t申请item了，参数id就是指明是向哪个slabclass_t
// 申请item。如果该slabclass_t是有空闲item，那么就从空闲的item队列中分配一个
// 如果没有空闲item，那么就申请一个内存页。再从新申请的页中分配一个item
// 返回值为得到的item，如果没有内存了，返回NULL
static void *do_slabs_alloc(const size_t size, unsigned int id, uint64_t *total_bytes,
    unsigned int flags) {
  slabclass_t *p;
  void *ret = NULL;
  item *it = NULL;

  if (id < POWER_SMALLEST || id > power_largest) {
    MEMCACHED_SLABS_ALLOCATE_FAILED(size, 0);
    return NULL;
  }
  p = &slabclass[id]; // 根据id获取到具体的分配器
  assert(p->sl_curr == 0 || ((item *)p->slots)->slabs_clsid == 0);
  if (total_bytes != NULL) {
    *total_bytes = p->requested;
  }

  if (size <= p->size) {
    // 当前本slab分配器维护的item链表中如果没有空闲的item可用.
    // 那就新申请一个slab页并且从这个页中分配item.
    if (p->sl_curr == 0 && flags != SLABS_ALLOC_NO_NEWPAGE) {
      do_slabs_newslab(id);
    }

    // 经过上面的处理后， 本slab分配器维护的item链表中就有一个可用item
    // 那直接分配出去就ok了撒.
    if (p->sl_curr != 0) {
      it = (item *)p->slots;
      p->slots = it->next;
      if (it->next) it->next->prev = 0;
      it->it_flags &= ~ITEM_SLABBED; //修改写标记表示已经分配出去了.
      it->refcount = 1;
      p->sl_curr--;
      ret = (void *)it;
    } else {
      ret = NULL;
    }
  } else {
    ret = do_slabs_alloc_chunked(size, p, id);
  }

  if (ret) {
    p->requested += size; // 更新下本次分配出去的内存.
    MEMCACHED_SLABS_ALLOCATE(size, id, p->size, ret);
  } else {
    MEMCACHED_SLABS_ALLOCATE_FAILED(size, id);
  }

  return ret;
}

static void do_slabs_free_chunked(item *it, const size_t size, unsigned int id,
                  slabclass_t *p) {
  item_chunk *chunk = (item_chunk *) ITEM_data(it);
  size_t realsize = size;
  while (chunk) {
    realsize += sizeof(item_chunk);
    chunk = chunk->next;
  }
  chunk = (item_chunk *) ITEM_data(it);
  unsigned int chunks_found = 1;

  it->it_flags = ITEM_SLABBED;
  it->slabs_clsid = 0;
  it->prev = 0;
  it->next = (item *) chunk->next;
  assert(it->next);
  /* top chunk should already point back to head */
  assert(it->next && (void*)it->next->prev == (void*)chunk);
  chunk = chunk->next;
  chunk->prev = (item_chunk *)it;

  while (chunk) {
    assert(chunk->it_flags == ITEM_CHUNK);
    chunk->it_flags = ITEM_SLABBED;
    chunk->slabs_clsid = 0;
    chunks_found++;
    if (chunk->next) {
      chunk = chunk->next;
    } else {
      break;
    }
  }
  /* must have had nothing hanging off of the final chunk */
  assert(chunk && chunk->next == 0);
  /* Tail chunk, link the freelist here. */
  chunk->next = p->slots;
  if (chunk->next) chunk->next->prev = chunk;

  p->slots = it;
  p->sl_curr += chunks_found;
  p->requested -= size;

  return;
}


static void do_slabs_free(void *ptr, const size_t size, unsigned int id) {
  slabclass_t *p;
  item *it;

  assert(id >= POWER_SMALLEST && id <= power_largest);
  if (id < POWER_SMALLEST || id > power_largest)
    return;

  MEMCACHED_SLABS_FREE(size, id, ptr);
  p = &slabclass[id];

  it = (item *)ptr;
  if ((it->it_flags & ITEM_CHUNKED) == 0) {
    // 为item的it_flags添加ITEM_SLABBED属性, 标明这个item是在slab中没有被分配出去
    it->it_flags = ITEM_SLABBED;
    it->slabs_clsid = 0;
    // 由split_slab_page_into_freelist调用时，下面4行的作用是
    // 让这些item的prev和next相互指向，把这些item连起来.
    // 当本函数是在worker线程向内存池归还内存时调用，那么下面4行的作用是,
    // 使用链表头插法把该item插入到空闲item链表中。
    it->prev = 0;
    it->next = p->slots;
    if (it->next) it->next->prev = it;
    p->slots = it; // slot变量指向第一个空闲可以使用的item

    p->sl_curr++; // 空闲可以使用的item数量
    p->requested -= size; // 减少这个slabclass_t分配出去的字节数
  } else {
    do_slabs_free_chunked(it, size, id, p);
  }
  return;
}

static int nz_strcmp(int nzlength, const char *nz, const char *z) {
  int zlength=strlen(z);
  return (zlength == nzlength) && (strncmp(nz, z, zlength) == 0) ? 0 : -1;
}

bool get_stats(const char *stat_type, int nkey, ADD_STAT add_stats, void *c) {
  bool ret = true;

  if (add_stats != NULL) {
    if (!stat_type) {
      /* prepare general statistics for the engine */
      STATS_LOCK();
      APPEND_STAT("bytes", "%llu", (unsigned long long)stats_state.curr_bytes);
      APPEND_STAT("curr_items", "%llu", (unsigned long long)stats_state.curr_items);
      APPEND_STAT("total_items", "%llu", (unsigned long long)stats.total_items);
      STATS_UNLOCK();
      if (settings.slab_automove > 0) {
        pthread_mutex_lock(&slabs_lock);
        APPEND_STAT("slab_global_page_pool", "%u", slabclass[SLAB_GLOBAL_PAGE_POOL].slabs);
        pthread_mutex_unlock(&slabs_lock);
      }
      item_stats_totals(add_stats, c);
    } else if (nz_strcmp(nkey, stat_type, "items") == 0) {
      item_stats(add_stats, c);
    } else if (nz_strcmp(nkey, stat_type, "slabs") == 0) {
      slabs_stats(add_stats, c);
    } else if (nz_strcmp(nkey, stat_type, "sizes") == 0) {
      item_stats_sizes(add_stats, c);
    } else if (nz_strcmp(nkey, stat_type, "sizes_enable") == 0) {
      item_stats_sizes_enable(add_stats, c);
    } else if (nz_strcmp(nkey, stat_type, "sizes_disable") == 0) {
      item_stats_sizes_disable(add_stats, c);
    } else {
      ret = false;
    }
  } else {
    ret = false;
  }

  return ret;
}

/*@null@*/
static void do_slabs_stats(ADD_STAT add_stats, void *c) {
  int i, total;
  /* Get the per-thread stats which contain some interesting aggregates */
  struct thread_stats thread_stats;
  threadlocal_stats_aggregate(&thread_stats);

  total = 0;
  for(i = POWER_SMALLEST; i <= power_largest; i++) {
    slabclass_t *p = &slabclass[i];
    if (p->slabs != 0) {
      uint32_t perslab, slabs;
      slabs = p->slabs;
      perslab = p->perslab;

      char key_str[STAT_KEY_LEN];
      char val_str[STAT_VAL_LEN];
      int klen = 0, vlen = 0;

      APPEND_NUM_STAT(i, "chunk_size", "%u", p->size);
      APPEND_NUM_STAT(i, "chunks_per_page", "%u", perslab);
      APPEND_NUM_STAT(i, "total_pages", "%u", slabs);
      APPEND_NUM_STAT(i, "total_chunks", "%u", slabs * perslab);
      APPEND_NUM_STAT(i, "used_chunks", "%u",
              slabs*perslab - p->sl_curr);
      APPEND_NUM_STAT(i, "free_chunks", "%u", p->sl_curr);
      /* Stat is dead, but displaying zero instead of removing it. */
      APPEND_NUM_STAT(i, "free_chunks_end", "%u", 0);
      APPEND_NUM_STAT(i, "mem_requested", "%llu",
              (unsigned long long)p->requested);
      APPEND_NUM_STAT(i, "get_hits", "%llu",
          (unsigned long long)thread_stats.slab_stats[i].get_hits);
      APPEND_NUM_STAT(i, "cmd_set", "%llu",
          (unsigned long long)thread_stats.slab_stats[i].set_cmds);
      APPEND_NUM_STAT(i, "delete_hits", "%llu",
          (unsigned long long)thread_stats.slab_stats[i].delete_hits);
      APPEND_NUM_STAT(i, "incr_hits", "%llu",
          (unsigned long long)thread_stats.slab_stats[i].incr_hits);
      APPEND_NUM_STAT(i, "decr_hits", "%llu",
          (unsigned long long)thread_stats.slab_stats[i].decr_hits);
      APPEND_NUM_STAT(i, "cas_hits", "%llu",
          (unsigned long long)thread_stats.slab_stats[i].cas_hits);
      APPEND_NUM_STAT(i, "cas_badval", "%llu",
          (unsigned long long)thread_stats.slab_stats[i].cas_badval);
      APPEND_NUM_STAT(i, "touch_hits", "%llu",
          (unsigned long long)thread_stats.slab_stats[i].touch_hits);
      total++;
    }
  }

  /* add overall slab stats and append terminator */

  APPEND_STAT("active_slabs", "%d", total);
  APPEND_STAT("total_malloced", "%llu", (unsigned long long)mem_malloced);
  add_stats(NULL, 0, NULL, 0, c);
}

static void *memory_allocate(size_t size) {
  void *ret;

  if (mem_base == NULL) {
    ret = malloc(size);
  } else {
    ret = mem_current;

    if (size > mem_avail) {
      return NULL;
    }

    if (size % CHUNK_ALIGN_BYTES) {
      size += CHUNK_ALIGN_BYTES - (size % CHUNK_ALIGN_BYTES);
    }

    mem_current = ((char*)mem_current) + size;
    if (size < mem_avail) {
      mem_avail -= size;
    } else {
      mem_avail = 0;
    }
  }
  mem_malloced += size;

  return ret;
}

/* Must only be used if all pages are item_size_max */
static void memory_release() {
  void *p = NULL;
  if (mem_base != NULL)
    return;

  if (!settings.slab_reassign)
    return;

  while (mem_malloced > mem_limit &&
      (p = get_page_from_global_pool()) != NULL) {
    free(p);
    mem_malloced -= settings.item_size_max;
  }
}

void *slabs_alloc(size_t size, unsigned int id, uint64_t *total_bytes,
    unsigned int flags) {
  void *ret;

  pthread_mutex_lock(&slabs_lock);
  ret = do_slabs_alloc(size, id, total_bytes, flags);
  pthread_mutex_unlock(&slabs_lock);
  return ret;
}

void slabs_free(void *ptr, size_t size, unsigned int id) {
  pthread_mutex_lock(&slabs_lock);
  do_slabs_free(ptr, size, id);
  pthread_mutex_unlock(&slabs_lock);
}

void slabs_stats(ADD_STAT add_stats, void *c) {
  pthread_mutex_lock(&slabs_lock);
  do_slabs_stats(add_stats, c);
  pthread_mutex_unlock(&slabs_lock);
}

static bool do_slabs_adjust_mem_limit(size_t new_mem_limit) {
  /* Cannot adjust memory limit at runtime if prealloc'ed */
  if (mem_base != NULL)
    return false;
  settings.maxbytes = new_mem_limit;
  mem_limit = new_mem_limit;
  mem_limit_reached = false; /* Will reset on next alloc */
  memory_release(); /* free what might already be in the global pool */
  return true;
}

bool slabs_adjust_mem_limit(size_t new_mem_limit) {
  bool ret;
  pthread_mutex_lock(&slabs_lock);
  ret = do_slabs_adjust_mem_limit(new_mem_limit);
  pthread_mutex_unlock(&slabs_lock);
  return ret;
}

void slabs_adjust_mem_requested(unsigned int id, size_t old, size_t ntotal)
{
  pthread_mutex_lock(&slabs_lock);
  slabclass_t *p;
  if (id < POWER_SMALLEST || id > power_largest) {
    fprintf(stderr, "Internal error! Invalid slab class\n");
    abort();
  }

  p = &slabclass[id];
  p->requested = p->requested - old + ntotal;
  pthread_mutex_unlock(&slabs_lock);
}

unsigned int slabs_available_chunks(const unsigned int id, bool *mem_flag,
    uint64_t *total_bytes, unsigned int *chunks_perslab) {
  unsigned int ret;
  slabclass_t *p;

  pthread_mutex_lock(&slabs_lock);
  p = &slabclass[id];
  ret = p->sl_curr;
  if (mem_flag != NULL)
    *mem_flag = mem_limit_reached;
  if (total_bytes != NULL)
    *total_bytes = p->requested;
  if (chunks_perslab != NULL)
    *chunks_perslab = p->perslab;
  pthread_mutex_unlock(&slabs_lock);
  return ret;
}

static pthread_cond_t slab_rebalance_cond = PTHREAD_COND_INITIALIZER;
static volatile int do_run_slab_thread = 1;
static volatile int do_run_slab_rebalance_thread = 1;

#define DEFAULT_SLAB_BULK_CHECK 1
int slab_bulk_check = DEFAULT_SLAB_BULK_CHECK;

static int slab_rebalance_start(void) {
  slabclass_t *s_cls;
  int no_go = 0;

  // 只要对slab区操作就要加锁,这里的加锁是针对全局的slab_id[1~63]
  // 所以锁的开销稍微大一些
  pthread_mutex_lock(&slabs_lock);

  if (slab_rebal.s_clsid < POWER_SMALLEST ||
    slab_rebal.s_clsid > power_largest  ||
    slab_rebal.d_clsid < SLAB_GLOBAL_PAGE_POOL ||
    slab_rebal.d_clsid > power_largest  ||
    slab_rebal.s_clsid == slab_rebal.d_clsid)
    no_go = -2;

  // 取出s_clsid信息
  s_cls = &slabclass[slab_rebal.s_clsid];

  // 增大slab数组的大小, 用来存放可能移过来的chunk.
  if (!grow_slab_list(slab_rebal.d_clsid)) {
    no_go = -1;
  }

  // 源slab页太少了, 无法分一个页给别人.
  if (s_cls->slabs < 2)
    no_go = -3;

  if (no_go != 0) {
    pthread_mutex_unlock(&slabs_lock);
    return no_go;
  }

  // 标志将源slab class的第几个内存页分给目标slab class
  // 这里是默认是将第一个内存页分给目标slab class
  s_cls->killing = 1;

  // 记录要移动的页的信息。slab_start指向页的开始位置.
  // slab_end指向页的结束位置。slab_pos则记录当前处理的位置(item)
  slab_rebal.slab_start = s_cls->slab_list[s_cls->killing - 1];
  slab_rebal.slab_end   = (char *)slab_rebal.slab_start +
    (s_cls->size * s_cls->perslab);
  slab_rebal.slab_pos   = slab_rebal.slab_start;
  slab_rebal.done     = 0;

  // 要rebalance线程接下来进行内存页移动
  slab_rebalance_signal = 2;

  pthread_mutex_unlock(&slabs_lock);

  STATS_LOCK();
  stats_state.slab_reassign_running = true;
  STATS_UNLOCK();

  return 0;
}

/* CALLED WITH slabs_lock HELD */
static void *slab_rebalance_alloc(const size_t size, unsigned int id) {
  slabclass_t *s_cls;
  s_cls = &slabclass[slab_rebal.s_clsid];
  int x;
  item *new_it = NULL;

  for (x = 0; x < s_cls->perslab; x++) {
    new_it = do_slabs_alloc(size, id, NULL, SLABS_ALLOC_NO_NEWPAGE);
    /* check that memory isn't within the range to clear */
    if (new_it == NULL) {
      break;
    }
    if ((void *)new_it >= slab_rebal.slab_start
      && (void *)new_it < slab_rebal.slab_end) {
      /* Pulled something we intend to free. Mark it as freed since
       * we've already done the work of unlinking it from the freelist.
       */
      s_cls->requested -= size;
      new_it->refcount = 0;
      new_it->it_flags = ITEM_SLABBED|ITEM_FETCHED;
#ifdef DEBUG_SLAB_MOVER
      memcpy(ITEM_key(new_it), "deadbeef", 8);
#endif
      new_it = NULL;
      slab_rebal.inline_reclaim++;
    } else {
      break;
    }
  }
  return new_it;
}

/* CALLED WITH slabs_lock HELD */
/* detatches item/chunk from freelist. */
static void slab_rebalance_cut_free(slabclass_t *s_cls, item *it) {
  /* Ensure this was on the freelist and nothing else. */
  assert(it->it_flags == ITEM_SLABBED);
  if (s_cls->slots == it) {
    s_cls->slots = it->next;
  }
  if (it->next) it->next->prev = it->prev;
  if (it->prev) it->prev->next = it->next;
  s_cls->sl_curr--;
}

enum move_status {
  MOVE_PASS=0, MOVE_FROM_SLAB, MOVE_FROM_LRU, MOVE_BUSY, MOVE_LOCKED
};

static int slab_rebalance_move(void) {
  slabclass_t *s_cls;
  int x;
  int was_busy = 0;
  int refcount = 0;
  uint32_t hv;
  void *hold_lock;
  enum move_status status = MOVE_PASS;

  pthread_mutex_lock(&slabs_lock);

  // 取出源slab信息
  s_cls = &slabclass[slab_rebal.s_clsid];

  // 这里默认一次只循环一次,也就是在移除chunk里面item的时候,一次只移除一个item
  // 不过可以在启动的时候设定这个slab_bulk_check循环次数
  // 尽可能的还是把这个变量设置小一些,保证只循环一次就退出循环,因为这样可以减小锁的颗粒度
  // 可以看到上面slab是全局锁,如果我们当前这个slab id一直占用锁,会导致其它的slab id
  // 也都无法操作,所以这里每次循环处理完一个item之后马上释放锁,然后在获取锁在进行处理
  for (x = 0; x < slab_bulk_check; x++) {
    hv = 0;
    hold_lock = NULL;
    item *it = slab_rebal.slab_pos; // 获取item
    item_chunk *ch = NULL;
    status = MOVE_PASS;
    if (it->it_flags & ITEM_CHUNK) {
      /* This chunk is a chained part of a larger item. */
      ch = (item_chunk *) it;
      /* Instead, we use the head chunk to find the item and effectively
       * lock the entire structure. If a chunk has ITEM_CHUNK flag, its
       * head cannot be slabbed, so the normal routine is safe. */
      it = ch->head;
      assert(it->it_flags & ITEM_CHUNKED);
    }

    // 如果it_flags&ITEM_SLABBED为真，那么就说明这个item
    // 根本就没有分配出去。如果为假，那么说明这个item被分配
    // 出去了，但处于归还途中。参考do_item_get函数里面的
    // 判断语句，有slab_rebalance_signal作为判断条件的那个
    if (it->it_flags != (ITEM_SLABBED|ITEM_FETCHED)) {
      if (it->it_flags & ITEM_SLABBED) { // 没有分配出去, 即时空闲的item.
        // 把当前item从空闲s_cls->slots链表移动出来，因为我们要回收这个chunk
        // 所以这个chunk里面的item就不能在被当前slab引用了.
        if (s_cls->slots == it) {
          s_cls->slots = it->next;
        }
        if (it->next) it->next->prev = it->prev;
        if (it->prev) it->prev->next = it->next;
        s_cls->sl_curr--;
        status = MOVE_FROM_SLAB;
      } else if ((it->it_flags & ITEM_LINKED) != 0) { // 是否被使用的item
        // 获取哈希锁并试图锁它, 如果锁失败了, 则代表这个item正在忙
        hv = hash(ITEM_key(it), it->nkey);
        if ((hold_lock = item_trylock(hv)) == NULL) {
          status = MOVE_LOCKED;
        } else { // 说明这个item虽然被使用但当前没有被访问.
          refcount = refcount_incr(&it->refcount); // 更新下引用计数.
          if (refcount == 2) {
            //double check, 判断一次是否被使用的item
            if ((it->it_flags & ITEM_LINKED) != 0) {
              // 把这个被使用的item复制到其他chunk下
              status = MOVE_FROM_LRU;
            } else {
              // 如果不是则可能刚巧同一时间被删除了,所以改成正在忙的状态
              // 下次循环再看一次
              status = MOVE_BUSY;
            }
          } else {
            //如果引用+1不等于2则代表其他线程正在操作该item,正在忙
            status = MOVE_BUSY;
          }

          // 当这个item当前正在被working线程访问的时候
          // 这里就放弃对它的移动操作. 恢复现场.
          if (status == MOVE_BUSY) {
            refcount_decr(&it->refcount);
            item_trylock_unlock(hold_lock);
          }
        }
      } else {
        status = MOVE_BUSY;
      }
    }

    int save_item = 0;
    item *new_it = NULL;
    size_t ntotal = 0;
    switch (status) {
      case MOVE_FROM_LRU:
        // 当前item总占用字节数
        ntotal = ITEM_ntotal(it);
        if (ch == NULL && (it->it_flags & ITEM_CHUNKED)) {
          ntotal = s_cls->size;
        }
        // 判断当前是否到期了.
        if ((it->exptime != 0 && it->exptime < current_time)
            || item_is_flushed(it)) {
          save_item = 0;
        } else if (ch == NULL &&
            (new_it = slab_rebalance_alloc(ntotal, slab_rebal.s_clsid)) == NULL) {
          save_item = 0;
          slab_rebal.evictions_nomem++;
        } else if (ch != NULL &&
            (new_it = slab_rebalance_alloc(s_cls->size, slab_rebal.s_clsid)) == NULL) {
          save_item = 0;
          slab_rebal.evictions_nomem++;
        } else {
          save_item = 1;
        }
        pthread_mutex_unlock(&slabs_lock);
        unsigned int requested_adjust = 0;
        //把当前的item内容copy到新的new_it下
        if (save_item) {
          if (ch == NULL) {
            memcpy(new_it, it, ntotal);
            new_it->prev = 0;
            new_it->next = 0;
            new_it->h_next = 0;
            new_it->it_flags &= ~ITEM_LINKED;
            // 把当前item引用全部释放掉, 在把新的new_it全部引用上
            // 这样就相当于把当前item移动copy到其他chunk下了,把当前item位置腾出来了
            new_it->refcount = 0;
            do_item_replace(it, new_it, hv);
            /* Need to walk the chunks and repoint head  */
            if (new_it->it_flags & ITEM_CHUNKED) {
              item_chunk *fch = (item_chunk *) ITEM_data(new_it);
              fch->next->prev = fch;
              while (fch) {
                fch->head = new_it;
                fch = fch->next;
              }
            }
            it->refcount = 0;
            it->it_flags = ITEM_SLABBED|ITEM_FETCHED;
#ifdef DEBUG_SLAB_MOVER
            memcpy(ITEM_key(it), "deadbeef", 8);
#endif
            slab_rebal.rescues++;
            requested_adjust = ntotal;
          } else {
            item_chunk *nch = (item_chunk *) new_it;
            /* Chunks always have head chunk (the main it) */
            ch->prev->next = nch;
            if (ch->next)
              ch->next->prev = nch;
            memcpy(nch, ch, ch->used + sizeof(item_chunk));
            ch->refcount = 0;
            ch->it_flags = ITEM_SLABBED|ITEM_FETCHED;
            slab_rebal.chunk_rescues++;
#ifdef DEBUG_SLAB_MOVER
            memcpy(ITEM_key((item *)ch), "deadbeef", 8);
#endif
            refcount_decr(&it->refcount);
            requested_adjust = s_cls->size;
          }
        } else { // 把当前item引用全部释放掉
          ntotal = ITEM_ntotal(it);
          do_item_unlink(it, hv);
          slabs_free(it, ntotal, slab_rebal.s_clsid);
          slab_rebal.busy_items++;
          was_busy++;
        }
        item_trylock_unlock(hold_lock);
        pthread_mutex_lock(&slabs_lock);
        // 把当前item占用的字节数从总占用字节数里面减去
        s_cls->requested -= requested_adjust;
        break;
      case MOVE_FROM_SLAB:
        it->refcount = 0;
        it->it_flags = ITEM_SLABBED|ITEM_FETCHED;
#ifdef DEBUG_SLAB_MOVER
        memcpy(ITEM_key(it), "deadbeef", 8);
#endif
        break;
      case MOVE_BUSY:
      case MOVE_LOCKED:
        // 记录一下正在忙的item数量
        slab_rebal.busy_items++;
        was_busy++;
        break;
      case MOVE_PASS:
        break;
    }

    // 如果本次item正在忙没有移动走, 那么也会把指针移动到下个item的位置处理下个item
    // 等这一圈全部循环完之后,回过头来发现刚才有正在忙的item没有移动走,
    // 那么会再继续循环一轮直到把chunk内所有item全部移除完毕。
    slab_rebal.slab_pos = (char *)slab_rebal.slab_pos + s_cls->size;
    if (slab_rebal.slab_pos >= slab_rebal.slab_end)
      break;
  }

  // 判断是否处理完所有item
  if (slab_rebal.slab_pos >= slab_rebal.slab_end) {
    // 如果有则重新把slab_pos指针重置到开始位置,然后重新一轮循环处理
    if (slab_rebal.busy_items) {
      slab_rebal.slab_pos = slab_rebal.slab_start;
      STATS_LOCK();
      stats.slab_reassign_busy_items += slab_rebal.busy_items;
      STATS_UNLOCK();
      // 清零
      slab_rebal.busy_items = 0;
    } else {
      // 当前chunk内所有item移除完毕
      slab_rebal.done++;
    }
  }

  pthread_mutex_unlock(&slabs_lock);

  return was_busy;
}

static void slab_rebalance_finish(void) {
  slabclass_t *s_cls;
  slabclass_t *d_cls;
  int x;
  uint32_t rescues;
  uint32_t evictions_nomem;
  uint32_t inline_reclaim;
  uint32_t chunk_rescues;

  pthread_mutex_lock(&slabs_lock);

  s_cls = &slabclass[slab_rebal.s_clsid];
  d_cls = &slabclass[slab_rebal.d_clsid];

#ifdef DEBUG_SLAB_MOVER
  /* If the algorithm is broken, live items can sneak in. */
  slab_rebal.slab_pos = slab_rebal.slab_start;
  while (1) {
    item *it = slab_rebal.slab_pos;
    assert(it->it_flags == (ITEM_SLABBED|ITEM_FETCHED));
    assert(memcmp(ITEM_key(it), "deadbeef", 8) == 0);
    it->it_flags = ITEM_SLABBED|ITEM_FETCHED;
    slab_rebal.slab_pos = (char *)slab_rebal.slab_pos + s_cls->size;
    if (slab_rebal.slab_pos >= slab_rebal.slab_end)
      break;
  }
#endif

  s_cls->slabs--; // 源slab class的内存页数减一
  for (x = 0; x < s_cls->slabs; x++) {
    s_cls->slab_list[x] = s_cls->slab_list[x+1];
  }

  d_cls->slab_list[d_cls->slabs++] = slab_rebal.slab_start;
  if (slab_rebal.d_clsid > SLAB_GLOBAL_PAGE_POOL) {
    // 内存页所有字节清零, 这个也很重要的
    memset(slab_rebal.slab_start, 0, (size_t)settings.item_size_max);
    // 按照目标slab class的item尺寸进行划分这个页
    // 并且将这个页的内存并入到目标slab class的空闲item队列中
    split_slab_page_into_freelist(slab_rebal.slab_start,
      slab_rebal.d_clsid);
  } else if (slab_rebal.d_clsid == SLAB_GLOBAL_PAGE_POOL) {
    memory_release();
  }

  // 做一些清零的操作.
  slab_rebal.done     = 0;
  slab_rebal.s_clsid  = 0;
  slab_rebal.d_clsid  = 0;
  slab_rebal.slab_start = NULL;
  slab_rebal.slab_end   = NULL;
  slab_rebal.slab_pos   = NULL;
  evictions_nomem  = slab_rebal.evictions_nomem;
  inline_reclaim = slab_rebal.inline_reclaim;
  rescues   = slab_rebal.rescues;
  chunk_rescues = slab_rebal.chunk_rescues;
  slab_rebal.evictions_nomem  = 0;
  slab_rebal.inline_reclaim = 0;
  slab_rebal.rescues  = 0;

  slab_rebalance_signal = 0; // rebalance线程完成工作后，再次进入休眠状态

  pthread_mutex_unlock(&slabs_lock);

  STATS_LOCK();
  stats.slabs_moved++;
  stats.slab_reassign_rescues += rescues;
  stats.slab_reassign_evictions_nomem += evictions_nomem;
  stats.slab_reassign_inline_reclaim += inline_reclaim;
  stats.slab_reassign_chunk_rescues += chunk_rescues;
  stats_state.slab_reassign_running = false;
  STATS_UNLOCK();

  if (settings.verbose > 1) {
    fprintf(stderr, "finished a slab move\n");
  }
}

static void *slab_rebalance_thread(void *arg) {
  int was_busy = 0;
  mutex_lock(&slabs_rebalance_lock);

  while (do_run_slab_rebalance_thread) {
    if (slab_rebalance_signal == 1) {
      // 标志要移动的内存页的信息, 并将slab_rebalance_signal赋值为2
      // slab_rebal.done赋值为0，表示没有完成
      if (slab_rebalance_start() < 0) {
        slab_rebalance_signal = 0;
      }

      was_busy = 0;
    } else if (slab_rebalance_signal && slab_rebal.slab_start != NULL) {
      was_busy = slab_rebalance_move(); // 进行内存页迁移操作
    }

    if (slab_rebal.done) { // 完成内存页重分配操作
      slab_rebalance_finish();
    } else if (was_busy) {
      usleep(50); // 有worker线程在使用内存页上的item
    }

    if (slab_rebalance_signal == 0) { // 一开始就在这里休眠
      pthread_cond_wait(&slab_rebalance_cond, &slabs_rebalance_lock);
    }
  }
  return NULL;
}

/* Iterate at most once through the slab classes and pick a "random" source.
 * I like this better than calling rand() since rand() is slow enough that we
 * can just check all of the classes once instead.
 */
static int slabs_reassign_pick_any(int dst) {
  static int cur = POWER_SMALLEST - 1;
  int tries = power_largest - POWER_SMALLEST + 1;
  for (; tries > 0; tries--) {
    cur++;
    if (cur > power_largest)
      cur = POWER_SMALLEST;
    if (cur == dst)
      continue;
    if (slabclass[cur].slabs > 1) {
      return cur;
    }
  }
  return -1;
}

static enum reassign_result_type do_slabs_reassign(int src, int dst) {
  if (slab_rebalance_signal != 0)
    return REASSIGN_RUNNING;

  if (src == dst)
    return REASSIGN_SRC_DST_SAME;

  /* Special indicator to choose ourselves. */
  if (src == -1) {
    src = slabs_reassign_pick_any(dst);
    /* TODO: If we end up back at -1, return a new error type */
  }

  if (src < POWER_SMALLEST    || src > power_largest ||
    dst < SLAB_GLOBAL_PAGE_POOL || dst > power_largest)
    return REASSIGN_BADCLASS;

  // 如果该 slab id 下的 chunk 小于2块则不回收了.
  if (slabclass[src].slabs < 2)
    return REASSIGN_NOSPARE;

  slab_rebal.s_clsid = src;
  slab_rebal.d_clsid = dst;

  slab_rebalance_signal = 1;
  pthread_cond_signal(&slab_rebalance_cond);

  return REASSIGN_OK;
}

enum reassign_result_type slabs_reassign(int src, int dst) {
  enum reassign_result_type ret;
  if (pthread_mutex_trylock(&slabs_rebalance_lock) != 0) {
    return REASSIGN_RUNNING;
  }
  ret = do_slabs_reassign(src, dst);
  pthread_mutex_unlock(&slabs_rebalance_lock);
  return ret;
}

/* If we hold this lock, rebalancer can't wake up or move */
void slabs_rebalancer_pause(void) {
  pthread_mutex_lock(&slabs_rebalance_lock);
}

void slabs_rebalancer_resume(void) {
  pthread_mutex_unlock(&slabs_rebalance_lock);
}

static pthread_t rebalance_tid;

int start_slab_maintenance_thread(void) {
  int ret;
  slab_rebalance_signal = 0;
  slab_rebal.slab_start = NULL;
  char *env = getenv("MEMCACHED_SLAB_BULK_CHECK");
  if (env != NULL) {
    slab_bulk_check = atoi(env);
    if (slab_bulk_check == 0) {
      slab_bulk_check = DEFAULT_SLAB_BULK_CHECK;
    }
  }

  if (pthread_cond_init(&slab_rebalance_cond, NULL) != 0) {
    fprintf(stderr, "Can't intiialize rebalance condition\n");
    return -1;
  }
  pthread_mutex_init(&slabs_rebalance_lock, NULL);

  if ((ret = pthread_create(&rebalance_tid, NULL,
      slab_rebalance_thread, NULL)) != 0) {
    fprintf(stderr, "Can't create rebal thread: %s\n", strerror(ret));
    return -1;
  }
  return 0;
}

/* The maintenance thread is on a sleep/loop cycle, so it should join after a
 * short wait */
void stop_slab_maintenance_thread(void) {
  mutex_lock(&slabs_rebalance_lock);
  do_run_slab_thread = 0;
  do_run_slab_rebalance_thread = 0;
  pthread_cond_signal(&slab_rebalance_cond);
  pthread_mutex_unlock(&slabs_rebalance_lock);

  /* Wait for the maintenance thread to stop */
  pthread_join(rebalance_tid, NULL);
}
