#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <string>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/uio.h>
#include <unistd.h>
#include <vector>

int dice = 0;

void *(*malloc_func)(size_t);
void *(*realloc_func)(void *, size_t);
ssize_t (*pread_func)(int fd, void *buf, size_t size, off_t offset);
int (*close_func)(int fd);

void hook() {
  malloc_func = malloc;
  realloc_func = realloc;
  pread_func = pread;
  close_func = close;
}

void *call_malloc(size_t x) {
  int k = rand() % 10;
  if (!dice && k == 7)
    return NULL;
  return malloc_func(x);
}

void *call_realloc(void *src, size_t size) {
  int k = rand() % 10;
  if (!dice && k == 7)
    return NULL;
  return realloc_func(src, size);
}

int call_pread(int fd, void *buf, size_t size, off_t offset) {

  int k = rand() % 100;
  if (!dice && k == 7)
    return k;
  return pread_func(fd, buf, size, offset);
}

int call_close(int fd) {

  int k = rand() % 10;
  if (!dice && k == 7)
    return -1;
  return close(fd);
}

// #define malloc(x) call_malloc(x)
// #define realloc(src, x) call_realloc(src, x)
// #define pread(fd, buf, size, offset) call_pread(fd, buf, size, offset)
// #define close(fd) call_close(fd)

#include "../lsmt_ro_file.c"
#include "lsmt_ro_file.h"
#include "gtest/gtest.h"

#define RAND_READN 16 * 1024
#define RAND_RANGE                                                             \
  (uint64_t)(rand() % (1 << 20)), (uint32_t)(rand() % (1 << 6) + 1)
//生成一个1M以内，长度不超过64的线段

void rand_segment(struct segment *s) {
  s->offset = (uint64_t)(rand() % (1 << 12));
  s->length = (uint64_t)(rand() % ((1 << 10) + 1));
}

TEST(LSMT_RO, lowerbound) {
  struct segment_mapping *mappings = NULL;
  size_t n = 10;
  int test_count = 10;
  mappings =
      (struct segment_mapping *)calloc(n, sizeof(struct segment_mapping));
  uint64_t last_offset = 0;
  for (int i = 0; i < n; i++) {
    rand_segment((struct segment *)&mappings[i]);
    mappings[i].offset += last_offset;
    last_offset = segment_end((segment *)&mappings[i]);
  }
  struct lsmt_ro_index *index =
      create_memory_index(mappings, n, 0, INT64_MAX, true);
  if (!index) {
    free(mappings);
    return;
  }
  for (int i = 0; i < test_count; i++) {
    struct segment s;
    rand_segment(&s);
    print_segment(&s);
    const struct segment_mapping *lowerbound =
        ro_index_lower_bound(index, s.offset);
  }
  free(index);
  free(mappings);
}

TEST(LSMT_RO, err_index_order) {

  struct segment_mapping *mappings = NULL;
  int n = 10;
  mappings =
      (struct segment_mapping *)calloc(n, sizeof(struct segment_mapping));
  for (int i = 0; i < n; i++) {
    rand_segment((struct segment *)&mappings[i]);
    PRINT_INFO("generate index: [ %lu, %u ]", mappings[i].offset,
               mappings[i].length);
  }
  verify_mapping_order(mappings, n);
  memset(mappings, 0, sizeof(mappings));

  uint64_t last_offset = 0;
  PRINT_INFO("create mappings (size： %d)", n);
  for (int i = 0; i < n; i++) {
    rand_segment((struct segment *)&mappings[i]);
    mappings[i].offset += last_offset;
    last_offset = segment_end((segment *)&mappings[i]);
    PRINT_INFO("generate index: [ %lu, %u ] %lu", mappings[i].offset,
               mappings[i].length, last_offset);
  }
  create_memory_index(mappings, n, 0, 10, false);
  free(mappings);
}

TEST(LSMT_RO, merge_indexes) {
  struct segment_mapping m4[5] = {{100, 60, 0},
                                  {200, 50, 60},
                                  {300, 40, 110},
                                  {400, 100, 150},
                                  {510, 30, 250}};
  struct segment_mapping m3[5] = {
      {90, 20, 0}, {175, 30, 20}, {220, 10, 50}, {370, 15, 60}, {800, 10, 75}};
  struct segment_mapping m2[1] = {{0, 1000, 0}};
  struct lsmt_ro_index *i4 = create_memory_index(m4, 5, 0, INT64_MAX, true);
  struct lsmt_ro_index *i3 = create_memory_index(m3, 5, 0, INT64_MAX, true);
  struct lsmt_ro_index *i2 = create_memory_index(m2, 1, 0, INT64_MAX, true);
  struct lsmt_ro_index *idx[3] = {i4, i3, i2};
  struct lsmt_ro_index *mi = NULL;
  if (!i2 || !i3 || !i4) {
    goto err_malloc;
  }
  mi = merge_memory_indexes(idx, 3);
  if (mi) {
    for (const struct segment_mapping *p = mi->pbegin; p != mi->pend; p++) {
      print_segment_mapping(p);
    }
    free(mi);
  }
  return;
err_malloc:
  free(i2);
  free(i3);
  free(i4);
}

#define IMAGE_RO_LAYERS 5
TEST(LSMT_RO, load_index) {
  const char *index = "/tmp/img_index.0.lsmt";
  const char *data = "/tmp/img_data.0.lsmt";
  int fd = open(index, O_RDONLY);
  if (fd == -1) {
    PRINT_ERROR("errno: %d msg: %s", errno, strerror(errno));
    return;
  }
  struct lsmt_ht ht;
  ssize_t n = 0;
  struct segment_mapping *mi = do_load_index((void *)(&fd), &ht, false, &n);
  free(mi);
  mi = do_load_index((void *)(&fd), &ht, true, &n);
  // for (const struct segment_mapping *p = mi; p!=mi+n; p++ ){
  //         print_segment_mapping(p);
  // }
  free(mi);
  fd = open(data, O_RDONLY);
  if (fd == -1) {
    PRINT_ERROR("errno: %d msg: %s", errno, strerror(errno));
    return;
  }

  mi = do_load_index((void *)(&fd), &ht, false, &n);
  free(mi);
}

TEST(LSMT_RO, err_open_file) {
  const char *layer = "/tmp/img_data.0.lsmt";
  int fd = open(layer, O_RDONLY);
  if (fd == -1) {
    PRINT_ERROR("errno: %d msg: %s", errno, strerror(errno));
    return;
  }
  struct lsmt_ro_file *ro = open_file((void *)(&fd), true);
  close_file(&ro);
  fd = 0;
  ro = open_file((void *)(&fd), true);
  close_file(&ro);
}

// TEST(LSMT_RO, open_files_exceed)
//{
//        int files [ IMAGE_RO_LAYERS + 1 ];
//        open_files((void **)(&files), IMAGE_RO_LAYERS + 1, true);
//}
//
TEST(LSMT_RO, open_files) {
  std::vector<std::string> layers(IMAGE_RO_LAYERS);
  for (int i = 0; i < IMAGE_RO_LAYERS; i++) {
    layers[i] = "/tmp/img_layer." + std::to_string(i) + ".lsmt";
  }
  const char *disk = "/tmp/img.disk";
  uint64_t files[IMAGE_RO_LAYERS];
  int cnt = 0;
  for (int i = 0; i < IMAGE_RO_LAYERS; i++) {
    int fd = open(layers[i].c_str(), O_RDONLY);
    if (fd == -1) {
      PRINT_INFO("open file failed%d\n", i);
      break;
    }
    files[i] = fd;
    cnt++;
  }
  PRINT_INFO("open image (layers: %d)", cnt);
  struct lsmt_ro_file *single = open_file((void *)(&files[0]), false);
  close_file(&single);
  struct lsmt_ro_file *ro = open_files((void **)(&files), cnt, true);
  PRINT_INFO("create lsmt_ro_file object. addr: 0x%lx",
             (unsigned long)(void *)ro);

  if (ro == NULL) {
    for (int i = 0; i < cnt; i++)
      if (files[i])
        close(files[i]);
    PRINT_INFO("create lsmt_ro_file object failed, func return.%c", 0);
    return;
  }

  set_max_io_size(ro, 0);     // invalid check
  set_max_io_size(ro, 10007); // invalid check
  set_max_io_size(ro, 512 * 1024);
  get_max_io_size(ro);
  PRINT_INFO("file->MAX_IO_SIZE: %lu", ro->MAX_IO_SIZE);
  int fimg = open(disk, O_RDONLY);
  struct stat st;
  fstat(fimg, &st);
  char *data = (char *)calloc(st.st_size, sizeof(char));
  size_t readn = pread(fimg, data, st.st_size, 0);
  if (readn < st.st_size)
    return;
  char buf[1024 * 1024] = {};
  int times = RAND_READN;
  PRINT_INFO("do randread (times %d)", times);
  for (int i = 0; i < 3; i++) {
    struct segment s = {RAND_RANGE};
    lsmt_pread(ro, buf, s.length, s.offset);
  }
  for (int i = 0; i < times - 3; i++) {
    struct segment s = {RAND_RANGE};
    lsmt_pread(ro, buf, s.length / ALIGNMENT * ALIGNMENT,
               s.offset / ALIGNMENT * ALIGNMENT);
  }

  PRINT_INFO("start verify lsmt_ro_file. %lu", ro->m_vsize);

  struct timeval t0, t1;
  gettimeofday(&t0, NULL);
  for (off_t o = 0; o < (off_t)ro->m_vsize;
       o += sizeof(buf)) { // buf[1<<20], 一次读1MB
    ssize_t ret = lsmt_pread(ro, buf, sizeof(buf), o);
    EXPECT_EQ(ret, (ssize_t)sizeof(buf));
    for (size_t i = 0; i < sizeof(buf) / ALIGNMENT; ++i) {
      char *p = buf + i * ALIGNMENT;
      for (size_t j = 0; j < ALIGNMENT; ++j)
        EXPECT_EQ(p[0], p[j]);
      if (p[0] != data[o / ALIGNMENT + i]) {
        PRINT_INFO("file offset: %lu (%lu)\n", o + i * ALIGNMENT,
                   o / ALIGNMENT + i);
        EXPECT_EQ(p[0], data[o / ALIGNMENT + i]);
        char *p = buf + i * ALIGNMENT;
        memset(p, 0, ALIGNMENT);
        lsmt_pread(ro, p, ALIGNMENT, o + i * ALIGNMENT);
        EXPECT_EQ(p[0], data[o / ALIGNMENT + i]);
        close_file(&ro);
        return;
      }
    }
  }
  gettimeofday(&t1, NULL);
  int c_time_elapse =
      (t1.tv_sec - t0.tv_sec) * 1000 + (t1.tv_usec - t0.tv_usec) / 1000;
  PRINT_INFO("lsmt_pread time cost: %d", c_time_elapse);

  close_file(&ro);
}

// TEST(PROG, malloc)
// {
//         int *arr = (int *)malloc(100);

// }

int main(int argc, char **argv) {

  hook();
  int seed = 101037;
  srand(seed);
  ::testing::InitGoogleTest(&argc, argv);
  int ret = RUN_ALL_TESTS();
  PRINT_INFO("ALL DONE.%c", 0);
  return 0;
}
