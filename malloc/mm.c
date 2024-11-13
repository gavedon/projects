/* Krzysztof Chmiel 316749
Oświadczam, że jestem jedynym twórcą poniższego kodu.
(wyjątkami są procedury i pomysły wzięte z pliku mm-implicit oraz z 9.9 rodziału
ksiązki CSAPP )

Opis:
0. Idea rozwiązania to segregated fits z użyciem first fita jako metody
wstawiania
1. Tak wygląda stuktura sterty:

-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
|  padding (12 bajtów, żeby wyrównać do payloadu(16B)) |  segregated_list
(preheap, czyli pierwsze bloki z każdej klasy)  |  bloki wolne i zajęte   |
4-bajtowy epilogue z CSAPPA |
-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

2. Wygląd bloków:

Zajęte:         Wolne:
------------    ------------
|  Header  |    |  Header  |
|----------|    |----------|
|          |    |   Prev   |
| Payload  |    |----------|
|(+padding)|    |   Next   |
|          |    |----------|
|          |    |(+padding)|
|          |    |----------|
|          |    |  Footer  |
------------    ------------

3. Co do samych klas, to wyszło mi, że 14 jest najopytmalniejszą liczbą, każda
następna jest dwukrotnie więszka od poprzedniej, a najmniejsza zaczyna się od
16, bo tylko może mieć najmniej blok (zgodnie ze stałą ALIGNMENT) 4.
*/
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

#define DEBUG
#ifdef DEBUG
#define debug(...) printf(__VA_ARGS__)
#else
#define debug(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

// Everything below is taken stright out of the mm-implicit

typedef int32_t word_t; /* Heap is bascially an array of 4-byte words. */

typedef enum {
  FREE = 0,     /* Block is free */
  USED = 1,     /* Block is used */
  PREVFREE = 2, /* Previous block is free (optimized boundary tags) */
} bt_flags;

static word_t *heap_start; /* Address of the first block */
static word_t *heap_end;   /* Address past last byte of last block */
static word_t *last;       /* Points at last block */

/* --=[ boundary tag handling ]=-------------------------------------------- */

static inline size_t bt_size(word_t *bt) {
  return *bt & ~(USED | PREVFREE);
}

static inline int bt_used(word_t *bt) {
  return *bt & USED;
}

static inline int bt_free(word_t *bt) {
  return !(*bt & USED);
}

/* Given boundary tag address calculate it's buddy address. */
static inline word_t *bt_footer(word_t *bt) {
  return (void *)bt + bt_size(bt) - sizeof(word_t);
}

/* Given payload pointer returns an address of boundary tag. */
static inline word_t *bt_fromptr(void *ptr) {
  return (word_t *)ptr - 1;
}

/* Creates boundary tag(s) for given block. */
static inline void bt_make(word_t *bt, size_t size, bt_flags flags) {
  size_t bt_mask = size | flags;
  *bt = bt_mask;
  if (bt_free(bt)) { // footer is needed only in free blocks
    *bt_footer(bt) = bt_mask;
  }
}

/* Previous block free flag handling for optimized boundary tags. */
static inline bt_flags bt_get_prevfree(word_t *bt) {
  return *bt & PREVFREE;
}

static inline void bt_clr_prevfree(word_t *bt) {
  if (bt)
    *bt &= ~PREVFREE;
}

static inline void bt_set_prevfree(word_t *bt) {
  *bt |= PREVFREE;
}

/* Returns address of next block or NULL. */
static inline word_t *bt_next(word_t *bt) {
  if (bt != last) {
    return (void *)bt + bt_size(bt);
  }
  return NULL;
}

/* Returns address of previous block or NULL. */
static inline word_t *bt_prev(word_t *bt) {
  if (bt != heap_start) {
    return (void *)bt - bt_size(bt - 1);
  }
  return NULL;
}

/* Calculates block size incl. header, footer & payload,
 * and aligns it to block boundary (ALIGNMENT). */
static inline size_t blksz(size_t size) {
  return (size + sizeof(word_t) + ALIGNMENT - 1) & -ALIGNMENT; // CSAPP
}

static void *morecore(size_t size) {
  void *ptr = mem_sbrk(size);
  if (ptr == (void *)-1)
    return NULL;
  return ptr;
}

// Here ends the mm-implicit part

static word_t *segregated_list; // pointer to the beggining of the classes array

#define ALL_CLASSES 14 // number of lists in the segregated free list
static inline int find_class(size_t size) {
  size_t class = 0;
  size_t class_size_iter =
    16; // equal to the value of the smallest possible block
  while (class < ALL_CLASSES - 1) {
    if (size <= class_size_iter) {
      break;
    }
    class ++;
    class_size_iter *= 2;
  }
  return class;
}

// getters and setters to operate on the segregated list

static void *heap; // Points to the beggining of the heap

static inline word_t *get_prev_fblk(word_t *bt) {
  word_t offset = *(bt + 1);
  return offset ? heap + offset : NULL;
}

static inline void set_prev_fblk(word_t *bt, word_t *prev) {
  if (bt == NULL) {
    return;
  }
  *(bt + 1) = prev ? (void *)prev - heap : 0;
}

// The same thing but with the next
static inline word_t *get_next_fblk(word_t *bt) {
  word_t offset = *(bt + 2);
  return offset ? heap + offset : NULL;
}

static inline void set_next_fblk(word_t *bt, word_t *next) {
  if (bt == NULL) {
    return;
  }
  *(bt + 2) = next ? (void *)next - heap : 0;
}

// The policy I use is first fit, which means I put the new block at the
// beginning (actually as a second block, because the first one is always the
// sheriff)
static inline void insert(word_t *bt) {
  size_t where_to_put = find_class(bt_size(bt));
  word_t *first_elem =
    (word_t *)segregated_list + where_to_put * sizeof(word_t);
  word_t *next = get_next_fblk(first_elem);
  set_prev_fblk(bt, first_elem);
  set_next_fblk(bt, next);
  set_next_fblk(first_elem, bt);
  set_prev_fblk(next, bt);
}
// it's really simple, all we do is changing the ptrs of the next and prev
// blocks of the given block, so that they are now poining to each other
// avoiding current block
static inline void removee(word_t *bt) {
  word_t *prev_of_the_one_to_be_removed = get_prev_fblk(bt);
  word_t *next_of_the_one_to_be_removed = get_next_fblk(bt);
  set_next_fblk(prev_of_the_one_to_be_removed, next_of_the_one_to_be_removed);
  set_prev_fblk(next_of_the_one_to_be_removed, prev_of_the_one_to_be_removed);
}
// This is simply taken stright out of the CSAPP and translated, so it fits our
// semantics. All we do is check whether the previous block, next block or both
// are free, if so, then we merge them and creat one block of a summarized size
static inline word_t *coalesce(word_t *bt) {

  size_t size = bt_size(bt);
  int prev_unused = bt_get_prevfree(bt);
  int next_used = bt_used(bt_next(bt));
  word_t *next = bt_next(bt);
  word_t *prev = bt_prev(bt);

  if (!prev_unused && next_used) {
    insert(bt);
    return bt;
  } else if (!prev_unused && !next_used) {
    size += bt_size(next);
    removee(next);
    bt_make(bt, size, FREE);
    bt_set_prevfree(bt_next(bt));

  } else if (prev_unused && next_used) {
    size += bt_size(prev);
    bt = prev;
    removee(prev);
    bt_make(bt, size, FREE | bt_get_prevfree(prev));
    bt_set_prevfree(bt_next(bt));

  } else {
    size += bt_size(next) + bt_size(prev);
    bt = prev;
    removee(next);
    removee(prev);
    bt_make(bt, size, FREE | bt_get_prevfree(prev));
    bt_set_prevfree(bt_next(bt));
  }
  insert(bt);
  return bt;
}

// Here we look for the possible place to put the block of given size,
// find_class helps to find the right class, but there is a chance there will be
// no free space there. So we look for the actual place to put the block
static word_t *find_fit(size_t size) {
  for (size_t class = find_class(size); class < ALL_CLASSES; class ++) {
    word_t *first_elem = (word_t *)segregated_list + class * sizeof(word_t);
    word_t *next = get_next_fblk(first_elem);
    while (first_elem != next) {
      first_elem = get_next_fblk(first_elem);
      if (bt_size(first_elem) >= size) {
        return first_elem;
      }
    }
  }
  return NULL;
}

// Here is the initialization process of the whole program. We creat all the
// classes in the list, then initialize the main part of the heap,
// also taking care of the padding, so that the adresses are aligned exactly as
// we want them to. Bear in mind, that the sheriffs initialized
// in each class of the segregated fits list are size 0, so they cannot be
// re/alloced accidently
int mm_init(void) {
  size_t padding = (ALIGNMENT - sizeof(word_t)) / sizeof(word_t);
  void *new = morecore(ALL_CLASSES * 16 + 64);
  if (!new)
    return -1;
  heap = new;
  segregated_list = heap_end = heap_start = last = NULL;
  word_t *preheap = (word_t *)new + ALL_CLASSES * sizeof(word_t) + padding;
  heap_start = heap_end = last = preheap;
  segregated_list = (word_t *)new + padding;
  for (size_t class = 0; class < ALL_CLASSES; class ++) {
    word_t *first_sheriff = (word_t *)segregated_list + class * sizeof(word_t);
    bt_make(first_sheriff, 0, USED);
    word_t *last_sheriff =
      (word_t *)segregated_list + class * sizeof(word_t) + 1;
    bt_make(last_sheriff, 0, USED);
    set_prev_fblk(first_sheriff, last_sheriff);
    set_next_fblk(first_sheriff, last_sheriff);
    set_prev_fblk(last_sheriff, first_sheriff);
    set_next_fblk(last_sheriff, first_sheriff);
  }
  return 0;
}

static inline size_t split(word_t *bt, size_t size) {
  size_t old_size = bt_size(bt);
  removee(bt);
  if (bt_size(bt) - size >= ALIGNMENT) {
    bt_make(bt, size, USED | bt_get_prevfree(bt));
    word_t *next = bt_next(bt);
    bt_make(next, old_size - size, FREE);
    bt_set_prevfree(bt_next(next));
    insert(next);
    return 1;
  }
  return 0;
}
// the malloc actaully is nothing special, just meet all the pointed out
// specification characteristics we try to split the block, to avoid the
// internal fragmentation, that's why we use the suggested in the CSAPP 9.9
// chapter split function if there is no free space, we use sbrk to get some
// more
void *malloc(size_t size) {
  if (size == 0) {
    return NULL;
  }
  size_t size_blk = blksz(size);
  word_t *bt = find_fit(size_blk);

  if (bt == NULL) {
    bt = last;
    void *new = morecore(size_blk);
    if (new == NULL) {
      return NULL;
    }
    bt_make(bt, size_blk, USED | bt_get_prevfree(bt));
    last = (void *)bt + bt_size(bt);
    bt_make(last, 4, USED);
    heap_end = (void *)last + bt_size(last);
  } else {
    if (!split(bt, size_blk)) {
      bt_make(bt, bt_size(bt), USED | bt_get_prevfree(bt));
      bt_clr_prevfree(bt_next(bt));
    }
  }
  return bt + 1;
}
// free just frees the allocated memory and coalesce eagerly, which means as
// soon as the block is freed, we check whether the neighbours are free to, if
// so we merge them
void free(void *ptr) {
  if (ptr != NULL) {
    word_t *bt = (word_t *)ptr - 1;
    size_t size = bt_size(bt);
    bt_make(bt, size, FREE | bt_get_prevfree(bt));
    bt_set_prevfree(bt_next(bt));
    coalesce(bt);
  }
}

static inline word_t *split_notfree(word_t *bt, size_t size, size_t old_size) {
  word_t *old = bt;
  bt_make(bt, size, USED | bt_get_prevfree(bt));
  word_t *next = bt_next(bt);
  bt_make(next, old_size - size, FREE);
  insert(next);
  bt_set_prevfree(bt_next(next));
  return old;
}
// the realloc works the same as malloc, which means it has been done using the
// given in the project description specification.
// It uses a very similiar split procedure as malloc, but since there are some
// differneces, a separate split_notfree function has been created
void *realloc(void *old_ptr, size_t size) {
  if (!old_ptr) {
    return malloc(size);
  }
  if (size == 0) {
    free(old_ptr);
    return NULL;
  }
  word_t *old_bt = bt_fromptr(old_ptr);
  size_t old_size = bt_size(old_bt);
  void *new_ptr = old_ptr;
  size_t new_size = blksz(size);

  int diff = old_size - new_size;
  if (ALIGNMENT > diff && diff >= 0) {
    return old_ptr;
  } else if (diff >= ALIGNMENT) {
    split_notfree(old_bt, new_size, old_size);
    return old_ptr;
  } else if (diff < 0) {
    size_t size_neighbour = old_size;
    word_t *next = bt_next(old_bt);
    if (bt_free(next)) {
      size_neighbour += bt_size(next);
      if (size_neighbour >= new_size) {
        removee(next);
        bt_make(old_bt, size_neighbour, USED | bt_get_prevfree(old_bt));
        bt_clr_prevfree(bt_next(old_bt));
        old_size = bt_size(old_bt);
        if ((old_size - new_size) >= ALIGNMENT) {
          split_notfree(old_bt, new_size, old_size);
        }
        return old_bt + 1;
      }
    }
  }
  new_ptr = malloc(size);
  if (new_ptr == NULL) {
    return NULL;
  }
  size_t old_sizee = bt_size(old_bt) - sizeof(word_t);
  if (size < old_sizee) {
    old_sizee = size;
  }
  memcpy(new_ptr, old_ptr, old_sizee);
  free(old_ptr);
  return new_ptr;
}

// Here I have changed nothing compared to mm-implicit
void *calloc(size_t nmemb, size_t size) {
  size_t bytes = nmemb * size;
  void *new_ptr = malloc(bytes);

  /* If malloc() fails, skip zeroing out the memory. */
  if (new_ptr)
    memset(new_ptr, 0, bytes);

  return new_ptr;
}

void mm_checkheap(int verbose) {
  // word_t *block = heap_start;
  // while (block != NULL) {
  //   printf("----------------------\n");
  //   printf("ADDRESS: %p\n", block);
  //   printf("PREV FREE?: %d\n", bt_get_prevfree(block));
  //   printf("FREE?: %d\n", bt_free(block));
  //   printf("SIZE: %lu\n", bt_size(block));
  //   printf("----------------------\n");
  //   block = bt_next(block);
}
