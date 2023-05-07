/*
 * Malloc version 1, an explicit allocator.
 * The whole allocator is aligned by 8 Bytes.
 * For each allocated block, it starts with a 4 Bytes header, which contains messages of the block's size, and the alloc
 situation of the block and the block before. The following is the main data of the block. And after that is the optimal
 padding.
 * As for a free block, more than the header, it also has a footer at the end, which contains messages of the block's
 size, and the alloc situation of the block itself. What's more, it also contains a two-way linked list in the middle,
 pointing to the free blocks before it and after it.
 * The allocator will use the first-fit strategy and add the freed block to the tail of the linked list.
 * by Eternal-Fir at 4.26
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

// basic constants and variable types
#define ALIGNMENT 8
#define DWORD_SIZE 8
#define WORD_SIZE 4
#define LIMITSIZE 0xffffffff
#define HEAD 0
#define TAIL 4
#define FIT_NUMBER 1
#define MIN_BLOCK_SIZE (3*WORD_SIZE)
typedef unsigned long long uint64_t, dword_t;
typedef unsigned int uint32_t, word_t;
typedef signed int offset_t;
#define TRUE (word_t)(1)
#define FALSE (word_t)(0)
#define WHOLE_SIZE (word_t)(mem_heapsize())

// tool funcs
#define MAX(x, y) ((x)>(y) ? (x) : (y))
#define MIN(x, y) ((x)<(y) ? (x) : (y))

// align
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

// get and set value to void*
#define GET(p) (*(word_t *)((offset_t)(p)+(mem_heap_lo())))
#define DGET(p) (*(dword_t *)((offset_t)(p)+(mem_heap_lo())))
#define SET(p, val) (*(word_t *)((offset_t)(p)+(mem_heap_lo()))=((word_t)val))
#define DSET(p, val) (*(dword_t *)((offset_t)(p)+(mem_heap_lo()))=((dword_t)val))
#define PHY_VIR_TRANSLATE(phy) (word_t)(phy-mem_heap_lo())
#define VIR_PHY_TRANSLATE(vir) (void*)(vir+mem_heap_lo())
#define ZERO(p) SET(p,0)
#define DZERO(p) DSET(p,0)
#define MEMCPY(old, new) SET(new,GET(old))
#define DMEMCPY(old, new) DSET(new,DGET(old))

// get and set total size and head and tail of the two-way linked list.
#define GET_TOTAL_SIZE (mem_heapsize())
#define GET_HEAD (GET(0))
#define SET_HEAD(value) (SET(0,value))
#define GET_TAIL (GET(WORD_SIZE))
#define SET_TAIL(value) (SET(WORD_SIZE,value))

// header and footer message get and set
#define HEADER_PACK(size, alloc_before, alloc_now) (((size)|(alloc_before<<1))|(alloc_now))
#define FOOTER_PACK(size, alloc) ((size)|(alloc))
#define GET_SIZE(value) (value & ~0x3)
#define GET_ALLOC_FRONT(value) ((value & 0x3)>>1)
#define GET_ALLOC_NOW(value) (value & 0x1)
#define GET_HEADER(bp) GET((bp)-WORD_SIZE)
#define GET_FOOTER(bp) GET((bp)+GET_SIZE(GET_HEADER(bp)))
#define SET_HEADER(bp, size, alloc_before, alloc_now) (SET(((bp)-WORD_SIZE),HEADER_PACK(size, alloc_before, alloc_now)))
#define SET_FOOTER(bp, size, alloc) (SET(((bp)+size),FOOTER_PACK(size, alloc)))
#define GET_PREV(bp) (GET(bp))
#define GET_NEXT(bp) (GET(bp+WORD_SIZE))
#define SET_PREV(bp, offset) (SET(bp,offset))
#define SET_NEXT(bp, offset) (SET(bp+WORD_SIZE,offset))

// (bp) be the start of the main part of the blk, then return the (bp) of prev/next block in physics.
#define BLK_BEHIND_FREE(bp) ((bp)+GET_SIZE(GET_HEADER(bp))+DWORD_SIZE)
#define BLK_BEHIND_BUSY(bp) ((bp)+GET_SIZE(GET_HEADER(bp))+WORD_SIZE)
#define BLK_FRONT_FREE(bp) ((bp)-GET_SIZE(GET(bp-DWORD_SIZE))-DWORD_SIZE) // only if the block front is free

// get the required size of the malloc op in
#define REQUIRED_SIZE(size) (MAX(ALIGN(size-WORD_SIZE)+WORD_SIZE,MIN_BLOCK_SIZE))

// using to set massages of busy block
void SET_BUSY_BLOCK(offset_t bp, word_t size, word_t alloc_before) {
//    SET(bp, size);
    SET_HEADER(bp, size, alloc_before, TRUE);
//    SET_FOOTER(bp, size, TRUE);
}

// using to set massages of free block
void SET_FREE_BLOCK(offset_t bp, word_t size, word_t alloc_front, offset_t prev, offset_t next) {
//    SET(bp, size);
    SET_HEADER(bp, size, alloc_front, FALSE);
    SET_FOOTER(bp, size, FALSE);
    SET_PREV(bp, prev);
    SET_NEXT(bp, next);
}

// using to change the allocated situation of the block in front of it, return sit of front before
word_t CHANGE_ALLOCATED_FRONT(offset_t bp, word_t alloca_front_new) {
    word_t header = GET_HEADER(bp);
    word_t size = GET_SIZE(header);
    word_t alloc_front_before = GET_ALLOC_FRONT(header);
    word_t alloc_now = GET_ALLOC_NOW(header);
    SET_HEADER(bp, size, alloca_front_new, alloc_now);
    return alloc_front_before;
}

// the max apace in available in the linked list now.
word_t max_available_space_now;

const int print_dbg_info = 0;
int dbg_op_cnt;


/*
 * mm_init - Set basic space, set the head and tail of the two-way linked list
 * Set the first block(free)
 */
int mm_init(void) {
//    dbg_printf("init_start\n");

    int total_size = 32;
    mem_sbrk(total_size);
    SET_FREE_BLOCK(16, 8, TRUE, HEAD, TAIL);
    SET_HEAD(16);
    SET_TAIL(16);

    max_available_space_now = 8;
    // set last virtual block
    SET_HEADER(32, 0, FALSE, TRUE);

    dbg_op_cnt = 0;
//    dbg_printf("init_end\n");
    return 0;
}

/*
 * malloc - Allocate a block.
 * We firstly search it through the linked list with the best first k fit algorithm.
 * If there isn't a block satisfies the space requirement, we would use mem_sbrk() to ask for enough space
 */
void *malloc(size_t size) {
    if (print_dbg_info) {
        dbg_op_cnt++;
        dbg_printf("malloc %d start: size=%d\n", dbg_op_cnt, size);
    }


    word_t size_required = REQUIRED_SIZE(size);
    if (WHOLE_SIZE + size_required > LIMITSIZE)
        return VIR_PHY_TRANSLATE(0);
    offset_t object_block = GET_HEAD;
    offset_t min_block = 0;
    word_t min_size = 0xffffffff;
    word_t size_now = 0;
    word_t fit_cnt = 0;
    if(size_required>max_available_space_now+4){
        object_block=TAIL;
    }else{
        while (object_block != TAIL && fit_cnt < FIT_NUMBER) {
            word_t header = GET_HEADER(object_block);
            size_now = GET_SIZE(header)+WORD_SIZE; // can put a WORD size into the footer
            fit_cnt++;
            if (size_now < size_required) {
                fit_cnt--;
            } else { // first k fit
//                fit_cnt++;
                if (size_now < min_size) {
                    min_size = size_now;
                    min_block = object_block;
                }
            }
            object_block = GET_NEXT(object_block);
        }
        if (fit_cnt != 0) {
            object_block = min_block;
            size_now = min_size;
        }
    }
    if (object_block == TAIL) { // space run out
        object_block = PHY_VIR_TRANSLATE(mem_sbrk(size_required + WORD_SIZE));
        word_t alloc_front = GET_ALLOC_FRONT(GET(object_block - WORD_SIZE));
        MEMCPY(object_block - WORD_SIZE, object_block - WORD_SIZE + size_required + WORD_SIZE);
        CHANGE_ALLOCATED_FRONT(object_block + size_required + WORD_SIZE, TRUE);
        SET_BUSY_BLOCK(object_block, size_required, alloc_front);
    } else {
        if (size_now - size_required < 16) { // allocated directly
            size_required = size_now;
            offset_t prev_block, next_block;
            prev_block = GET_PREV(object_block);
            next_block = GET_NEXT(object_block);
            if (prev_block != HEAD) {
                SET_NEXT(prev_block, next_block);
            } else {
                SET_HEAD(next_block);
            }
            if (next_block != TAIL) {
                SET_PREV(next_block, prev_block);
            } else {
                SET_TAIL(prev_block);
            }
            word_t alloc_front = GET_ALLOC_FRONT(GET_HEADER(object_block));
            SET_BUSY_BLOCK(object_block, size_required, alloc_front);
            // need to modify the situation of next block's pre alloc sit.
            offset_t block_behind = BLK_BEHIND_BUSY(object_block);
            word_t record_before = CHANGE_ALLOCATED_FRONT(block_behind, TRUE);
            if (record_before != FALSE)
                dbg_printf("alloc situation error at %d while alloc %d\n", block_behind, object_block);
        } else { // need to divide
            word_t size_remain = size_now - size_required - DWORD_SIZE;
            offset_t new_block = object_block + size_required + WORD_SIZE;
            offset_t prev_block = GET_PREV(object_block), next_block = GET_NEXT(object_block);
            word_t object_header_before = GET_HEADER(object_block);
            SET_BUSY_BLOCK(object_block, size_required, GET_ALLOC_FRONT(object_header_before));
            if (prev_block != HEAD) {
                SET_NEXT(prev_block, new_block);
            } else {
                SET_HEAD(new_block);
            }
            if (next_block != TAIL) {
                SET_PREV(next_block, new_block);
            } else {
                SET_TAIL(new_block);
            }
            SET_FREE_BLOCK(new_block, size_remain, TRUE, prev_block, next_block);
            offset_t block_behind = new_block + size_remain + DWORD_SIZE; // don't need?
            word_t record_before = CHANGE_ALLOCATED_FRONT(block_behind, FALSE);
            if (record_before != FALSE)
                dbg_printf("alloc situation error at %d while alloc %d\n", block_behind, object_block);
        }
    }

    if (print_dbg_info)
        dbg_printf("malloc %d end\n", dbg_op_cnt);
    return VIR_PHY_TRANSLATE(object_block);
}

/*
 * free - Free an allocated block
 * We Add the new freed block to the head of the linked list.
 * By checking the block's header, we decided if the block need to be merged to the block in front of it. TODO: If we need to care about the block behind it ?
 */
void free(void *ptr) {
    if (print_dbg_info) {
        dbg_op_cnt++;
        dbg_printf("free %d start\n", dbg_op_cnt);
    }


    offset_t object_block = PHY_VIR_TRANSLATE(ptr);
    if (object_block < 16 || object_block > WHOLE_SIZE) {
//        printf("free a block out of range: %d", object_block);
        return;
    }
    word_t old_header = GET_HEADER(object_block);
    word_t size_free = GET_SIZE(old_header) + WORD_SIZE;
    if (GET_ALLOC_NOW(old_header) == FALSE) {
        printf("alloc sit error at %d\n", object_block);
        return;
    }
    word_t alloc_sit_front = GET_ALLOC_FRONT(GET_HEADER(object_block));
    offset_t behind_block = BLK_BEHIND_BUSY(object_block);
    word_t behind_header = GET_HEADER(behind_block);
    word_t alloc_sit_behind = GET_ALLOC_NOW(behind_header);
    if (alloc_sit_behind == TRUE && alloc_sit_front == TRUE) {
        // simply add a block to the linked list
        // size now need to -8
        size_free -= DWORD_SIZE;
        offset_t second_head = GET_HEAD;
        if (second_head != TAIL) {
            SET_FREE_BLOCK(object_block, size_free, TRUE, HEAD, second_head);
            SET_PREV(second_head, object_block);
            SET_HEAD(object_block);
        } else {
            SET_FREE_BLOCK(object_block, size_free, TRUE, HEAD, TAIL);
            SET_HEAD(object_block);
            SET_TAIL(object_block);
        }
        CHANGE_ALLOCATED_FRONT(behind_block, FALSE);
        if (max_available_space_now < size_free)
            max_available_space_now = size_free;
    } else if (alloc_sit_front == TRUE && alloc_sit_behind == FALSE) {
        // need to merge with block behind
        word_t new_size = size_free + GET_SIZE(behind_header);
        offset_t prev_block = GET_PREV(behind_block), next_block = GET_NEXT(behind_block);
        if (prev_block == HEAD) {
            SET_HEAD(object_block);
        } else {
            SET_NEXT(prev_block, object_block);
        }
        if (next_block == TAIL) {
            SET_TAIL(object_block);
        } else {
            SET_PREV(next_block, object_block);
        }
        ZERO(behind_block - WORD_SIZE);
        SET_FREE_BLOCK(object_block, new_size, TRUE, prev_block, next_block);
        if (max_available_space_now < new_size)
            max_available_space_now = new_size;
    } else if (alloc_sit_front == FALSE && alloc_sit_behind == TRUE) {
        // need to merge with block front
        offset_t master_block = BLK_FRONT_FREE(object_block);
        word_t old_master_header = GET_HEADER(master_block);
        word_t new_size = GET_SIZE(old_master_header) + size_free;
        offset_t prev_block = GET_PREV(master_block), next_block = GET_NEXT(master_block);
        DZERO(master_block + GET_SIZE(old_master_header));
        SET_FREE_BLOCK(master_block, new_size, GET_ALLOC_FRONT(old_master_header), prev_block, next_block);
        CHANGE_ALLOCATED_FRONT(behind_block, FALSE);
        if (max_available_space_now < new_size)
            max_available_space_now = new_size;
    } else {
        // need to merge three blocks together, need to destroy behind block and reshape master block
        offset_t master_block = BLK_FRONT_FREE(object_block);
        word_t old_master_header = GET_HEADER(master_block);
        word_t new_size = GET_SIZE(old_master_header) + size_free + GET_SIZE(behind_header) + DWORD_SIZE;
        offset_t behind_prev = GET_PREV(behind_block), behind_next = GET_NEXT(behind_block);
        if (behind_prev == HEAD) {
            SET_HEAD(behind_next);
        } else {
            SET_NEXT(behind_prev, behind_next);
        }
        if (behind_next == TAIL) {
            SET_TAIL(behind_prev);
        } else {
            SET_PREV(behind_next, behind_prev);
        }
        DZERO(master_block + GET_SIZE(old_master_header));
        ZERO(object_block + GET_SIZE(old_header));
        offset_t master_prev = GET_PREV(master_block), master_next = GET_NEXT(master_block);
        SET_FREE_BLOCK(master_block, new_size, GET_ALLOC_FRONT(old_master_header), master_prev, master_next);
        if (max_available_space_now < new_size)
            max_available_space_now = new_size;
    }

    if (print_dbg_info)
        dbg_printf("free %d end\n", dbg_op_cnt);
    return;
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 * If the old ptr in be NULL, equals to malloc()
 * If the size in be 0, equals to free()
 * Otherwise, malloc a new block as size required, copying its data, and freeing the old block.
 */
void *realloc(void *oldptr, size_t size) {
    if (print_dbg_info) {
        dbg_op_cnt++;
        dbg_printf("realloc %d start: size=%d\n", dbg_op_cnt, size);
        dbg_op_cnt--;
    }


    if (oldptr == NULL)
        return malloc(size);
    if (size == 0) {
        free(oldptr);
        return NULL;
    }
    void *new_ptr = malloc(size);
    offset_t old_block = PHY_VIR_TRANSLATE(oldptr), new_block = PHY_VIR_TRANSLATE(new_ptr);
    word_t old_header = GET_HEADER(old_block), new_header = GET_HEADER(new_block);
    word_t old_size = GET_SIZE(old_header), new_size = GET_SIZE(new_header);
    word_t copy_size = MIN(old_size, new_size);
    for (word_t i = 0; i < copy_size; i += 4) { // remember: only copy the main data area
        MEMCPY(old_block + i, new_block + i);
    }

    dbg_op_cnt--;

    free(oldptr);

    if (print_dbg_info)
        dbg_printf("realloc %d end completely.\n", dbg_op_cnt);
    return new_ptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc(size_t nmemb, size_t size) {
    if (print_dbg_info) {
        dbg_op_cnt++;
        dbg_printf("calloc %d start: size=%d\n", dbg_op_cnt, size);
    }

    void *new_ptr = malloc(nmemb * size);
    offset_t new_block = PHY_VIR_TRANSLATE(new_ptr);
    word_t new_size = GET_SIZE(GET_HEADER(new_block));
    for (word_t i = 0; i < new_size; i += 4) {
        ZERO(new_block + i);
    }

    if (print_dbg_info)
        dbg_printf("calloc %d end\n", dbg_op_cnt);
    return new_ptr;
}

/*
 * mm_checkheap - There are no bugs in my code, so I don't need to check,
 *      so nah!
 */
void mm_checkheap(int verbose) {
    /*Get gcc to be quiet. */
    verbose = verbose;
    offset_t blk_now = GET_HEAD;
    while (blk_now != TAIL) {

        if (blk_now < 0 || blk_now > WHOLE_SIZE)
            dbg_printf("linked list error at %d\n", blk_now);
        word_t header = GET_HEADER(blk_now);
        if (GET_ALLOC_NOW(header) != FALSE)
            dbg_printf("alloc situation error at %d\n", blk_now);
        if (GET_SIZE(header) <= 0)
            dbg_printf("free block size error at %d\n", blk_now);
        blk_now = GET_NEXT(blk_now);
    }
    blk_now = GET_TAIL;
    while (blk_now != HEAD) {
        if (blk_now < 0 || blk_now > WHOLE_SIZE)
            dbg_printf("linked list error at %d\n", blk_now);
        word_t footer = GET_FOOTER(blk_now);
        if (GET_ALLOC_NOW(footer) != FALSE)
            dbg_printf("alloc situation error at %d\n", blk_now);
        blk_now = GET_PREV(blk_now);
    }
    if (verbose == 0) {
        word_t total_size = WHOLE_SIZE;
        offset_t now = 0;
        while (now < total_size) {
            for (int i = 0; i < 4; ++i) {
                word_t our = GET(now);
                dbg_printf("%d ", now);
                now++;
            }
            dbg_printf("\n");
        }
    }
}
