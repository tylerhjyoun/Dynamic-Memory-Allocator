/*
 * mm.c -  Simple allocator based on Segregated Explicit free lists,
 *         first fit placement, and boundary tag coalescing.
 *
 * Each block has header and footer of the form:
 *
 *      63       32   31        1   0
 *      --------------------------------
 *     |   unused   | block_size | a/f |
 *      --------------------------------
 *
 * a/f is 1 iff the block is allocated. The list has the following form:
 *
 * begin                                       end
 * heap                                       heap
 *  ----------------------------------------------
 * | hdr(8:a) | zero or more usr blks | hdr(0:a) |
 *  ----------------------------------------------
 * | prologue |                       | epilogue |
 * | block    |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 *
 *
 * CITATIONS
 * LOG2X Implementation Idea from https://stackoverflow.com/questions/11376288/fast-computing-of-log2-for-64-bit-integers
 */
#include "memlib.h"
#include "mm.h"
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Your info */
team_t team = {
    /* First and last name */
    "Tyler Youn",
    /* UID */
    "405141291",
    /* Custom message (16 chars) */
    "reeeeee",
};

typedef struct {
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
} header_t;

typedef header_t footer_t;

typedef struct block_t{
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
    union {
        struct {
            struct block_t* next;
            struct block_t* prev;
        };
        int payload[0]; 
    } body;
} block_t;

/* This enum can be used to set the allocated bit in the block */
enum block_state { FREE,
                   ALLOC };

#define CHUNKSIZE (1 << 16) /* initial heap size (bytes) */
#define OVERHEAD (sizeof(header_t) + sizeof(footer_t)) /* overhead of the header and footer of an allocated block */
#define MIN_BLOCK_SIZE (32) /* the minimum block size needed to keep in a freelist (header + footer + next pointer + prev pointer) */
#define NUM_OF_BUCKETS (16)
#define LOG2(X) ((unsigned) (8*sizeof(unsigned) - __builtin_clz(X) - 1)) /* cited above */

/* Global variables */
static block_t *prologue; /* pointer to first block */
static block_t** seglistp;

/* function prototypes for internal helper routines */
static block_t *extend_heap(size_t words);
static block_t *place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);
static footer_t *get_footer(block_t *block);
static void printblock(block_t *block);
static void checkblock(block_t *block);
static int find_index(size_t size);
static void insertblock(block_t *block);
static void removeblock(block_t *block);
/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void) {
    /* create and initialize array of free lists */
    seglistp = mem_sbrk(sizeof(block_t*)*NUM_OF_BUCKETS); // n is number of buckets
    
    for(int i = 0; i < NUM_OF_BUCKETS; i++){
        seglistp[i] = NULL;
    }
    /* create the initial empty heap */
    if ((prologue = mem_sbrk(CHUNKSIZE)) == (void*)-1)
        return -1;
    /* initialize the prologue */
    prologue->allocated = ALLOC;
    prologue->block_size = sizeof(header_t);
    /* initialize the first free block */
    block_t *init_block = (void *)prologue + sizeof(header_t);
    init_block->allocated = FREE;
    init_block->block_size = CHUNKSIZE - OVERHEAD;
    footer_t *init_footer = get_footer(init_block);
    init_footer->allocated = FREE;
    init_footer->block_size = init_block->block_size;
    insertblock(init_block);
    /* initialize the epilogue - block size 0 will be used as a terminating condition */
    block_t *epilogue = (void *)init_block + init_block->block_size;
    epilogue->allocated = ALLOC;
    epilogue->block_size = 0;
    return 0;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) {
    uint32_t asize;       /* adjusted block size */
    uint32_t extendsize;  /* amount to extend heap if no fit */
    uint32_t extendwords; /* number of words to extend heap if no fit */
    block_t *block;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    size += OVERHEAD;

    asize = ((size + 7) >> 3) << 3; /* align to multiple of 8 */
    
    if (asize < MIN_BLOCK_SIZE) {
        asize = MIN_BLOCK_SIZE;
    }

    /* Search the free list for a fit */
    if ((block = find_fit(asize)) != NULL) {
        return place(block, asize)->body.payload;
    }
    /* No fit found. Get more memory and place the block */
    extendsize = (asize > CHUNKSIZE) // extend by the larger of the two
                     ? asize
                     : CHUNKSIZE;
    extendwords = extendsize >> 3; // extendsize/8
    if ((block = extend_heap(extendwords)) != NULL) {
        return place(block, asize)->body.payload;
    }
    /* no more memory :( */
    return NULL;
}
/* $end mmmalloc */

/*
 * mm_free - Free a block
 */
/* $begin mmfree */
void mm_free(void *payload) {
    block_t *block = payload - sizeof(header_t);
    block->allocated = FREE;
    footer_t *footer = get_footer(block);
    footer->allocated = FREE;
    insertblock(block);
    coalesce(block);
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 * NO NEED TO CHANGE THIS CODE!
 */
void *mm_realloc(void *ptr, size_t size) {
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    block_t* block = ptr - sizeof(header_t);
    copySize = block->block_size;
    if (size < copySize)
        copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/*
 * mm_checkheap - Check the heap for consistency
 */
void mm_checkheap(int verbose) {
    block_t *block = prologue;

    if (verbose)
        printf("Heap (%p):\n", prologue);

    if (block->block_size != sizeof(header_t) || !block->allocated)
        printf("Bad prologue header\n");
    checkblock(prologue);

    /* iterate through the heap (both free and allocated blocks will be present) */
    for (block = (void*)prologue+prologue->block_size; block->block_size > 0; block = (void *)block + block->block_size) {
        if (verbose)
            printblock(block);
        checkblock(block);
    }

    if (verbose)
        printblock(block);
    if (block->block_size != 0 || !block->allocated)
        printf("Bad epilogue header\n"); 
}

/* The remaining routines are internal helper routines */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static block_t *extend_heap(size_t words) {
    block_t *block;
    uint32_t size;
    size = words << 3; // words*8
    if (size == 0 || (block = mem_sbrk(size)) == (void *)-1)
        return NULL;
    /* The newly acquired region will start directly after the epilogue block */ 
    /* Initialize free block header/footer and the new epilogue header */
    /* use old epilogue as new free block header */
    block = (void *)block - sizeof(header_t);
    block->allocated = FREE;
    block->block_size = size;

    /* free block footer */
    footer_t *block_footer = get_footer(block);
    block_footer->allocated = FREE;
    block_footer->block_size = block->block_size;
    /* new epilogue header */
    header_t *new_epilogue = (void *)block_footer + sizeof(header_t);
    new_epilogue->allocated = ALLOC;
    new_epilogue->block_size = 0;
    insertblock(block);

    /* Coalesce if the previous block was free */
    return coalesce(block);
}
/* $end mmextendheap */

/*
 * place - Place block of asize bytes at start of free block block
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
 static block_t* place(block_t *block, size_t asize) {
    size_t split_size = block->block_size - asize;
    if(asize <= 112 && split_size >= MIN_BLOCK_SIZE){ /* sorts blocks smaller than 112 towards top of heap */
        removeblock(block);
        block->block_size = split_size;
        block->allocated = FREE;
        /* set footer of allocated block*/
        footer_t *footer = get_footer(block);
        footer->block_size = split_size;
        footer->allocated = FREE;
        /* update the header of the new free block */
        block_t *new_block = (void *)block + block->block_size;
        new_block->block_size = asize;
        new_block->allocated = ALLOC;
        /* update the footer of the new free block */
        footer_t *new_footer = get_footer(new_block);
        new_footer->block_size = asize;
        new_footer->allocated = ALLOC;
        insertblock(block);
        /* coalesce if next block is free*/
        coalesce(block); 
        return new_block;  
    }
    if(asize > 112 && split_size >= MIN_BLOCK_SIZE){ /* sorts blocks larger than 112 towards top of heap */
        /* split the block by updating the header and 
        marking it allocated*/
        removeblock(block);
        block->block_size = asize;
        block->allocated = ALLOC;
        /* set footer of allocated block*/
        footer_t *footer = get_footer(block);
        footer->block_size = asize;
        footer->allocated = ALLOC;
        /* update the header of the new free block */
        block_t *new_block = (void *)block + block->block_size;
        new_block->block_size = split_size;
        new_block->allocated = FREE;
        /* update the footer of the new free block */
        footer_t *new_footer = get_footer(new_block);
        new_footer->block_size = split_size;
        new_footer->allocated = FREE;
        insertblock(new_block);
        /* coalesce if next block is free*/
        coalesce(new_block);   
        return block;
    }
    /* splitting the block will cause a splinter so we just include it in the allocated block */
    block->allocated = ALLOC;
    footer_t *footer = get_footer(block);
    footer->allocated = ALLOC;
    removeblock(block);
    return block;

}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static block_t *find_fit(size_t asize) {
    /* first fit search */
    int index = find_index(asize);
    block_t *root_bucket = seglistp[index];
    block_t *b;
    b = root_bucket;
    if(root_bucket != NULL){ /* if bucket isn't empty, proceed normally */
        for (b = seglistp[index]; b->body.next != NULL; b = b->body.next) {
                if (asize <= b->block_size) {
                    return b;
                }
        }
        if(b->body.next == NULL && asize <= b->block_size){ /* check if fits into free list w/ one block */
            return b;
        }
    } 
    for(int i = index; i < NUM_OF_BUCKETS-1; i++){ /* if empty, search array for non-empty bucket */
            if(seglistp[i] != NULL && seglistp[i]->block_size >= asize){
                return seglistp[i];
            }
    }
    return NULL;
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static block_t *coalesce(block_t *block) {
    footer_t *prev_footer = (void *)block - sizeof(header_t);
    header_t *next_header = (void *)block + block->block_size;
    bool prev_alloc = prev_footer->allocated;
    bool next_alloc = next_header->allocated;
    if (prev_alloc && next_alloc) { /* Case 1 */ 
        /* no coalesceing */
         return block;
    }
    else if (prev_alloc && !next_alloc) { /* Case 2 */   
        /* remove current block and next block from free list */  
        block_t *next_block = (void*)block + block->block_size;
        removeblock(next_block);
        removeblock(block);
        /* Update header of current block to include next block's size */
        block->block_size += next_header->block_size;
        /* Update footer of next block to reflect new size */
        footer_t *next_footer = get_footer(block);
        next_footer->block_size = block->block_size;
        /* Update free list by inserting new free block*/
        insertblock(block);
    }
    else if (!prev_alloc && next_alloc) { /* Case 3 */       
         /* Update header of prev block to include current block's size and remove current and previous blocks from list and insert prev_block */
        block_t *prev_block = (void *)prev_footer - prev_footer->block_size + sizeof(header_t);
        removeblock(block);
        removeblock(prev_block);
        prev_block->block_size += block->block_size;
        /* Update footer of current block to reflect new size */
        footer_t *footer = get_footer(prev_block);
        footer->block_size = prev_block->block_size;
        insertblock(prev_block);
        block = prev_block;
     }

    else { /* Case 4 */
        /* remove blocks */
        /* Update header of prev block to include current and next block's size */
        block_t *prev_block = (void *)prev_footer - prev_footer->block_size + sizeof(header_t);
        block_t *next_block = (void*)block + block->block_size;
        removeblock(next_block);
        removeblock(prev_block);
        removeblock(block);
        prev_block->block_size += block->block_size + next_header->block_size;
        /* Update footer of next block to reflect new size */
        footer_t *next_footer = get_footer(prev_block);
        next_footer->block_size = prev_block->block_size;
        /* Update blocks*/
        insertblock(prev_block);
        block = prev_block;
    }
    return block;
}
static void insertblock(block_t *block){ /* insert block in bucket */
    int index = find_index(block->block_size);
     if(seglistp[index] != NULL){ /* checks if bucket is empty */
        block->body.next = seglistp[index];  
        block->body.prev = NULL;

        seglistp[index]->body.prev = block;
        seglistp[index] = block;
    }
    else if(seglistp[index] == NULL){
        seglistp[index] = block;

        block->body.next = NULL;
        block->body.prev = NULL;
    }     

}
static void removeblock(block_t *block){
    int index = find_index(block->block_size);
    if(block == seglistp[index]){ /* if removing first block of bucket */
        seglistp[index] = block->body.next;
    }
    if(block->body.prev != NULL){
        block->body.prev->body.next = block->body.next;
    }
    if(block->body.next != NULL){
        block->body.next->body.prev = block->body.prev;
    }
}
static int find_index(size_t size){
    int index = LOG2(size)-5;
    if(index >= NUM_OF_BUCKETS){ /* if bucket is too large (i.e. > 2^NUM_OF_BUCKETS) */
        index = NUM_OF_BUCKETS-1;
    }
    return index;
}
static footer_t* get_footer(block_t *block) {
    return (void*)block + block->block_size - sizeof(footer_t);
}

static void printblock(block_t *block) {
    
    uint32_t hsize, halloc, fsize, falloc;
    block_t * nextp, *prevp;

    hsize = block->block_size;
    halloc = block->allocated;
    footer_t *footer = get_footer(block);
    fsize = footer->block_size;
    falloc = footer->allocated;

    nextp = block->body.next;
    prevp = block->body.prev;

    if (hsize == 0) {
        printf("%p: EOL\n", block);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c] nextp: %p prevp: %p\n", block, hsize,
           (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'), nextp, prevp);
}

static void checkblock(block_t *block) {
    if ((uint64_t)block->body.payload % 8) {
        printf("Error: payload for block at %p is not aligned\n", block);
    }
    footer_t *footer = get_footer(block);
    if (block->block_size != footer->block_size) {
        printf("Error: header does not match footer\n");
    }
}
