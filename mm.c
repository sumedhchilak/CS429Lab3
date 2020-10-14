/* Sumedh Chilakamarri - High Level Description of Design:
 * My implementation involves using an Implicit Free List as in the Computer Systems Textbook.
 * This simple allocator will use boundary tag coalescing.
 * For the malloc implementation, I am using a Next Fit approach which is similar to the default first
 * fit approach in the textbook but instead starts where the previous search finished. I have another pointer
 * called finder that points to the last allocated block. The find fit function starts searching for the next free
 * block starting at the last allocated block and another loop checking from the beginning to the last allocated block
 * to enhance throughput.
 * There will also be splitting to create new free blocks.
 * If the remainder of the block after splitting is greater than or equal to the minimum block size
 * then the program will make sure the block will be split
 * There is an allocated prologue header/footer and epilogue header
 * There will be good space utilization and thoroughput with this approach.
 */
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// Declared Constants and descriptions from Computer Systems Textbook
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 12)
#define MAX(x, y) ((x) > (y)? (x) : (y))
// Pack size and the allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))
// read and write a word at address p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
// read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
// Address of block ptr bp header and footer computer
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
// Address of next and previous blocks computed given the block ptr bp
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

// Degbugging From Zachary Leeper's TA Session
// Calls deleted in actual code as TA said it would reduce optimization in Piazza
#ifdef DEBUG
#define CHECKHEAP mm_check()
#define INC_NUM_FREEBLOCKS num_freeblocks++
#define DEC_NUM_FREEBLOCKS num_freeblocks--
#else
#define CHECKHEAP
#define INC_NUM_FREEBLOCKS
#define DEC_NUM_FREEBLOCKS
#endif

// Global Variables
static char *heap_listp = 0; // First block pointer
static char *finder; // next fit block pointer
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

// Header Node. Contains a single field which is the packed size 
// and is allocated
typedef struct header {
    size_t size_alloc;
} header_t;

// Footer Node. Contains a single field which is the packed size 
// and is allocated
typedef struct footer {
    size_t size_alloc;
} footer_t;

// FreeBlock Node. Contained within unallocated blocks. Can be used to implement
// an explicit free list.
typedef struct freeblock {
    struct freeblock *next;
    struct freeblock *prev;
} freeblock_t;

void put_footer(footer_t *f, size_t size, bool alloc) {
    assert(f);
    assert(size % ALIGNMENT == 0);
    f->size_alloc = (alloc & 0x1) | size;
}

size_t get_size_footer(footer_t *f) {
    assert(f);
    return (~0x7) & f->size_alloc;
}

void put_header(header_t *h, size_t size, bool alloc) {
    assert(h);
    assert(size % ALIGNMENT == 0);
    h->size_alloc = alloc | size;
}

size_t get_size(header_t *h) {
    assert(h);
    return (~0x7) & h->size_alloc;
}

size_t get_alloc(header_t *h) {
    assert(h);
    return h->size_alloc & 0x1;
}

footer_t *get_footer(header_t *h) {
    assert(h);
    return (footer_t *)(((size_t)h) + get_size(h) - sizeof(footer_t));
}

header_t *get_header(void *p) {
    assert(p);
    return (header_t *)(((size_t)p) - sizeof(header_t));
}

header_t *get_above_header(header_t *h) {
    assert(h);
    return (header_t *)(((size_t)h) + get_size(h));
}

header_t *get_below_header(header_t *h) {
    assert(h);
    footer_t *prev_footer = (footer_t *)(((size_t)h) - sizeof(footer_t));
    return (header_t *)(((size_t)h) - get_size_footer(prev_footer));
}

void *get_payload(header_t *h) {
    assert(h);
    return (void*)(((size_t) h) + sizeof(header_t));
}

freeblock_t *get_freeblock(header_t *h) {
    assert(h);
    return (freeblock_t *)(((size_t)h) + sizeof(header_t));
}

header_t *get_freeblock_header(freeblock_t *freeblock) {
    assert(freeblock);
    return (header_t *)(((size_t)freeblock) - sizeof(header_t));
}

/* 
 * mm_init - initialize the malloc package.
 * Four words from the memory system selected and initialized in order to create empty free list.
 * Initial free block created by extending the heap 
 * Used elements from Computer Systems textbook
 */
int mm_init(void)
{
    // Initial empty heap being created
    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1){
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0,1));
    heap_listp += (2 * WSIZE);
    finder = heap_listp;
    // Empty heap with free blocks of CHUNKSIZE byted is extended
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 *     Method derived from the Computer Systems Textbook
 */
void *mm_malloc(size_t size)
{
   size_t asize;
   size_t extendsize;
   char *bp;
   if(size == 0){
       return NULL;
   }
   // The block size is adjusted according to the required allignement
   if(size <= DSIZE){
       asize = 2 * DSIZE;
   } else{
       asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
   }
   // trying to find a fit by searching the free list
   if((bp = find_fit(asize)) != NULL){
       place(bp, asize);
       return bp;
   }
   // If the fit was not found then ore memory requested and block placed
   extendsize = MAX(asize, CHUNKSIZE);
   if((bp = extend_heap(extendsize/WSIZE)) == NULL){
       return NULL;
   }
   place(bp, asize);
   return bp;
}

// Function from the Computer Systems Textbook
/*
    Function uses a next fit technique to search for a free block that fits.
    The first loop starts where the previous search finished and searches 
    for the next free block that fits. The other loop searches starting from
    the beginning until the previous search.
*/
static void *find_fit(size_t asize){
    char * temp = finder;
    void *bp;
    // Next Fit Search Implementation
    // Searches for fit starting at the most recent last allocated block (where the previous search finished)
    for(finder = finder; GET_SIZE(HDRP(finder)); finder = NEXT_BLKP(finder)){
        if(!GET_ALLOC(HDRP(finder)) && (asize <= GET_SIZE(HDRP(finder)))){
            return finder;
        }
    }
    // Searches for fit from starting until the previous search;
    for(bp = heap_listp; bp < temp; bp = NEXT_BLKP(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL;
}
/*
    Helper: Function from the Computer Systems Textbook
    If the remainder of the block after splitting is greater than or equal to the minimum block size
    then the program will make sure the block will be split
*/
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    if((csize - asize) >= (2 * DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
/*
    Helper: extend_heap from Computer Systems Textbook
    Method makes sure the requested size is rounded up to the nearest multiple of 2 words
    and then the additional heap space is retrieved from memory.
*/
static void *extend_heap(size_t words){
    char *bp;
    size_t size;
    // Allocate even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }
    // Free block header and footer and epilogue header are initialized
    PUT(HDRP(bp), PACK(size, 0)); // Free block header
    PUT(FTRP(bp), PACK(size, 0)); // Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header
    // Coalesce if previous block free
    return coalesce(bp);
}

/*
 * mm_free - Freeing a block does nothing.
 *  From the Computer Systems Textbook
 *  Previously allocated block is freed and the adjacent free blocks
 *  are merged using boundary-tag coalescing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 Method uses the Boundary Tag Coalescing technique.
The method uses the four cases as described in the textbook and are described/implemented below
From the Computer Systems Textbook
*/
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    // Case 1
    // Next and prev allocated and block being freed in the middle
    if(prev_alloc && next_alloc){
        return bp;
    }
    // Case 2
    // next is free and previous is allocated
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // Case 3
    // Previous is free and the next block is allocated
    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    // Case 4
    // Both previous and next are free
    } else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // Ensures the next fit finder pointer is not pointing to a recently freed and coalesced block
    // Edge Case
    if((finder < NEXT_BLKP(bp)) && (finder > (char *)bp)){
        finder = bp;
    }
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * The pointed to the allocated region of at least size bytes is returned
 * following the limits as addressed in the handout.
 */
void *mm_realloc(void *ptr, size_t size)
{
    // Basic Implementation with elements from Computer Systems Textbook and Assignment Handout
    void *old = ptr;
    void *newp;
    size_t copy;
    // Gets new ptr block and size of payload calculated
    newp = mm_malloc(size);
    if (newp == NULL){
      return NULL;
    }
    // if size is 0 then call is equivalent to mm_free(ptr)
    if(size == 0){
        mm_free(ptr);
        return 0;
    }
    // old data copied
    copy = *(size_t *)((char *)old - SIZE_T_SIZE);
    if (size < copy){
      copy = size;
    }
    // Payload of ptr block copied into payload of new block
    memcpy(newp, old, copy);
    // old block is freed
    mm_free(old);
    // Pointed to the new block returned
    return newp;
}
// Check Method from TA Discussion Session Zachary Leeper
// global variables
static freeblock_t *freeHead;
static header_t *firstHead;
static int num_freeblocks;

/* Derived from Zachary Leeper's TA Discussion Session
 * mm_check - Scans the heap for inconsistencies, should exit with an assert
 * if an inconsistency is found.
 */
void mm_check()
{
    header_t *h = firstHead;
    bool prev_alloc = !get_alloc(h);
    //assert prologue header is correct
    assert(get_below_header(h) == (header_t *) mem_heap_lo());
    //block level invariants
    while(get_size(h > 0)){
        footer_t *f = get_footer(h);
        size_t size = get_size(h);
        //assert header and footer have the same size and allocation
        assert(get_size_footer(f) == size);
        //assert header and footer match
        assert((void *)f - size + sizeof(footer_t) == h);
        //assert no contiguous free blocks
        assert(prev_alloc != 0 && get_alloc(h) != 0);
        //assert size is aligned
        assert(size % ALIGNMENT == 0);
        assert((long) get_payload(h) % ALIGNMENT == 0);
        //assert header/footer inside the heap
        assert(h > mem_heap_lo() && h < mem_heap_hi());
        prev_alloc = get_alloc(h);
        h = get_above_header(h);
    }
    //assert epilogue is correct
    assert((void *) get_above_header(h) == mem_heap_hi() - 7);
    freeblock_t *fb = freeHead;
    freeblock_t *prev = freeHead->prev;
    freeblock_t *next = freeHead->next;
    int count = 0;
    //list level invariants
    while(fb){
        count++;
        h = get_freeblock_header(fb);
        //assert block is actually free
        assert(!get_alloc(h));
        if(prev)
            assert(prev->next == fb);
        if(next)
            assert(next->prev == fb);
        assert(fb > mem_heap_lo() && fb < mem_heap_hi());
        fb = next;
    }
    //check for backwards cycle
    fb = prev;
    while(fb){
        fb = fb->prev;
    }
    //assert number of freeblocks in the list = number of free blocks
    assert(count == num_freeblocks);
    return 0;
}












