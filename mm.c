/* High Level Description of Design:

 * My implementation involves using doubly linked explicit freelist.
 * Each allocated block keeps track of the size in a hidden fixed size header.
 * Each free block keeps track of size, the next-neighbor,
 * and the previous neighbor in the fixed header size.
 * The process will be Last in First Out (LIFO) and will be in address order
 * Only disadvantage to this approach would be that the free blocks would need
 * to be large enough in order to contain pointers.
 * For the malloc implementation, I also plan on using a First Fit approach where list is free
 * from the beginning and the first free blocks large enough for the payload are selected.
 * There will also be splitting to create new free blocks 
 * Allocated Block :  [header | payload | footer]
 * Free Block: [header | previous | next | payload | footer]
 * doubly linked Explicit Free List: [null <- freeblock1 -> freeblock2 <- freeblock3 -> ...... <- freeblockN -> null]
 * After the first fleeblock of the appropriate size is found, then its allocated bits
 * is set to zero and the freed block is coalesced with other free neighboring blocks as needed.
 * 
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

// Declared Constants from Computer Systems Textbook
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 8)
#define MIN 24
#define MAX (x, y) ((x) > (y)? (x) : (y))
#define PACK (size, alloc) ((size) | (alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) == (val))
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


static char *point_list_heap = 0;
static char *point_list_free = 0;

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
 * Used elements from Computer Systems textbook
 */
int mm_init(void)
{
    // Initial empty heap being created
    if((point_list_heap = mem_sbrk(4 * WSIZE)) == (void *)-1){
        return -1;
    }
    PUT(point_list_heap, 0);
    PUT(point_list_heap + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(point_list_heap + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(point_list_heap + (3 * WSIZE), PACK(0,1));
    point_list_heap += (2 * WSIZE);
    // Empty heap with free blocks of CHUNKSIZE byted is extended
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    return 0;
}
/*
    Helper: extend_heap from Computer Systems Textbook
*/
static void *extend_heap(size_t words){
    char*bp;
    size_t size;
    // Allocate even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }
    // Free block header and footer and epilogue header are initialized
    PUT(HDRP(bp), PACK(size, 0)); // Free block header
    PUT(FTRP(bp), PACK(size, 0)); // Free block footer
    PUT(HDRP(NEEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header
    // TODO:
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;
    if(size == 0){
        return NULL;
    }
    if(point_list_heap == 0){
        mm_init();
    }
    //TODO
    return NULL;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    return NULL;
}

/*
 * mm_check - Scans the heap for inconsistencies, should exit with an assert
 * if an inconsistency is found.
 */
void mm_check()
{
    return;
}












