//#################################################################################################
//
// This is a proof-of-concept implementation of the HashSieve algorithm, as originally 
// described in the Crypto'15 paper:
//
//	 "Sieving for shortest vectors in lattices using angular locality-sensitive hashing"
//
// This implementation was written by Thijs Laarhoven [mail at thijs dot com] in 2014. The 
// HashSieve algorithm is an extension of the GaussSieve algorithm, introduced by Micciancio
// and Voulgaris at SODA'10. The whole idea of lattice sieving further dates back to work of
// Ajtai, Kumar, and Sivakumar at STOC'01. 
//
// This code is released under the MIT license (see https://opensource.org/licenses/MIT).
//
//#################################################################################################

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include <ctype.h>

//########################################
//  		SCHEME PARAMETERS
//########################################
// N:   
//		Dimension of the lattice and the Euclidean space (full-rank lattices)
// SEED: 
//		Seed of the input challenge basis (usually 0)
// PROBE: 
//		Level of probing
//			PROBE = 0: Do not use probing (fastest but uses more space)
//			PROBE = 1: 1-level probing (factor ~2 slower, factor [1 + k/2] less space)
//			PROBE = 2: 2-level probing (factor ~4 slower, factor [1 + k/2 + k(k-1)/8] less space)
// K: 
//		Hash length; number of hyperplanes used for a partition in a single hash table
//			Theoretically: k = 0.2209n
// T: 
//		Number of hash tables
// 			Theoretically, without probing: T = 2^(0.1290n)
//			Theoretically, 1-level probing: T1 = 2^(0.1290n) / [1 + k/2]
//			Theoretically, 2-level probing: T2 = 2^(0.1290n) / [1 + k/2 + k(k-1)/8]
//
// Note that K = T = 1 roughly corresponds to an unoptimized implementation of the original GaussSieve
//
// Some commonly used numbers: 
//		 N -  K -    T -  T1 -  T2
//		-------------------------------
// 		30 -  7 -   15 -   3
// 		35 -  8 -   23 -   5
// 		40 -  9 -   36 -   7
// 		45 - 10 -   56 -   9
// 		50 - 11 -   87 -  13
// 		55 - 12 -  137 -  19 -   6
// 		60 - 13 -  214 -  28 -   8
// 		65 - 14 -  334 -  41 -  10
// 		70 - 15 -  523 -  60 -  14
// 		75 - 17 -  817 -  88 -  20
// 		80 - 18 - 1278 - 130 -  27
//		85 - 19 - 1999 - 193 -  38
// 		90 - 20 - 3126 - 286 -  54
// 		95 - 21 - 4888 - 426 -  77
//	   100 - 22 - 7643 - 635 - 109
//########################################
#define N 50
#define SEED 0
#define PROBE 1
#define K 11
#define T 13

//########################################
//  		GLOBAL PARAMETERS
//########################################
#define MAX_VECTORS 1000000				// Maximum total number of vectors in the system
#define MAX_ITERATIONS 100000000000		// Maximum number of "iterations"
#define MAX_COLLISIONS_1 10000000		// Maximum number of type-1 collisions: sampling the 0-vector
#define MAX_COLLISIONS_2 10000000		// Maximum number of type-2 collisions: after reductions, obtaining the 0-vector 
#define BUCKETS (1 << (K-1))			// Number of buckets in each HashSieve hash table

// For each vector we store the entries and its norm squared
struct vect {
	long long int Coord[N];
	unsigned long long int Norm2;
};

// For the Gram-Schmidt basis we also store the entries and their squared norms
struct dvect {
	double Coord[N];
	double Norm2;
};

// Each hash table bucket contains a list of pointers to vectors
// The length indicates the current number of occupied entries
// The size indicates the current size of the underlying array
struct bucket {
	vect** Pointers;
	unsigned int Length;
	unsigned int Size;
};

// HashSieve-specific variables
unsigned short A[T][K][2]; 					// Hash matrices: only stores coordinates of non-zero stuff
bucket HashTables[T][1 << (K-1)];			// Locality-sensitive hash tables

// GaussSieve variables
vect B[N];
dvect Bs[N];
double mu[N][N];
vect Vectors[MAX_VECTORS];					// Vectors in the system
vect* Stack[MAX_VECTORS];					// Stack of pointers to vectors
unsigned long long int VectorsLength = 0;	// Total number of vectors in the system
unsigned long long int StackLength = 0;		// Number of vector pointers on the stack
unsigned long long int Reductions1 = 0;		// Count number of v-reductions
unsigned long long int Reductions2 = 0;		// Count number of w-reductions
unsigned long long int Collisions1 = 0;		// Count number of collisions occurring from sampling
unsigned long long int Collisions2 = 0;		// Count number of list collisions
unsigned long long int Comparisons = 0;		// Count number of inner products between v and w
unsigned long long int Hashes = 0;			// Count number of "hashes" computed
unsigned long long int MinNorm2; 			// Current minimum of squared vector norms
unsigned long long int Target;				// The target length for the current dimension
unsigned long long int Iteration;			// The current iteration count

// Klein sampler variables
dvect xKlein;
double AKlein;


// Compute the inner product between different integer (lattice) vectors v and w
long long int ip(vect* v, vect* w)
{
	long long int res = 0;
	for(int i = 0; i < N; i++){
		res += v->Coord[i] * w->Coord[i];
	}
	return res;
}

// Compute the inner product between a lattice vector and a real vector
double ip(vect* v, dvect* w)
{
	double res = 0;
	for(int i = 0; i < N; i++){
		res += (double)v->Coord[i] * w->Coord[i];
	}
	return res;
}

// Compute the inner product between two real vectors v and w
double ip(dvect* v, dvect* w)
{
	double res = 0;
	for(int i = 0; i < N; i++){
		res += v->Coord[i] * w->Coord[i];
	}
	return res;
}

// Add a vector v to a hash table bucket b
void bucketAdd(bucket* b, vect* v)
{
	// If the bucket overflows, make a new bucket of twice the size
	if(b->Length == b->Size){
		b->Size <<= 1;
		vect** NewPointers;
		NewPointers = new vect*[b->Size];
		for(short i = 0; i < b->Length; i++){
			NewPointers[i] = b->Pointers[i];
		}
		delete [] b->Pointers;
		b->Pointers = NewPointers;
	}
	
	// Insert v into the bucket
	b->Pointers[b->Length] = v;
	b->Length++;
}

// Remove a vector v from a hash table bucket b
void bucketRemove(bucket* b, vect* v)
{
	// Find w's position in the hash bucket
	int vPos = 0;
	while(b->Pointers[vPos] != v && vPos < b->Length){
		vPos++;
	}
	if(vPos >= b->Length){
       	perror("Vector not found in bucket...\n");
       	exit(-1);
	}		
	// Make the bucket shorter		
	b->Length--;
	b->Pointers[vPos] = b->Pointers[b->Length];
}

// Compute the locality-sensitive hash of a vector v for table t
int lshash(vect* v, int t)
{
	int res = 0;
	int AbsIPMax = 100000000;
	int AbsIPMaxPos = 0;
	int AbsIPMaxSgn = 0;
	for(int k = 0; k < K; k++){
		res <<= 1;
		int IP = v->Coord[A[t][k][0]] - v->Coord[A[t][k][1]];
		if(IP > 0)
			res++;
	}
	
	// Merge buckets u and 2^K - u - 1
	if(res >= (1 << (K-1)))
		res = 2 *  (1 << (K-1)) - res - 1;
	return res;
}

// Add/subtract the vector w to/from v
void add(vect* v, vect* w, long long int vw)
{
	if(vw > 0){
		// Subtract w from v
		for(int i = 0; i < N; i++)
			v->Coord[i] -= w->Coord[i];
		v->Norm2 += w->Norm2 - 2 * vw;
	}
	else{
		// Add w to v
		for(int i = 0; i < N; i++)
			v->Coord[i] += w->Coord[i];
		v->Norm2 += w->Norm2 + 2 * vw;
	}
}

// Generate a new, randomly sampled vector v using a naive method
void sampleSimple(vect* v)
{
	int i, j;
	long long int coeff;
	for (j = 0; j < N; j++){
		v->Coord[j] = 0;
	}
	for (i = 0; i < N; i++){
		coeff = (rand() % 2);
		//coeff = (1.0 * rand() / RAND_MAX > 0.02 ? 0 : 1);
		for (j = 0; j < N; j++){
			v->Coord[j] += (long long int)coeff * (B[i].Coord[j]);
		}
	}
	v->Norm2 = 0;
	for(j = 0; j < N; j++){
		v->Norm2 += v->Coord[j] * v->Coord[j];
	}
}

// Import the basis from the given text file filestring
void importBasis(char* filestring)
{
	int i, j, dgt, busy, crd, crdsgn;
    FILE* input_file;
    
    //char filestring[500];
    //snprintf(filestring, 500, "C:\\Google Drive\\Cpp\\SVP\\dim%usd%u-LLL.txt", N, SEED);
    input_file = fopen(filestring, "r");
    if (input_file == 0){
        perror("Cannot open input file...\n");
        exit(-1);
    }
    else{
    	i = 0;
    	j = 0;
        busy = 0;			// Currently reading a coordinate?
		crd = 0; 			// Coordinate value
		crdsgn = 1; 		// Sign of coordinate
        while ((dgt = fgetc(input_file)) != EOF)
        {
        	if (dgt == '-'){
        		// Start fresh coordinate
        		busy = 1;
        		crd = 0; 
        		crdsgn = -1;
        	}
            else if (isdigit(dgt)){
            	if (busy > 0){
            		// Append digit to coordinate
            		crd *= 10;
            		crd += dgt - '0';
            	}
            	else {
            		// Start fresh coordinate
            		busy = 1;
            		crd = dgt - '0'; 
					crdsgn = 1;           		
            	}
        	}
        	else {
        		if (busy > 0){
            		// Write coordinate to basis
            		B[i].Coord[j] = crd * crdsgn;
            		j++;
            		if (j == N){
						B[i].Norm2 = 0;
						for(int i1 = 0; i1 < N; i1++){
							B[i].Norm2 += B[i].Coord[i1] * B[i].Coord[i1];
						}
						j = 0;
            			i++;
            		}
					busy = 0;
            	}
        	}
		}
	}
    fclose(input_file);
}

// The randRound algorithm as described by Klein
int randRound(double c, double r)
{
	int p = floor(r);
	int q = p + 1;
	double a = r - (double)p;
	double b = 1 - a;
	double spos = 0;
	double sneg = 0;
	for(int i = 0; i < 10; i++){
		spos += exp(-c * (i + b) * (i + b));
		sneg += exp(-c * (i + a) * (i + a));
	}
	double s;
	s = spos + sneg;
	spos = spos / s;
	sneg = sneg / s;
	
	double rr;
	rr = 1.0 * ((double)rand() / RAND_MAX);
	int i = 0;
	if (rr < spos){
		// Integer lies on the positive side of r
		double spos2;
		spos2 = exp(-c * (i + b) * (i + b)) / s;
		while(rr > spos2){
			i++;
			spos2 += exp(-c * (i + b) * (i + b)) / s;
		}
		return q + i;
	}
	else{
		// Integer lies on the negative side of r
		rr = 1 - rr; // Total weight on this side of the curve is 1 - rr
		double sneg2;
		sneg2 = exp(-c * (i + a) * (i + a)) / s;
		while(rr > sneg2){
			i++;
			sneg2 += exp(-c * (i + a) * (i + a)) / s;
		}
		return p - i;
	}
}

// Compute the Gram-Schmidt basis and store it in Bs
void gramSchmidt()
{
	int i,j,k;
	for(i = 0; i < N; i++){
		for(j = 0; j < N; j++){
			mu[i][j] = 0;
			Bs[i].Coord[j] = (double)B[i].Coord[j];
		}
		for(k = 0; k < i - 1; k++){
			mu[i][k] = ip(&B[i], &Bs[k]) / Bs[k].Norm2;
			for(j = 0; j < N; j++){
				Bs[i].Coord[j] -= mu[i][k] * Bs[k].Coord[j];
			}
		}
		Bs[i].Norm2 = ip(&Bs[i], &Bs[i]);
	}
}


// Klein's near algorithm -- Call this with d = n - 1 and x = (0, ..., 0)
void nearA(vect* res, double A, dvect* x, int d)
{
	if(d == -1){
		for(int i = 0; i < N; i++){
			res->Coord[i] = 0;
		}
		res->Norm2 = ip(res, res);
	}
	else{
		double rd = 0;
		for(int i = 0; i < N; i++){
			rd += (double)x->Coord[i] * Bs[d].Coord[i];
		}
		rd = rd / Bs[d].Norm2;
		//printf("%u\n", Bs[d][N]);
		double cd = A * Bs[d].Norm2;
		double ld = randRound(cd, rd);
		dvect xp;
		for(int i = 0; i < N; i++){
			xp.Coord[i] = x->Coord[i] + (double)((ld - rd) * Bs[d].Coord[i] - ld * B[d].Coord[i]);
		}
		xp.Norm2 = ip(&xp, &xp);
		nearA(res, A, &xp, d - 1);
		for(int i = 0; i < N; i++){
			res->Coord[i] += (long long int)(ld * B[d].Coord[i]);
		}
		res->Norm2 = ip(res, res);
	}
}

// Initialize Klein sampler; initialize zero-vector x and value A
void initKlein()
{
	for(int i = 0; i < N; i++){
		xKlein.Coord[i] = 0;
	}
	xKlein.Norm2 = 0;
	
	AKlein = log(N) * log(N);
	double minval = Bs[0].Norm2;
	for(int i = 1; i < N; i++){
		if(Bs[i].Norm2 < minval){
			minval = Bs[i].Norm2;
		}
	}
	AKlein /= minval;
	AKlein /= 70.;
}


// Initialize the hash vectors and the hash tables
void initHashes()
{
	// Initialize hash tables as empty
	for(int t = 0; t < T; t++){
		// Initialize random sparse hash vectors by choosing two non-zero entries
		for(int k = 0; k < K; k++){
			A[t][k][0] = (rand() % N);
			A[t][k][1] = (rand() % N);
			//A[t][k][1] = (A[t][k][0] % 2 == 0) ? (A[t][k][0] + 1) : (A[t][k][0]);
			while(A[t][k][1] == A[t][k][0])
				A[t][k][1] = (rand() % N);
		}
		// Initialize empty hash buckets
		for(int b = 0; b <  (1 << (K-1)); b++){
			HashTables[t][b].Length = 0;
			HashTables[t][b].Size = 4;
			HashTables[t][b].Pointers = new vect*[4];
		}
	}
}

// Initialize the stack (and the vectors list) by adding basis vectors to it
void initStack()
{
	// Push all basis vectors to the stack
	for(int i = 0; i < N; i++){
    	for(int j = 0; j < N; j++){
    		Vectors[i].Coord[j] = B[i].Coord[j];
    	}
    	Vectors[i].Norm2 = B[i].Norm2;
    	VectorsLength++;
    	Stack[i] = &Vectors[i];
    	StackLength++;
    }
}

// Initialize various parameters of the HashSieve algorithm
void initParams()
{
	// Hardcoded shortest vector lengths / SVP records according to the SVP challenge database and/or own experiments
	// These are sharp bounds for finding the shortest vector in SVP challenge lattices with seed 0
	unsigned long long int Targets[200];
	Targets[30] = 2091662;
    Targets[31] = 2117044;
    Targets[32] = 2147531;
    Targets[33] = 2301849;
    Targets[34] = 2302448;
    Targets[35] = 2637604;
    Targets[36] = 2535727;
    Targets[37] = 2470204;
    Targets[38] = 2662328;
    Targets[39] = 3022037;
	Targets[40] = 2898390;
    Targets[41] = 2834609;
    Targets[42] = 2414615;
    Targets[43] = 3037224;
    Targets[44] = 2825373;
    Targets[45] = 3098331;
    Targets[46] = 2989372;
    Targets[47] = 3187572;
    Targets[48] = 3222705;
    Targets[49] = 3454355;
    Targets[50] = 3584095;
    Targets[51] = 3551524;
    Targets[52] = 3633605;
    Targets[53] = 3496843;
    Targets[54] = 3694084;
	Targets[55] = 3773021;
	Targets[56] = 3900625;
	Targets[57] = 3815991;
	Targets[58] = 4072324;
	Targets[59] = 3781187;
	Targets[60] = 3779136;
	Targets[61] = 4464769;
	Targets[62] = 4380649;
	Targets[63] = 4228565;
	Targets[64] = 4426816;
	Targets[65] = 4396757;
	Targets[66] = 4405628;
	Targets[67] = 4787344;
	Targets[68] = 4588164;
	Targets[69] = 4778537;
	Targets[70] = 4596736;
	Targets[71] = 4963938;
	Targets[72] = 4752400;
	Targets[73] = 4800481;
	Targets[74] = 5085025;
	Targets[75] = 5202961;
	Targets[76] = 5026564;
	Targets[77] = 5500000;
	Targets[78] = 5171076;
	Targets[79] = 5508409;
	Targets[80] = 5166529;
	Target = Targets[N];
	StackLength = 0;
	VectorsLength = 0;
	Reductions1 = 0;
	Reductions2 = 0;
	Comparisons = 0;
	Collisions1 = 0;
	Collisions2 = 0;
	Hashes = 0;
	Iteration = 0;
	MinNorm2 = 100000000000;
}

// Sample a new vector using Klein's sampler
void sampleKlein(vect* res)
{
	nearA(res, AKlein, &xKlein, N - 1);
}

//###############################################################################
//###############################################################################
//###############################################################################

// The main execution of the HashSieve algorithm

int main(void)
{	

Start:
	srand(time(0));			// Use srand(0); for reproducible results

    char filestring[500];
    snprintf(filestring, 500, "dim%usd%u-LLL.txt", N, SEED);
	importBasis(filestring);
	gramSchmidt();
	initKlein();
	initParams();
	initHashes();
	initStack();
    
	printf("=====  HashSieve  ======\n" );
	printf("Dimension (N):  %8d\n", N);
	printf("Random seed:    %8d\n", SEED);
	printf("Probe level:    %8d\n", PROBE);
	printf("Target length:  %8d\n", Target);
	printf("Hash length (k): %7d\n", K);
	printf("Hash tables (t): %7d\n", T);
	printf("------------------------\n");
	
	// Some dummy variables used in the algorithm
	int i,j,k,m,n,t;
	vect** Candidates;
	vect* v;
	vect* w;
	int vHash[T];			// "Temporary" variable for hashes of a target vector v
	int vHashp;				// Shifted hashes of v used for probing only
	int wHash[T];			// "Temporary" variable for hashes of a candidate vector w
	long long int vw;
	long long int vwAbs;
	long long int vwAbsDouble;
	long long int NCandidates;
	int vReduced;
	time_t start = time(NULL);
	time_t now;
	time_t end;
	
	// The main algorithm loop
	while(Iteration < MAX_ITERATIONS && Collisions2 < MAX_COLLISIONS_2){
		Iteration++;
		
		// Get vector from stack, or sample a new one if the stack is empty
		if(StackLength == 0){
			if(VectorsLength == MAX_VECTORS){
				perror("Vector list overflow...\n");
        		goto End;
			}
			sampleKlein(&Vectors[VectorsLength++]);
			//sampleSimple(&Vectors[VectorsLength++]);
			while(Vectors[VectorsLength-1].Norm2 == 0 && Collisions1 < MAX_COLLISIONS_1){
				Collisions1++;
				sampleKlein(&Vectors[VectorsLength-1]);
				//sampleSimple(&Vectors[VectorsLength-1]);
			}
			v = &Vectors[VectorsLength-1];
		}
		else{
			v = Stack[--StackLength];
		}
		
		vReduced = 0;
		// Check each table for candidate near list vectors
		for(t = 0; t < T; t++){
				
			//###############################################################################
			// 1. Search the bucket labeled h(v); the only step when not using probing
			//###############################################################################
			
			// Compute v's hash value
			vHash[t] = lshash(v, t);
			Hashes += K;
			Candidates = HashTables[t][vHash[t]].Pointers;
			NCandidates = HashTables[t][vHash[t]].Length;
			
			// Go through the list to find reducing vectors
			for(j = NCandidates - 1; j >= 0; j--){
				w = Candidates[j];
				vw = ip(v, w);				
				Comparisons++;
				vwAbs = (vw > 0 ? vw : -vw);
				vwAbsDouble = (vwAbs << 1);
			
				// Reduce v with w if possible
				if(vwAbsDouble > w->Norm2){
					add(v, w, vw);
					Reductions1++;
					vReduced = 1;
					goto vEnd;
				}
			
				// Reduce w with v if possible
				if(vwAbsDouble > v->Norm2){
					
					// Remove w from the hash tables
					for(int tt = 0; tt < T; tt++){
						wHash[tt] = lshash(w, tt);
						Hashes += K;
						bucketRemove(&HashTables[tt][wHash[tt]], w);
					}
					
					// Reduce w with v
					add(w, v, vw);
					
					Reductions2++;
					if(w->Norm2 > 0)
						Stack[StackLength++] = w;
					else
						Collisions2++;
				}
			}
			
			//###############################################################################
			// 2. Search all buckets adjacent to h(v) as well; used during 1-level probing
			//###############################################################################
			
			// One layer of probing: visiting all adjacent Buckets as well 
			if(PROBE == 1){
				for(int bit = 0; bit < K; bit++){
					// Compute v's hash value
					vHashp = vHash[t] ^ (1 << bit);
					if(vHashp >= BUCKETS)
						vHashp = 2 * BUCKETS - vHashp - 1;
						
					//Hashes += K; -- Updating the hashes is cheap; even cheaper than regular hash computations
					Candidates = HashTables[t][vHashp].Pointers;
					NCandidates = HashTables[t][vHashp].Length;
					
					// Go through the list to find reducing vectors
					for(j = NCandidates - 1; j >= 0; j--){
						w = Candidates[j];
						vw = ip(v, w);
						Comparisons++;
						vwAbs = (vw > 0 ? vw : -vw);
						vwAbsDouble = (vwAbs << 1);
					
						// Reduce v with w if possible
						if(vwAbsDouble > w->Norm2){
							add(v, w, vw);
							Reductions1++;
							vReduced = 1;
							goto vEnd;
						}
					
						// Reduce w with v if possible
						if(vwAbsDouble > v->Norm2){
							
							// Remove w from the hash tables
							for(int tt = 0; tt < T; tt++){
								wHash[tt] = lshash(w, tt);
								Hashes += K;
								bucketRemove(&HashTables[tt][wHash[tt]], w);
							}
							
							// Reduce w with v
							add(w, v, vw);
							
							Reductions2++;
							if(w->Norm2 > 0)
								Stack[StackLength++] = w;
							else
								Collisions2++;
						}	
					}
				}
			}
			
			//###############################################################################
			// 3. Search all buckets 2-adjacent to h(v) as well; used during 2-level probing
			//###############################################################################
			
			// Two layers of probing: visiting all buckets at distance 1 and 2 as well
			else if(PROBE == 2){
				for(int bit = 0; bit < K; bit++){
					for(int bit2 = 0; bit2 <= bit; bit2++){
						
						if(bit2 == bit)
							vHashp = vHash[t] ^ (1 << bit);
						else
							vHashp = (vHash[t] ^ (1 << bit)) ^ (1 << bit2);
						
						if(vHashp >= BUCKETS)
							vHashp = 2 * BUCKETS - vHashp - 1;
							
						//Hashes += K; -- Updating the hashes is cheap
						Candidates = HashTables[t][vHashp].Pointers;
						NCandidates = HashTables[t][vHashp].Length;
						
						// Go through the list to find reducing vectors
						for(j = NCandidates - 1; j >= 0; j--){
							w = Candidates[j];
							vw = ip(v, w);
							Comparisons++;
							vwAbs = (vw > 0 ? vw : -vw);
							vwAbsDouble = (vwAbs << 1);
						
							// Reduce v with w if possible
							if(vwAbsDouble > w->Norm2){
								add(v, w, vw);
								Reductions1++;
								vReduced = 1;
								goto vEnd;
							}
						
							// Reduce w with v if possible
							if(vwAbsDouble > v->Norm2){
								
								// Remove w from the hash tables
								for(int tt = 0; tt < T; tt++){
									wHash[tt] = lshash(w, tt);
									Hashes += K;
									bucketRemove(&HashTables[tt][wHash[tt]], w);
								}
								
								// Reduce w with v
								add(w, v, vw);
								
								Reductions2++;
								if(w->Norm2 > 0)
									Stack[StackLength++] = w;
								else
									Collisions2++;
							}	
						}
					}
				}
			}		
		}
		
vEnd:	// We have reached a decision for vector v
		// Push v to stack, list, or delete altogether
		if(vReduced == 0){
			if(v->Norm2 > 0){
				
				// Push v to the hash tables
				for(t = 0; t < T; t++)
					bucketAdd(&HashTables[t][vHash[t]], v);

				// Check for new minimum
				if(v->Norm2 < MinNorm2){
					now = time(NULL);
					printf("New minimum: %11llu (%5d sec)\n", v->Norm2, (now - start)); 
					MinNorm2 = v->Norm2;
				}
				if(v->Norm2 <= Target){
					now = time(NULL);
					printf("Target found: %10llu (%5d sec)\n", v->Norm2, (now - start));
					break;
				}
			}
			else{
				Collisions2++;
			}
		}
		else{
			// Append v to the stack
			Stack[StackLength++] = v;
		}
	}
	
End:
	end = time(NULL);
	printf("------------------------\n");
	
	// Formatting the time taken
	int Time = end - start;
	int Timesec = Time % 60;
	int Timemin = (Time / 60) % 60;
	int Timehr = (Time / 3600) % 24;
	int Timeday = (Time / 86400);
	if(Timeday == 0)
		printf("Time:           %02u:%02u:%02u (hh:mm:ss)\n", Timehr, Timemin, Timesec);
	else
		printf("Time:    (%3ud) %02u:%02u:%02u (hh:mm:ss)\n", Timeday, Timehr, Timemin, Timesec);
	
	// Formatting the main space costs
	double Space = (T * VectorsLength * sizeof(void*)) + (VectorsLength * N * sizeof(Vectors[0].Coord[0]));
	if(Space < 1000)
		printf("Est. space: %12f (bytes)\n", Space);
	else if (Space < 1000000)
		printf("Est. space: %12f (kB)\n", Space / 1000);
	else if (Space < 1000000000)
		printf("Est. space: %12f (MB)\n", Space / 1000000);
	else if (Space < 1000000000000)
		printf("Est. space: %12f (GB)\n", Space / 1000000000);
	else
		printf("Est. space: %12f (TB)\n", Space / 1000000000000);
	
	printf("------------------------\n");
	printf("Iterations:   %10llu\n", Iteration);
	printf("Inner products\n");
	printf("- Comparing:%12llu\n", Comparisons);
	printf("- Hashing: %13llu\n", Hashes);
	printf("- Total:   %13llu\n", (Comparisons + Hashes));
	printf("Reductions v: %10llu\n", Reductions1);
	printf("Reductions w: %10llu\n", Reductions2);
	printf("Vectors:      %10llu\n", VectorsLength);
	printf("List length:  %10llu\n", VectorsLength - Collisions2 - StackLength);
	printf("Stack length: %10llu\n", StackLength);
	printf("Collisions\n");
	printf("- Sampling 0: %10llu\n", Collisions1);
	printf("- Reducing:   %10llu\n", Collisions2);
	printf("- Total:      %10llu\n", Collisions1 + Collisions2);
	printf("Shortest:     %10llu\n\n", MinNorm2);	
	
	// Store results in output file, with data stored according to a certain structure (see below)
	FILE* f = fopen("hashsieve-results.txt", "a");
	if (f == NULL){
    	printf("Error opening file!\n");
    	exit(1);
	}
	fprintf(f, "HashSieve with (N,sd,pr,k,T) = (%u,%u,%u,%u,%u): {%d, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu}\n", 
		N, SEED, PROBE, K, T, (int)(end - start), Iteration, Comparisons, Hashes, Comparisons + Hashes, Reductions1, Reductions2, 
		VectorsLength - Collisions2 - StackLength, StackLength, Collisions1 + Collisions2, MinNorm2);
	fclose(f);
	
	//getchar();
	//goto Start;

}
