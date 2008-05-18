(********************************************)
(*           SODOKU GENERATOR               *)
(* Sodoku generator using genetic algorithms*)
(* Christian Theil Have <cth@itu.dk>, 2006  *)
(********************************************)
load "Int";
load "Math";
load "Random";

(***************************************************)
(***************** misc utility functions **********)

fun id x = x;

fun upto (min,max) = if min < max then min::upto(min+1,max) else [min];
infix 0 upto;

exception HasNoRoot
fun sqrt n =
  let fun tryroot(x,n) = 
	if x < 0 orelse x*x > n then raise HasNoRoot
	else if x*x = n then x 
	     else tryroot (x+1,n) 
  in 
	tryroot(0,n)
  end;

val randgen = Random.newgenseed(42.0);
fun rand (size) = Random.range (0,size) randgen;

(* print a line to stdout *)
fun puts s = 
	TextIO.output(TextIO.stdOut, (s ^ "\n")); 
	TextIO.flushOut(TextIO.stdOut);

(*********************************************************)
(*************** list functions **************************)
fun member(_,[]) = false 
  | member(x, y::ys) = if x=y then true else member(x,ys);
infix 0 member

fun remove(_,[]) = []
  | remove(x, y::ys) = if x=y then remove(x,ys) 
                       else y::remove(x,ys);

fun remove_first(_,[]) = []
  | remove_first(x, y::ys) = 
	if x=y then ys else y::remove_first(x,ys);

fun reverse([]) = []
  | reverse(x::xs) = reverse(xs) @ [ x ]

(* Merge sort:
 * vfunc can be used to change the ordering of elements
 * us id function for normal ordering (see sort function below) *)
fun msort(vfunc, l) = 
  if l = [] then []
  else if length(l) = 1 then l
  else
  let val l1 = List.take(l, length(l) div 2)
      val l2 = List.drop(l, length(l) div 2)
      fun merge ([],[]) = []
        | merge (x::xs, []) = x::merge(xs, [])
        | merge ([], y::ys) = merge(y::ys,[]) 
        | merge (x::xs, y::ys) =
	  if vfunc(x) < vfunc(y) then x::merge(xs,y::ys)
	  else y::merge(x::xs,ys)
  in 
      merge(msort(vfunc,l1),msort(vfunc,l2))
  end;

fun sort l = msort(id,l);

(* I know this is not a very good way to randomize a list.
 * doing it a number of times will improve distribution *)
fun randomize_list ([]) = []
  | randomize_list (x::xs) = 
    if rand(2) = 0 then x :: randomize_list(xs)
    else randomize_list(xs) @ [x]

exception OutOfBounds
fun nth (i,[]) = raise OutOfBounds
  | nth (i, x::xs) = if i = 1 then x else nth(i-1, xs) 

fun replace_nth(i,a,[]) = [] 
  | replace_nth(i,a,x::xs) = 
    if i = 1 then 
       a::replace_nth(i-1,a,xs)
    else
       x::replace_nth(i-1,a,xs); 

fun remove_nth(i,[]) = []
  | remove_nth(i,x::xs) =
    if i = 1 then remove_nth(i-1,xs)
    else x::remove_nth(i-1,xs)

(* swap elements at idx x and y int the list l *)
fun swap(l,x,y) =
   let val xth = nth(x,l) 
       val yth = nth(y,l)
   in
       replace_nth(y,xth,replace_nth(x,yth,l))
   end

fun remove_dupes [] = []
  | remove_dupes(x::xs) =
    if (x member xs) then xs else x::remove_dupes(xs)
    
      
(********************************************************)
(* Sodoku board representation                          *)
(* The sodoku board is represented as a list            *)
(* The functions below are used for creating and        *)
(* accessing the board.                                 *)
(********************************************************)

(* makes an totally empty sodoku board *)
fun mk_empty_board size = 
  let fun mkl 0 = [] | mkl s = 0::mkl(s-1)
  in mkl(size*size) end;

(* check if a board is empty *)
fun is_empty [] = true | is_empty (x::xs) =
  if x <> 0 then false else is_empty(xs); 

(* makes a full board, note that it is initially sorted *)
fun mk_full_board size =
  let fun mkl 0 = [] | mkl s = (s mod size)+1::mkl(s-1)
  in mkl(size*size) end;


(* uses randomize_list to randomize  the elements
 * in the board. It's done enough times to make the order
 * appear totally random *)
fun randomize_board(board) = 
  let   in 
    let fun many_times(x,board) = 
      if x = 0 then board
      else many_times(x-1,randomize_list(board)) 
    in
          many_times(length(board), board)
    end
  end

(* makes a random board *)
fun mk_board size = randomize_board(mk_full_board size)
  
(* removes numbers that are allready filled into
 * the board from the available list *)
fun remove_non_empty (avail, []) = avail  
  | remove_non_empty (avail, x::xs) =
    if x = 0 then
       remove_non_empty(avail, xs)
    else
       remove_non_empty(remove_first(x,avail), xs)

(* fill empty fields in an unfinished board *)
exception FillBoardMismatch
fun fill_board ([], []) = [] 
  | fill_board ([], _) = raise FillBoardMismatch 
  | fill_board (_, []) = raise FillBoardMismatch 
  | fill_board (x::xs, b::board) = 
    if b = 0 then (* if the field is empty *)
      x::fill_board(xs, board)
    else
      b::fill_board(x::xs, board);

(* creates a list corresponding to the nth row in
 * the sodoku board *)
fun nth_row(n,board) =
  let val offset = sqrt(length(board)) * (n-1)
      val rowsize = sqrt(length(board))
      fun extract [] = []
        | extract (x::xs) = List.nth(board,x)::extract(xs)
  in 
    extract(offset upto (offset+rowsize-1))
  end

(* creates a list corresponding to the nth column in
 * the sodoku board *)
fun nth_col(n,board) =
  let val colsize = sqrt(length(board)) 
      fun extract(board,x,n) = 
        if x = 0 then []
        else extract(board,x-1,n) @ [ List.nth(board,(n-1)+((x-1)*colsize)) ]
  in
    extract(board, colsize, n) 
  end

(* creates a list corresponding to the nth quadrant in
 * the sodoku board *)
fun nth_quadrant(n,board) = 
let val quadrants = sqrt(length(board))
    val quadsize  = sqrt(sqrt(length(board)))
    fun whatrows(q,r,rc) =
      if (q>(rc*r)) andalso (q<=(rc*(r+1))) then (r*rc+1,(r+1)*rc)
      else whatrows(q,r+1,rc)
in
    let val (from,to) = whatrows(n,0,quadsize) 
        fun getrows(a,b,board) = 
          if a < b then nth_row(a,board)::getrows(a+1,b,board) 
	  else [ nth_row(a,board) ];
        fun getcol([], _) = [] | getcol(x::rows, col) =
          List.take(List.drop(x,quadsize*col),quadsize) @ getcol(rows, col)
    in 
      getcol(getrows(from,to,board),(n-1) mod quadsize) 
    end
end;

(* Convert board to a string suitable for printing *)
fun board_toString (board) = 
  let
    fun row_to_s [] = "\n" | row_to_s (x::xs) = x ^ " " ^ row_to_s(xs)
    fun board_to_rows([], _) = ""
      | board_to_rows (xs, rowsize) =
        row_to_s(List.take(xs,rowsize)) ^ board_to_rows(List.drop(xs,rowsize),rowsize)
  in
    board_to_rows(map Int.toString board, sqrt(length(board))) 
  end

(************************************************************)
(* Utility and solution checking                            *)
(************************************************************)

(* checks if a line (either row or column or quadrant)
   contains  the correct set of of numbers *) 
fun checkline l = 
  let fun check (l,[]) = true
        | check (l,x::xs) = 
	    (x member l) andalso check(l,xs)
  in
      check(l, 1 upto length l) 
  end

(* like checkline above except it returns a number indicating
 * the number of correct numbers in a line *)
fun checkline_count l = 
  let fun check (l,[]) = 0 
        | check (l,x::xs) = 
	    if (x member l) then 1 + check(l,xs)
            else 0 + check(l,xs)
  in
      check(l, 1 upto length l) 
  end


(* This utitility function checks the fitness of a solution.
 * It's the sum of correct rows + sum of correct columns + 
 * sum of correct quadrants
 *) 
fun utility1 board = 
  let fun cf(f,0) = 0 
        | cf(f,n) = 
	  if checkline(f(n,board)) then 1+cf(f,n-1) else 0+cf(f,n-1) 
      val i = sqrt(length(board))
  in
    (cf(nth_row,i))+(cf(nth_col,i))+(cf(nth_quadrant,i)) 
  end;

(* This utility function is similar to the one above except
 * that it returns the sum of correct numbers in each 
 * row/column/quadrant *)
fun utility2 board = 
  let fun cf(f,0) = 0 
        | cf(f,n) = checkline_count(f(n,board))+cf(f,n-1) 
      val i = sqrt(length(board))
  in
    (cf(nth_row,i))+(cf(nth_col,i))+(cf(nth_quadrant,i)) 
  end;

fun utility board = utility2 board

(* Checks if a board is a solution or not *)
fun is_solution1 board = (3 * sqrt(length board) = utility1 board);
fun is_solution2 board = (utility2(board) = 3*(length board))

fun is_solution board = is_solution2 board

(* sort a list (of boards) by the relative utility *)
fun utility_sort(l) = msort(utility, l); 

(* given a list of boards, return a list of those that are solved *)
fun check_solutions [] = []
  | check_solutions(x::generation) =
	if is_solution x then x::check_solutions(generation)
	else check_solutions(generation);

(* A simple backtracking sodoku solver *)
(*
fun solver (x::xs, size) 
    let fun try_solve 0 = false 
      | fun try_solve n = 
	if solver(n::xs, size) then true else try_solve(n-1)
    if x = 0 then
	try_solve(size)
    else
*)

(* replaces all numbers that doesn't contribute to fitness
 * with 0
 *)
(*
fun scrub_board board =
  let fun scrub (x::xs) = 
        if utility(0::xs) < utility(x::xs) then 0::scrub(xs)
        else x::scrub(xs)
*)
   

fun print_solutions [] = "" 
  | print_solutions (x::xs) = 
  "\nFound a solution: \n" ^ board_toString(x) ^ print_solutions(xs)

(* Creates an initalial generationæ
 * The generation is initialized randomly *)
fun mk_generation1(0, _) = []
  | mk_generation1(size, boardsize) =
     mk_board boardsize::mk_generation1(size-1,boardsize);

(************************************************************)
(* Mutation and crossover                                   *)
(************************************************************)

(*
 * A "clever" mutation function. I do know if this is cheating though.
 * Problem is: It might still optimize for local minima's:
 * Eg. It might be necesary to do several mutations in order to 
 * get higher utility...
 * 
 * Possible optimizations: 
 *  - If a mutation doesn't lead to a higher utility, do it anyway
 *    with a certain probability...
 *  - Mutual recursion thing.. might work..
 *
 *)
fun cmutate (range,count) board = 
    let val first = List.take(board, length(board)-count)
	val rest = List.drop(board, length(board)-count)
    in 
	let fun try (board, i) = 
	    if i = 0 then
		List.nth(board,count-1)
	    else
		if (utility(first @ [i] @ List.drop(rest,1)) > utility(board)) then
		    i
		else
		    try (board,i-1)
	in
	(*
	 puts("iteration" ^ Int.toString(count));
	 puts("test" ^ Int.toString(length(rest)));
	 *)
	    
	    if length(rest) = 0 then
		board
	    else
		cmutate (range,count-1) (first @ [ try(board,range) ] @ List.drop(rest,1))
	end
    end

fun cswap (_,0) board = board
  | cswap (0,b) board = cswap(length(board), b-1) board
  | cswap (a,b) board = 
    let val newboard = swap(board,a,b)
    in
	if (utility(newboard) > utility(board)) then cswap (a-1,b) newboard
	else cswap(a-1,b) board
    end
	

(* disregards range, but I want to look similar to other 
 * mutation function generators *)
(*
fun cmutate_func rate range = fn [] => [] | (x::xs) => 
    cmutate(x, sqrt(length(x)), range)::cmutate_func rate range (xs)
*)


(* Create a function that can be used to mutate a list
 * (used to perform mutations of the sodoku board)  
 * rate is to interpreted as: mutate 1 out of rate individuals.
 *)
fun random_mutator_func rate range = fn [] => [] | (x::xs) =>
  if rand(rate) = 0 then (rand(range)+1)::random_mutator_func rate range (xs)
  else x::random_mutator_func rate range (xs)

(* Create a function that can be used to mutate a list.
 * Mutates the list by swapping existing numbers  *)
(*
fun swap_mutator_func rate range = fn [] => [] | (l) =>
  if (rand(rate) = 0) then swap(l,rand(range)+1,rand(range)+1) else l
*)
fun swap_mutator_func _ range l =
    let val a = rand(range)+1
	val b = rand(range)+1
    in
	swap(l,a,b)
    end


fun testit (board,c) = 
    if c = 0 then (puts("Testing; " ^ Int.toString(utility(board))); 0)
    else (puts("Testing; " ^ Int.toString(utility(board))); testit(cmutate(4,16) (board), c-1))
    
(* given two boards, randomly select which numbers from
 * each the go into the combined board *)
fun random_crossover([],_) = [] 
  | random_crossover(_,[]) = []
  | random_crossover(x::xs,y::ys) = 
    if rand(2) = 1 then x::random_crossover(xs,ys)
    else y::random_crossover(xs,ys)

(* Produce "count" combinations of  boards in list l RcleRR
 * choosen randomly *)
fun crossover (l,count) = 
  let val a = nth(rand(length(l))+1,l)
      val b = nth(rand(length(l))+1,l)
  in 
      if count = 0 then []
      else random_crossover(a,b)::crossover(l,count-1)
  end

fun breed(g) = crossover(g,length(g))

(*********************************************)
(* Selection functions                       *)
(*********************************************)

fun elite(g, count) =
  List.take(reverse(utility_sort(g)),count)

fun rselect(g, 0) = []
  | rselect(g, count) =
  let val s = rand(length(g))
  in
    List.nth(g, s)::rselect(remove_nth(s+1,g), count-1)
  end

fun combined_select(g,count) =
    reverse(utility_sort(elite(g, count div 2) @ rselect(g, count div 2)))
    

(*
fun select() =
    elite(rselect(breed(generation @ mutated(mutator_func,generation)) @ 
		  mutated(mutator_func,generation) @ generation, length(generation)*2), 
	  length(generation))
*)

(********************************************)
(* Some helper functions                    *)
(********************************************)


fun utility_count ([]) = 0
  | utility_count (x::xs) = utility(x)+utility_count(xs)

fun pall [] = (puts ("\n"))
  | pall (x::xs) = (puts(board_toString(x)); pall(xs))

fun putil [] = puts "\n"
  | putil (x::xs) = 
	(puts (Int.toString(utility(x)) ^ " " ); putil(xs))

fun pgeneration(g,i) = 
    ( puts ("Evolving generation " ^ Int.toString i); 
    puts (Int.toString i ^ " " ^ Int.toString(utility_count(g)) 
	  ^ " " ^ Int.toString(utility(hd(g))));
    puts ("Total utility; " ^ Int.toString(utility_count(g)));
    puts ("Utility: " ^ Int.toString(utility(hd(g))));
    puts ("Best board\n" ^ board_toString(hd(g))))

(****************************************************************)
(* The main evolution code                                      *)
(****************************************************************)

 (* This functions evolves the generation with an asexual approach
  * only mutation ever changes the genomes 
  * g: generation of sodoku boards
  * mf: mutation function
  * sf: selection_function
  * i: generation number
  *)
exception FoundSolution of int list list;
fun evolve(g,cf,mf,sf,i) = 
    let val solutions = check_solutions(g)
	val candidates = g @ map mf g
    in
	pgeneration(g,i);
	if (length(solutions) > 0) then raise FoundSolution (solutions)
	else evolve(sf(candidates,length(g)),cf,mf,sf,i+1)
    (* else evolve(sf(remove_dupes(candidates),length(g)),cf,mf,sf,i+1) *)
    end

(* Test function *)
fun test (sodoku_size, generation_size, mutation_rate) =
    let val gen1 = mk_generation1(generation_size,sodoku_size)
	(* val mutator = random_mutator_func mutation_rate (sodoku_size*sodoku_size) *)
	(* val mutator = swap_mutator_func mutation_rate (sodoku_size*sodoku_size) *)
	(* val mutator = cmutate (sodoku_size, sodoku_size*sodoku_size) *)
	val mutator = cswap ((sodoku_size*sodoku_size),(sodoku_size*sodoku_size))
    in
	evolve(gen1,breed,mutator,elite,0)
	handle FoundSolution (s) => puts (print_solutions(s))
    end



