module Main

%default total

-- A tiny expression language:

data Expr
  = IntExpr Nat
  | AddExpr Expr Expr

-- Semantics of expression language:

eval : Expr -> Nat
eval (IntExpr k)    = k
eval (AddExpr x y)  = (eval x) + (eval y)

-- Smoke tests:

eval_test_1 : eval (IntExpr 5) = 5
eval_test_1 = Refl

eval_test_2 : eval (AddExpr (IntExpr 1) (IntExpr 2)) = 3
eval_test_2 = Refl

-- A tiny assembler language:

data ASM
  = Add
  | Push Nat

Stack : Type
Stack = List Nat

-- run a sequence of ASM instructions given (maybe) a stack.
-- Returns either Just a stack (with the result on top) or Nothing (runtime error)

run : (code : List ASM) -> (stack : Maybe Stack) -> Maybe Stack
run _               Nothing                 = Nothing
run []              stack                   = stack
run (Add :: is)     (Just $ x :: y :: ss)   = run is (Just $ (x + y) :: ss)
run (Push k :: is)  (Just stack)            = run is (Just $ k :: stack)
run _               _                       = Nothing

-- Smoke tests:

run_test_add : (a,b : Nat) -> (is : List ASM) -> (stack : List Nat) -> run (Add :: is) (Just $ a :: b :: stack) = run is (Just $ (a + b) :: stack)
run_test_add a b is stack = Refl

run_test_push : (n : Nat) -> (is : List ASM) -> (stack : List Nat) -> run (Push n :: is) (Just stack) = run is (Just $ (n :: stack))
run_test_push n is stack = Refl

-- Proof that running nothing on any stack simply returns the stack:

run_prf_0 : (stack : Maybe Stack) -> run [] stack = stack
run_prf_0   Nothing     = Refl
run_prf_0   (Just x)    = Refl

-- Proof that running a list of instructions (x :: ys) is the same as first running x and then running ys:

run_prf_1 : (x : ASM) -> (ys : List ASM) -> (stack : Maybe Stack) -> run (x :: ys) stack = run ys (run [x] stack)
run_prf_1 x         []          stack                   = rewrite run_prf_0 (run [x] stack) in Refl
run_prf_1 x         (y :: ys)   Nothing                 = Refl
run_prf_1 Add       (y :: ys)   (Just [])               = Refl
run_prf_1 Add       (y :: ys)   (Just (x :: []))        = Refl
run_prf_1 Add       (y :: ys)   (Just (x :: (z :: xs))) = Refl
run_prf_1 (Push k)  (y :: ys)   (Just z)                = Refl

-- Proof that running a list of instructions (xs + ys) is the same as first running part of the list (xs) and then the rest of the list (ys):

run_prf_2 : (xs,ys : List ASM) -> (stack : Maybe Stack) -> run (xs ++ ys) stack = run ys (run xs stack)
run_prf_2 [] ys stack =
    rewrite run_prf_0 stack in
    Refl
run_prf_2 xs [] stack =
    rewrite appendNilRightNeutral xs in
    rewrite run_prf_0 (run xs stack) in
    Refl
run_prf_2 (x :: xs) (y :: ys) stack =
    rewrite run_prf_1 x xs stack in
    rewrite run_prf_1 y ys (run xs (run [x] stack)) in
    rewrite run_prf_1 x (xs ++ y :: ys) stack in
    rewrite run_prf_2 xs (y :: ys) (run [x] stack) in
    rewrite run_prf_1 y ys (run xs (run [x] stack)) in
    Refl

-- A compiler that compiles the tiny expression language to the tiny machine code language:

compile : Expr -> List ASM
compile (IntExpr k)   = [Push k]
compile (AddExpr x y) = compile x ++ compile y ++ [Add]

-- Smoke tests:

compile_test_1 : compile (AddExpr (IntExpr 1) (IntExpr 2)) = [Push 1,Push 2,Add]
compile_test_1 = Refl

compile_test_2 : compile (AddExpr (IntExpr 1) (AddExpr (IntExpr 2) (IntExpr 3))) = [Push 1,Push 2,Push 3,Add,Add]
compile_test_2 = Refl

-- Proof that:
-- 1. The compiler correctly compiles expr to stack machine
-- 2. Given a valid stack, the compiled code will always return a result (no runtime errors)
-- 3. The given stack will be "left alone" (resulting value is pushed on top of given stack)

compiler_is_correct : (e : Expr) -> (stack : Stack) -> run (compile e) (Just stack) = Just (eval e :: stack)
compiler_is_correct (IntExpr k)     stack = Refl
compiler_is_correct (AddExpr x y)   stack =
    rewrite run_prf_2 (compile x) (compile y ++ [Add]) (Just stack) in
    rewrite compiler_is_correct x stack in
    rewrite run_prf_2 (compile y) [Add] (Just (eval x :: stack)) in
    rewrite compiler_is_correct y (eval x :: stack) in
    rewrite plusCommutative (eval y) (eval x) in
    Refl
