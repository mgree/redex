module Untyped where

import Control.Monad
import Data.Maybe
import Test.QuickCheck

data Expr =
    Var Int
  | Lambda Expr
  | App Expr Expr

showExpr :: Int -> Expr -> String
showExpr _b (Var n) = "var" ++ show n
showExpr b (Lambda e) = "lambda. " ++ showExpr (b+1) e
showExpr b (App e1 e2) = "(" ++ showExpr b e1 ++ " " ++ showExpr b e2 ++ ")"

instance Show Expr where
  show e = showExpr 0 e

size :: Expr -> Int
size (Var _) = 1
size (Lambda e) = 1 + size e
size (App e1 e2) = size e1 + size e2

wellLexed :: Expr -> Bool
wellLexed = wellLexedAux 0
  where wellLexedAux :: Int -> Expr -> Bool
        wellLexedAux b (Var n) = 0 <= n && n < b
        wellLexedAux b (Lambda e) = wellLexedAux (b+1) e
        wellLexedAux b (App e1 e2) = wellLexedAux b e1 && wellLexedAux b e2

arbitraryExpr :: Int -> Int -> Gen Expr
arbitraryExpr n 0 = oneof [return $ Lambda $ Var 0] -- base case
arbitraryExpr n max = do
  oneof $ 
    (if n < max 
     then [arbitraryExpr (n+1) (max-1) >>= return . Lambda]
     else []) ++ 
    (if n > 0
     then [choose (0,n-1) >>= return . Var]
     else []) ++
    [do { e1 <- arbitraryExpr n (max `div` 2);
          e2 <- arbitraryExpr n (max `div` 2);
          return $ App e1 e2 }]

instance Arbitrary Expr where
  arbitrary = sized $ \max -> arbitraryExpr 0 max

-- All the terms we generate should be well-lexed
prop_WellLexed e = collect (size e) $ wellLexed e

subst :: Expr -> Int -> Expr -> Expr
subst e n (Var n') 
  | n == n' = e
  | otherwise = (Var n')
subst e n (Lambda e') = Lambda $ subst e (n+1) e'
subst e n (App e1 e2) = App (subst e n e1) (subst e n e2)

shift :: Int -> Expr -> Expr
shift i (Var n) = if n < i then Var n else Var (n-1)
shift i (Lambda e) = Lambda $ shift (i+1) e
shift i (App e1 e2) = App (shift i e1) (shift i e2)

value :: Expr -> Bool
value (Lambda e) = True
value _ = False

-- we can run this with m = Maybe or m = List
step :: MonadPlus m => Expr -> m Expr
step (Var _) = mzero -- unbound variable
step (Lambda e) = mzero -- found a term
step (App e1@(Lambda e11) e2) 
  | value e2 = return $ shift 0 $ subst e2 0 e11
  | otherwise = do
    e2' <- step e2
    return $ App e1 e2'
step (App e1 e2) = do
  e1' <- step e1
  return $ App e1' e2

-- if we can step, we'd better preserve scope
prop_StepWellLexed e = isJust next ==> wellLexed (fromJust next)
  where next = step e
        
-- verify progress
prop_Progress e = (classify isValue "value") $ (classify (not isValue) "step") $ value e || isJust (step e)
  where isValue = value e

-- use the List monad to ensure determinacy
prop_Deterministic e = nextStates > 0 ==> nextStates == 1
  where nextStates = length $ step e