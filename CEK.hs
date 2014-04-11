{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
{-# LANGUAGE TypeSynonymInstances, TemplateHaskell #-}
module CEK where

import Control.Monad
import Data.Maybe
import Data.List (intercalate)
import Test.QuickCheck
import Test.QuickCheck.All

type Name = Int

data Expr =
    Var Name
  | Num Int
  | Plus Expr Expr
  | IfZero Expr Expr Expr
  | Lambda Expr
  | App Expr Expr
  deriving (Show)

newtype Env = Env [Value] 
            deriving (Show)

count :: Env -> Int
count (Env vs) = length vs

boundIn :: Name -> Env -> Bool
boundIn x (Env env) = 0 <= x && x < length env

lookupIn :: Name -> Env -> Value
lookupIn x (Env env) = env !! x

extend :: Value -> Env -> Env
extend v (Env env) = Env (v:env)

data Value = VClo Expr Env | VNum Int
           deriving Show

isClosure :: Value -> Bool
isClosure (VClo _ _) = True
isClosure _ = False

isNum :: Value -> Bool
isNum (VNum _) = True
isNum _ = False

data Frame = 
    AppL Expr Env
  | AppR Expr Env
  | PlusL Expr Env
  | PlusR Int
  | If Expr Expr Env
  deriving Show
    
newtype Cont = Cont [Frame]
               deriving Show

data Code = T Expr | V Value | E String
          deriving Show

data Config = Config Code Env Cont 
            deriving Show

wellLexedExpr :: Int -> Expr -> Bool
wellLexedExpr b (Var n) = 0 <= n && n < b
wellLexedExpr _b (Num _n) = True
wellLexedExpr b (Plus e1 e2) = wellLexedExpr b e1 && wellLexedExpr b e2
wellLexedExpr b (IfZero e1 e2 e3) = 
  wellLexedExpr b e1 && wellLexedExpr b e2 && wellLexedExpr b e3
wellLexedExpr b (Lambda e) = wellLexedExpr (b+1) e
wellLexedExpr b (App e1 e2) = wellLexedExpr b e1 && wellLexedExpr b e2

wellLexedValue :: Value -> Bool
wellLexedValue (VClo code env) = wellLexedExpr (1 + count env) code
wellLexedValue (VNum _n) = True

wellLexedEnv :: Env -> Bool
wellLexedEnv (Env env) = all wellLexedValue env

wellLexedFrame :: Frame -> Bool
wellLexedFrame (AppL e2 env) = wellLexedEnv env && wellLexedExpr (count env) e2
wellLexedFrame (AppR code env) = wellLexedValue (VClo code env)
wellLexedFrame (PlusL e2 env) = wellLexedEnv env &&  wellLexedExpr (count env) e2
wellLexedFrame (PlusR n1) = True
wellLexedFrame (If e2 e3 env) = 
  wellLexedEnv env && wellLexedExpr (count env) e2 && wellLexedExpr (count env) e3

wellLexedCont :: Cont -> Bool
wellLexedCont (Cont fs) = all wellLexedFrame fs

wellLexedCode :: Int -> Code -> Bool
wellLexedCode b (T expr) = wellLexedExpr b expr
wellLexedCode _b (V val) = wellLexedValue val
wellLexedCode _b (E _msg) = True

wellLexed :: Config -> Bool
wellLexed (Config code env cont) = 
  wellLexedCode (count env) code &&
  wellLexedEnv env &&
  wellLexedCont cont

class Sized a where
  size :: a -> Int
  
instance Sized Expr where
  size (Var _) = 1
  size (Num _) = 1
  size (Plus e1 e2) = 1 + size e1 + size e2
  size (IfZero e1 e2 e3) = 1 + size e1 + size e2 + size e3
  size (Lambda e) = 1 + size e
  size (App e1 e2) = 1 + size e1 + size e2

instance Sized Value where
  size (VClo code env) = size code + size env
  size (VNum _n) = 1
  
instance Sized Frame where
  size (AppL e2 env) = 1 + size e2 + size env
  size (AppR code env) = 1 + size code + size env
  size (PlusL e2 env) = 1 + size e2 + size env
  size (PlusR n1) = 1
  size (If e2 e3 env) = 1 + size e2 + size e3 + size env

-- covers Env and Cont
instance Sized a => Sized [a] where
  size xs = sum (map size xs)

instance Sized Env where
  size (Env vs) = size vs
  
instance Sized Cont where
  size (Cont fs) = size fs

instance Sized Code where
  size (T expr) = size expr
  size (V val) = size val
  size (E msg) = 1

instance Sized Config where
  size (Config code env cont) = size code + size env + size cont

arbitraryExpr :: Int -> Int -> Gen Expr
arbitraryExpr n 0 = return $ Lambda $ Var 0 -- base case
arbitraryExpr n maxSize = do
  oneof $ 
    (if n < maxSize 
     then [arbitraryExpr (n+1) (maxSize-1) >>= return . Lambda]
     else []) ++ 
    (if n > 0
     then [choose (0,n-1) >>= return . Var]
     else []) ++
    [do { e1 <- arbitraryExpr n (maxSize `div` 2);
          e2 <- arbitraryExpr n (maxSize `div` 2);
          return $ App e1 e2 }]

arbitraryClosure :: Int -> Gen (Expr,Env)
arbitraryClosure 0 = arbitraryExpr 0 0 >>= return . \code -> (code,Env [])
arbitraryClosure maxSize = do
  bound <- choose (0,2)
  let remaining = (maxSize - 1) `div` (bound `max` 1)
  code <- arbitraryExpr bound remaining
  env <- arbitraryEnv bound remaining
  return $ (code,env)
        
arbitraryValue :: Int -> Gen Value
arbitraryValue maxSize = 
  oneof [arbitraryClosure maxSize >>= return . uncurry VClo,
         choose (-100,100) >>= return . VNum]

arbitraryEnv :: Int -> Int -> Gen Env
arbitraryEnv bound 0 = mapM arbitraryValue [0 | i <- [1..bound]] >>= return . Env
arbitraryEnv bound maxSize = 
  mapM arbitraryValue [(maxSize-1) `div` bound | i <- [1..bound]] >>= return . Env

arbitraryFrame :: Int -> Gen Frame
arbitraryFrame maxSize = 
  oneof [do 
            bound <- choose (0,2)
            let remaining = ((maxSize - 1) `div` (bound `max` 1)) `max` 0
            e2 <- arbitraryExpr bound remaining
            env <- arbitraryEnv bound remaining 
            frame <- elements [AppL, PlusL]
            return $ frame e2 env,
         arbitraryClosure ((maxSize - 1) `max` 0) >>= return . uncurry AppR,
         choose (-100,100) >>= return . PlusR,
         do 
            bound <- choose (0,2)
            let remaining = (maxSize `div` (2 * (bound `max` 1))) `max` 0
            e2 <- arbitraryExpr bound remaining
            e3 <- arbitraryExpr bound remaining
            env <- arbitraryEnv bound remaining 
            return $ If e2 e3 env]

arbitraryCont :: Int -> Gen Cont
arbitraryCont 0 = return $ Cont []
arbitraryCont maxSize = do
  height <- choose (0,4)
  let remaining = (maxSize - 1) `div` (height `max` 1)
  fs <- mapM arbitraryFrame [remaining | i <- [1..height]]
  return $ Cont fs

arbitraryCode :: Int -> Int -> Gen Code
arbitraryCode bound maxSize = 
  frequency [(45,arbitraryExpr bound maxSize >>= return . T),
             (45,arbitraryValue maxSize >>= return . V),
             (10,return $ E "generated")]

instance Arbitrary Config where
  arbitrary = sized $ \maxSize -> do
    bound <- choose (0,2)
    code <- arbitraryCode bound $ maxSize `div` 2
    let remaining = (maxSize `div` (bound `max` 1)) `div` 4 -- split between env and cont
    env <- arbitraryEnv bound remaining
    cont <- arbitraryCont remaining
    return $ Config code env cont
    
-- All the terms we generate should be well-lexed
prop_WellLexed e = collect (size e) $ wellLexed e

tConfig expr env cont = Config (T expr) env cont
vConfig val  env cont = Config (V val) env cont
eConfig msg  env cont = Config (E msg) env cont

step :: MonadPlus m => Config -> m Config
step (Config (T (Var x)) env cont) = do
  guard $ x `boundIn` env
  return $ vConfig (lookupIn x env) env cont
step (Config (T (Num n)) env cont) =
  return $ vConfig (VNum n) env cont
step (Config (T (Plus e1 e2)) env (Cont fs)) =
  return $ tConfig e1 env (Cont (PlusL e2 env : fs))
step (Config (T (IfZero e1 e2 e3)) env (Cont fs)) =
  return $ tConfig e1 env (Cont (If e2 e3 env : fs))
step (Config (T (Lambda e)) env cont) = 
  return $ vConfig (VClo e env) env cont
step (Config (T (App e1 e2)) env (Cont fs)) =
  return $ tConfig e1 env (Cont (AppL e2 env : fs))
-- AppL reduce
step (Config (V (VClo code env)) _envOld (Cont (AppL e2 env' : fs))) =
  return $ tConfig e2 env' (Cont (AppR code env : fs))
step (Config (V _v) env cont@(Cont (AppL e2 env' : fs))) =
  return $ eConfig "expected closure" env cont
-- PlusL reduce
step (Config (V (VNum n1)) env (Cont (PlusL e2 env' : fs))) = 
  return $ tConfig e2 env' (Cont (PlusR n1 : fs))
step (Config (V _v) env cont@(Cont (PlusL e2 env' : fs))) = 
  return $ eConfig "expected number" env cont
-- AppR reduce
step (Config (V v2) _env' (Cont (AppR code env : fs))) =
  return $ tConfig code (extend v2 env) (Cont fs)
-- PlusR reduce
step (Config (V (VNum n2)) env (Cont (PlusR n1:fs))) =
  return $ vConfig (VNum $ n1 + n2) env (Cont fs)
step (Config (V _v2) env cont@(Cont (PlusR n1:fs))) =
  return $ eConfig "expected number" env cont
-- If reduce
step (Config (V (VNum n)) _env' (Cont (If e2 e3 env:fs))) =
  return $ tConfig (if (n == 0) then e2 else e3) env (Cont fs)
step (Config (V _v) _env' cont@(Cont (If e2 e3 env:fs))) =
  return $ eConfig "expected number" env (Cont fs)
-- return and error cases
step (Config (V v) _env (Cont [])) = mzero
step (Config (E e) _env _cont) = mzero

isValue :: Config -> Bool
isValue (Config (V _) _env (Cont [])) = True
isValue _ = False

isError :: Config -> Bool
isError (Config (E _) _env _cont) = True
isError _ = False

isNormalForm cfg = isValue cfg || isError cfg

prop_StepWellLexed cfg = isJust next ==> wellLexed (fromJust next)
  where next = step cfg

prop_Progress cfg = 
  classify (isError cfg) "error" $ 
  classify (isValue cfg) "value" $
  classify (not nf) "step" $ 
  nf || isJust (step cfg)
  where nf = isNormalForm cfg

prop_Deterministic cfg = nextStates > 0 ==> nextStates == 1
  where nextStates = length $ step cfg

steps :: Int -> Config -> [Config]
steps 0 cfg = [cfg]
steps n cfg = case step cfg of
  Just cfg' -> cfg:((n-1) `steps` cfg')
  Nothing -> [cfg]

prop_ManySteps cfg = label (show $ length cfgs) $ 
                     all wellLexed cfgs
  where cfgs= 100 `steps` cfg

runTests = $quickCheckAll