{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

module Lambda where

import Data.List
import Data.Ord
import qualified Data.Map as Map
import Data.Copointed


----------------------------------------------------- SIMPLE TYPES


data Type = Atomic String | Type :->: Type 
     deriving (Eq,Ord)

instance Show Type where
  show (Atomic a) = a
  show (a :->: b) = "(" ++ show a ++ "->" ++ show b ++ ")"


atomicTypes1 = map Atomic (["a","b","c","d","e"] ++ [ x : show i | i <- [2,4..], x <- "abcde" ])
atomicTypes2 = map Atomic ([ x : show i | i <- [1,3..], x <- "abcde" ])


occurs :: String -> Type -> Bool
occurs x (Atomic y) = x == y
occurs x (a :->: b) = occurs x a || occurs x b


----------------------------------------------------- TERMS


data Term a = Var Int a | Abs (Term a) a | App (Term a) (Term a) a
     deriving (Eq,Ord)

instance Show (Term ()) where
  show (Var i _) = show i
  show (Abs t _)  = "\\." ++ show t
  show (App s t _) = "(" ++ show s ++ ")" ++ show t

instance Show (Term String) where
  show (Var i x) = x
  show (Abs t x)  = "\\" ++ x ++ "." ++ show t
  show (App s t _) = "(" ++ show s ++ ")" ++ show t

instance Functor Term where
  fmap f (Var i a)   = Var i (f a)
  fmap f (Abs t a)   = Abs (fmap f t) (f a)
  fmap f (App s t a) = App (fmap f s) (fmap f t) (f a)

instance Copointed Term where
  copoint (Var _ x)   = x
  copoint (Abs _ x)   = x
  copoint (App _ _ x) = x


----------------------------------------------------- NAMED TERMS

namesBound = ["x","y","z"] ++ [ v : show i | i <- [1..], v <- "xyz"]
namesFree  = ["a","b","c"] ++ [ v : show i | i <- [1..], v <- "abc"]

named :: Term a -> Term String
named t = fst $ f namesBound namesFree t where
  f    xs  vs (Var i _)   = (Var i (vs !! i),xs)
  f (x:xs) vs (Abs t _)   = let (s,ys) = f xs (x:vs) t in (Abs s x,ys) 
  f    xs  vs (App s t _) = let (w,ys) = f xs vs s; (u,zs) = f ys vs t in (App w u "", zs)

fromNamed :: Term String -> Term String
fromNamed = fst . f [] where
  f xs (Var _ x)   | Just i <- indexOf x xs = (Var i x,xs)
                   | otherwise              = (Var (length xs) x, xs ++ [x])
  f xs (Abs t x)   | (s,ys) <- f (x:xs) t   = (Abs s x,tail ys)
  f xs (App s t _) | (u,ys) <- f xs s,
                     (v,zs) <- f ys t       = (App u v "",zs) 

namedSubstitution :: String -> Term String -> Term String -> Term String
namedSubstitution x t = f where
  f v@(Var i y) = if x == y then t else v
  f   (Abs t y) = Abs (f t) y
  f (App s t y) = App (f s) (f t) y

----------------------------------------------------- UNTYPED TERMS


type UntypedTerm = Term ()

var i   = Var i ()
lam t   = Abs t ()
app s t = App s t ()


----------------------------------------------------- TYPED TERMS


type TypedTerm = Term Type

typeOf :: TypedTerm -> Type
typeOf = copoint

typeCheck :: TypedTerm -> Bool
typeCheck t = f [] (typeOf t) t where
  f as c (Var i b)            = case as `at` i of Just a -> a == b && b == c; _ -> False
  f as c (Abs s d@(a :->: b)) = c == d && f (a:as) b s
  f as c (App u v b)          = let a = typeOf v in b == c && f as (a :->: b) u && f as a v


----------------------------------------------------- TYPE ASSIGNMENT


typed :: Term a -> Maybe TypedTerm
typed t = f atomicTypes2 atomicTypes1 Map.empty t >>= ( \(t',_,m) -> return $ fmap (applySubstitution m) t' ) 
  where
    f as    xs  m (Var i _)    = Just (Var i (as !! i), xs, m)
    f as (x:xs) m (Abs t _)    | Just (t',ys,n) <- f (x:as) xs m t = Just (Abs t' (x :->: typeOf t'), ys, n)
                               | otherwise = Nothing
    f as (x:xs) m (App s t _)  | Just (s',xs1,m1) <- f as xs  m  s,
                                 Just (t',xs2,m2) <- f as xs1 m1 t,
                                 Just m3 <- updateMap (initialList (typeOf s') (typeOf t' :->: x) ) m2
                                  = Just (App s' t' x,xs2,m3)
                               | otherwise = Nothing


----------------------------------------------------- UNIFICATION MAPS


initialList :: Type -> Type -> [(String,Type)]
initialList  a b = f a b [] where
  f (Atomic x) b xs = (x,b):xs
  f a (Atomic y) xs = (y,a):xs
  f (a :->: b) (c :->: d) xs = f a c (f b d xs)


updateMap :: [(String,Type)] -> Map.Map String Type -> Maybe (Map.Map String Type)
updateMap        []  m = Just m
updateMap ((x,a):xs) m | Atomic y <- a, x == y = updateMap xs m
                       | Just b <- Map.lookup x m = updateMap (xs ++ initialList a b) m
                       | otherwise = let a1 = applySubstitution m a
                                         m1 = Map.map ( applySubstitution $ Map.singleton x a1 ) m
                                         m2 = Map.insert x a1 m1
                                     in if any (uncurry occurs) (Map.toList m2) then Nothing else updateMap xs m2


applySubstitution :: Map.Map String Type -> Type -> Type
applySubstitution m (Atomic x) = case Map.lookup x m of Just a -> a; _ -> Atomic x
applySubstitution m (a :->: b) = applySubstitution m a :->: applySubstitution m b


----------------------------------------------------- BETA REDUCTION


update :: Int -> Term a -> Term a
update i = f 0 where
  f j t | Var k x   <- t = if k < j then Var k x else Var (k + i) x
        | Abs s x   <- t = Abs (f (j+1) s) x
        | App u v x <- t = App (f j u) (f j v) x


substitute :: Term a -> Term a -> Term a
substitute s = f 0 where
  f i (Var j x)   | j == i = update i s
                  | j >  i = Var (j-1) x
                  | j <  i = Var j x
  f i (Abs s x)   = Abs (f (i+1) s) x
  f i (App u v x) = App (f i u) (f i v) x


beta :: Term a -> [Term a]
beta t
  | Var i _   <- t = []
  | Abs s x   <- t = [Abs s' x | s' <- beta s]
  | App u v x <- t = (case u of Abs s _ -> [substitute v s]; _ -> []) 
                      ++ [App u' v x | u' <- beta u]
                      ++ [App u v' x | v' <- beta v]


normalise :: Term a -> Term a
normalise t = case beta t of (x:_) -> normalise x; _ -> t


----------------------------------------------------- SAMPLES


instance Num (Term ()) where
  x + y = lam $ lam $ app (app x (var 1)) (app (app y (var 1)) (var 0))
  x * y = lam $ app x (app y (var 0))
  x - y = app (app y $ lam (app prec $ var 0)) x

  fromInteger n = lam $ lam $ foldr ($) (var 0) (replicate (fromInteger n) (app (var 1)))
  abs           = id
  signum _      = 1

prec = lam $ lam $ lam $ app (app (app (var 2) $ lam $ lam $ app (var 0) $ app (var 1) (var 3)) (lam $ var 1)) (lam $ var 0)

omega = let w = lam $ app (var 0) (var 0) in app w w

fix   = lam $ app (lam $ app (var 1) $ app (var 0) (var 0)) (lam $ app (var 1) $ app (var 0) (var 0))

i     = lam $ var 0
k     = lam $ lam $ var 0
s     = lam $ lam $ lam $ app (app (var 2) (var 0)) $ app (var 1) $ var 0

----------------------------------------------------- UTILS


at :: [a] -> Int -> Maybe a
at xs i = if i < 0 then Nothing else f xs i where
  f [] _ = Nothing
  f (x:xs) 0 = Just x
  f (_:xs) i = f xs (i-1)

indexOf :: Eq a => a -> [a] -> Maybe Int
indexOf y = f 0 where
  f _ [] = Nothing
  f i (x:xs) = if x == y then Just i else f (i+1) xs