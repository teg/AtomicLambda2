


-- Atomic Lambda Reduction
--------------------------


import Data.Char
import Data.List hiding (union)
import Data.Maybe
import Data.Monoid
import qualified Data.Set as Set
import qualified Data.Map as Map
import Control.Applicative
import Control.Arrow
import Control.Monad

import qualified Lambda as L


names = [ x : '_' : show n | n <- [1..], x <- "xyz" ]


---------------- PRE-TERMS

data Term    = V String
             | L String Term 
             | K String Term 
             | A Term Term
             | C Term Closure 
             | X [String]
             deriving Eq

data Closure = S [String] Term 
             | D  String DTerm
             deriving Eq 

data DTerm   = M Distributor 
             | N DTerm Closure 
             deriving Eq


instance Show Term where
  show = f where
    f (V v)   = v
    f (L v t) = "\\" ++ v ++ "." ++ show t
    f (K v t) =  "+" ++ v ++ "." ++ show t
    f (A t u) =  "(" ++ show t ++ ")" ++ show u
    f (C t s) = show t ++ show s
    f (X xs)  = "{" ++ intercalate "," xs ++ "}" 

instance Show Closure where
  show (S vs t)   = "[" ++ intercalate "," vs ++ " <- " ++ show t ++ "]"
  show (D v d)    = "[" ++ v ++ ". " ++ show d ++ "]"

instance Show DTerm where
  show (M d)   = showDistributor d
  show (N d c) = show d ++ show c


---------------- DISTRIBUTOR


type Distributor = Relation String String

distributorToList :: Distributor -> [(String,[String])]
distributorToList = map (id *** Set.toList) . Map.toList

showDistributor :: Distributor -> String
showDistributor d = "<" ++ intercalate "|" [ show x ++ ". " ++ intercalate "," ys | (x,ys) <- distributorToList d ] ++ ">"


---------------- LAMBDA

fromLambda :: L.Term a -> Term
fromLambda = _1of3 . f names [] where
  f (x:xs) yss (L.Var i _)   = (V x, xs, atIndex i (x:) yss) 
  f (x:xs) yss (L.Abs t _)   = let (t',xs',zs:zss) = f xs ([]:yss) t in case zs of [z] -> (L x t',xs',zss); _ -> (L x $ C t' $ S zs $ V x, xs',zss)
  f    xs  yss (L.App t u _) = let (t',ys,zss) = f xs yss t; (u',zs,wss) = f ys zss u in (A t' u', zs,wss) 

toLambda :: Term -> L.Term String
toLambda = L.fromNamed . f where
  f (V v)    = L.Var (-1) v 
  f (L v t)  = L.Abs (f t) v
  f (K v t)  = L.Abs (f t) v
  f (A t u)  = L.App (f t) (f u) ""
  f (C t c)  = g c (f t)
  f (X xs)   = error "toLambda: hole in atomic term"

  g (S xs t) = substitute x
    | D v d <- c0 = 

    | M d   <- d0 = 
    | N d c <- d0 = 


---------------- SCOPE


type Names = Set.Set String

type Scoping = Relation String String




single x = Map.singleton x (Set.empty)
singles xs = Map.fromList (zip xs $ repeat Set.empty)

extend :: String -> Scoping -> Scoping
extend x r = Map.map (Set.insert x) r




---------------- TERMS

type Errors = [String]

e_variableOverlap :: Names -> Names -> Errors
e_variableOverlap vs1 vs2 = [ v ++ " occurs double" | v <- Set.toList (Set.intersection vs1 vs2) ]

e_applySharing :: Scoping -> Scoping -> Errors
e_applySharing fs cs = [ v ++ " remains co-free in a sharing" | (v,_) <- Map.toList (Map.difference cs fs) ] ++
                       [ v ++ " outwith m-scope(s) " ++ intercalate "," (Set.toList vs) | (v,vs) <- Map.toList (Map.intersectionWith Set.difference cs fs), not (Set.null vs) ]


-- Analysis: 
--   ( Scoping,  -  Free variables with +scopes
--     Scoping,  -  Co-free variables of closures, with +scopes
--     Names,    -  Variable names used
--     Errors)   -  Errors

type Analysis = (Scoping, Scoping, Names, Errors)

class AL a where
  analyse :: a -> Analysis


instance AL Term where
  analyse t0 
    | V v   <- t0 = (single v, Map.empty, Set.singleton v, [])
    | L v t <- t0 = let (fs, _,vs,es) = analyse t
                        e = if Map.member v fs then [] else ["\\" ++ v ++ ". binds no variable"]
                    in (Map.delete v fs, Map.empty, vs, e ++ es)
    | K v t <- t0 = let (fs, _,vs,es) = analyse t
                        e = if (Set.member v vs) then [ "+" ++ v ++ ". binds " ++ v ] else []
                    in (extend v fs, Map.empty, vs, e ++ es)
    | A t u <- t0 = let (ft, _,vt,et) = analyse t
                        (fu, _,vu,eu) = analyse u
                        e = e_variableOverlap vt vu
                    in (Map.union ft fu, Map.empty, Set.union vt vu, e ++ et ++ eu )
    | C t c <- t0 = let (ft, _,vt,et) = analyse t
                        (fc,cc,vc,ec) = analyse c
                        e1 = e_applySharing ft cc
                        e2 = e_variableOverlap vt vc
                    in (Map.difference ft cc, Map.empty, Set.union vt vc, e1 ++ e2 ++ et ++ ec )
    | X xs  <- t0 = (singles xs, Map.empty, Set.fromList xs, ["hole in term"])

instance AL Closure where
  analyse c0
    | S xs t <- c0 = let (fs, _,vs,es) = analyse t
                         e = [ show x ++ " occurs both free and cofree in a sharing" | x <- xs, Map.member x fs ] 
                    in (fs, singles xs, vs, e ++ es)
    | D v d <- c0 = let (fs, cs, vs, es) = analyse d
                        e = if Map.member v fs then [] else [ v ++ " binds no variable in a distributor"]
                    in (Map.delete v fs, cs, vs, e ++ es)

instance AL DTerm where
  analyse d0
    | M d   <- d0 = let cs = invert d in (Map.map (const Set.empty) cs, cs, Set.empty, [])
    | N d c <- d0 = let (fd,cd,vd,ed) = analyse d
                        (fc,cc,vc,ec) = analyse c
                        e1 = e_applySharing fd cc
                        e2 = e_variableOverlap vd vc
                    in (Map.union fc (Map.difference fd cc), cd, Set.union vd vc, e1 ++ e2 ++ ed ++ ec )




---------------- UTILS

atIndex :: Int -> (a -> a) -> [a] -> [a]
atIndex _ f [] = []
atIndex 0 f (x:xs) = f x : xs
atIndex n f (x:xs) = x : atIndex (n-1) f xs

{-
indexOf :: a -> [a] -> Maybe Int
indexOf y = f 0 where
  f _ [] = Nothing
  f i (x:xs) = if x == y then Just i else f (i+1) xs
-}

_1of3 (x,_,_) = x
_2of3 (_,x,_) = x
_3of3 (_,_,x) = x


type Relation a b = Map.Map a (Set.Set b)

invert :: (Ord a, Ord b) => Relation a b -> Relation b a
invert r = Map.fromListWith Set.union [ (x,Set.singleton v) | (v,xs) <- Map.toList r, x <- Set.toList xs]





{-

---------------- TERMS

class AL a where

--  substitute :: Term -> Var -> a -> a

  analyse :: a -> (M.Map Var (S.Set Var), M.Map Var (S.Set Var), S.Set Var, [String])

-- analyse  gives the:
--   -free variables and the bar-scopes they fall under
--   -cofree variables and the tri-scopes they fall under
--   -free and bound variables
--   -error messages

  fv :: a -> S.Set Var
  cv :: a -> S.Set Var
  vv :: a -> S.Set Var

  fv t = let (fs,_,_,_) = analyse t in M.keysSet fs
  cv t = let (_,cs,_,_) = analyse t in M.keysSet cs
  vv t = let (_,_,vs,_) = analyse t in vs


instance AL Term where
  analyse t0 
    | V v   <- t0 = (M.singleton v (S.empty), M.empty, S.singleton v, [])
    | L v t <- t0 = let (fs,cs,vs,es) = analyse t
                        e = if M.member v fs then [] else ["\\" ++ v ++ ". binds no variable"]
                    in (M.delete v fs, cs, vs, e ++ es)
    | K v t <- t0 = let (fs, _,vs,es) = analyse t
                        e = if (S.member v vs) then [ v ++ " occurs within its own bar-scope" ] else []
                    in ( M.map (S.insert v) fs, M.empty, vs, e++es)
    | A t u <- t0 = let (ft,_,vt,et) = analyse t
                        (fu,_,vu,eu) = analyse u
                        e = e_variableOverlap vt vu
                    in (M.union ft fu, M.empty, S.union vt vu, e ++ et ++ eu )
    
    | Exp t s <- t0 = let (ft, _,vt,et) = analyse t
                          (fs,cs,vs,es) = analyse s
                          e1 = e_applySharing ft cs
                          e2 = e_variableOverlap vt vs
                      in (M.difference ft cs, M.empty, S.union vt vs, e1 ++ e2 ++ et ++ es )
    | Hole ys <- t0 = (M.fromList $ zip ys (repeat S.empty), M.empty, S.fromList ys, ["hole in term"])


  substitute w y = fromJust . walk Just f (const Nothing) (const Nothing)
    where
      f (Var x) = if y == x then Just w else Nothing
      --f (Abs x t) = if y == x then Just (Abs x t) else Nothing
      f t = Nothing


instance AL Exp where
  analyse s0
    | Share xs t  <- s0 = let (fs,_,vs,es) = analyse t
                              cs = M.fromList (zip xs (repeat S.empty))
                              e = [ show x ++ " occurs both free and cofree in a sharing" | x <- xs, M.member x fs ] 
                          in (fs, cs, vs, e++es)
    | Coshare x m <- s0 = let (fs, cs, vs, es) = analyse m
                              e = if M.member x fs then [] else [ x ++ " binds no variable in a cosharing"]
                          in (M.delete x fs, cs, S.insert x vs, e++es)

  substitute w y s0
    | Share xs t  <- s0 = Share xs (substitute w y t)
    | Coshare x m <- s0 = Coshare x (substitute w y m)

instance AL Medial where
  analyse m0
    | Medial m <- m0 = let cs = invertMap m in (M.map (const S.empty) cs, cs, S.empty, [])
    | Mexp m s <- m0 = let (fm,cm,vm,em) = analyse m
                           (fs,cs,vs,es) = analyse s
                           e1 = e_applySharing fm cs
                           e2 = e_variableOverlap vm vs
                       in (M.union fs (M.difference fm cs), combineMaps cm cs, S.union vm vs, e1++e2++em++es )

  substitute w y m0
    | Medial m <- m0 = Medial m
    | Mexp m s <- m0 = Mexp m (substitute w y s)


invertMap :: Ord a => M.Map a (S.Set a) -> M.Map a (S.Set a)
invertMap m = M.fromListWith S.union [ (x,S.singleton v) | (v,xs) <- M.toList m, x <- S.toList xs]

combineMaps :: (Ord a, Ord b) => M.Map a (S.Set b) ->  M.Map a (S.Set b) ->  M.Map a (S.Set b)
combineMaps = M.unionWith (S.union)



---------------- FOLDING AND TRAVERSING


foldT :: (Term -> a) -> (a -> a -> a) -> Term -> a
foldT f0 g0 = f where
  f t0 = let k = g0 (f0 t0) in
         case t0 of Abs _ t -> k (f t)
                    App t u -> k (g0 (f t) (f u))
                    Bar _ t -> k (f t)
                    Exp t s -> k (g0 (f t) (g s))
                    _ -> f0 t0
  g (Share _ t) = f t
  g (Coshare _ (Medial m)) = error "foldT : medial without shares"  
  g (Coshare _ m) = foldl1 g0 . map g $ mToList m


bars :: Term -> S.Set Var
bars = foldT f (S.union)
  where
    f (Bar x t) = S.singleton x
    f _ = S.empty


walk :: (Alternative m) => 
          (Var    -> m Var)    -> 
          (Term   -> m Term)   -> 
          (Exp    -> m Exp)    ->
          (Medial -> m Medial) -> Term -> m Term
walk onV onT onE onM = f0 where
    f0 t = onT t <|> f t
    f (Var x)   = Var <$> onV x 
    f (Abs x t) = Abs <$> onV x <*> f0 t
    f (App t u) = App <$> f0 t  <*> f0 u
    f (Bar x t) = Bar <$> onV x <*> f0 t
    f (Exp t s) = Exp <$> f0 t  <*> g0 s
    f (Hole xs) = Hole <$> k xs
    g0 s = onE s <|> g s
    g (Share xs t)  = Share   <$> k0 xs  <*> f0 t
    g (Coshare x m) = Coshare <$> onV x <*> h0 m
    h0 m = onM m <|> h m
    h (Medial m) = pure (Medial m) 
    h (Mexp m s) = Mexp <$> h0 m <*> g0 s
    k0 []     = pure []
    k0 (v:vs) = (:) <$> v0 v <*> k0 vs


rename :: Var -> Var -> Term -> Maybe Term
rename v w t | S.member v vs, not (S.member w vs) = walk v0 (const Nothing) (const Nothing) (const Nothing) t
             | otherwise = Nothing
  where
    vs = S.union (vars t) (bars t)
    v0 x = if x == v then Just w else Just x





---------------- ONLY HALF JOKING


data MC a b = Nae | Aye a

getMC :: Monoid a => MC a b -> a
getMC Nae     = mempty
getMC (Aye x) = x

unsafeGetMC :: MC a b -> a
unsafeGetMC (Aye x) = x
unsafeGetMC Nae = error "unsafeGetMC: Nae"

noe :: a -> MC b c
noe x = Nae

instance Functor (MC a) where
  fmap _ Nae     = Nae
  fmap _ (Aye x) = Aye x

instance Monoid a => Applicative (MC a) where
  pure _ = Aye mempty
  Nae   <*> Nae   = Nae
  Nae   <*> Aye y = Aye y
  Aye x <*> Nae   = Aye x
  Aye x <*> Aye y = Aye (x `mappend` y) 

instance Monoid a => Alternative (MC a) where
  empty = Nae
  Nae   <|> Nae   = Nae
  Nae   <|> Aye x = Aye x
  Aye x <|> _     = Aye x


varB :: Var -> Term -> S.Set Var
varB x = getMC . (walk (Aye . S.singleton) g noe noe)
  where
    g t | Bar y u <- t, x == y = Aye $ S.empty
        | otherwise = Nae
    

-}



{-
strictDifference = difference True
laxDifference    = difference False

-- difference m n
--   subtracts n from m:
--   for  (x,s)  in  n 
--        (x,t)  in  m,  s < t  

difference :: Bool -> Scoping -> Scoping -> Either Scoping String
difference b m n = f (Map.toList n) m where
  f [] m = Left m
  f ((x,s):xs) m | Just t <- Map.lookup x m = if Set.isSubsetOf s t 
                                              then f xs $ Map.delete x m
                                              else Right ("variable " ++ x ++ " outside scope of " ++ intercalate "," (Set.toList $ Set.difference s t))
                 | otherwise                = if b
                                              then Right ("variable " ++ x ++ " missing occurrence")
                                              else f xs m
-}