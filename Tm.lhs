******************************************************************************
**********                                                          **********
**********     Tm                                                   **********
**********                                                          **********
******************************************************************************

> module Tm where
> import Data.Monoid

Here's a representation of beta-normal terms.

> data Tm
>   = Sort :^ Level         -- sorts
>   | L [Tm] Tm             -- a bunch of local lets followed by one lambda
>   | Tm :& Tm              -- pairing
>   | R Tm                  -- recursive wrapping
>   | Integer :+ Tip        -- some successors then a tip...
>   deriving (Show, Eq)

> data Sort = Set | Prop deriving (Show, Eq)
> data Level = U Integer | Top deriving (Show, Eq, Ord)
> instance Monoid Level where
>   mempty = U 0
>   mappend (U i) (U j)  = U (i + j)
>   mappend _ _          = Top

> data Tip
>   = Z                     -- ...which is zero or
>   | N Ne                  -- a stuck computation
>   deriving (Show, Eq)

> data Ne
>   = V Int                            -- untyped de Bruijn index
>   | Name ::: Tm                      -- typed declared symbol
>   | Defn :$^ Level                   -- defined symbol, level shunted
>   | Ne :$ (Elim, [Tm])               -- something which might compute
>   deriving (Show, Eq)

> ne :: Ne -> Tm
> ne n = 0 :+ N n       -- neutrals are embedded by adding zero

> data Elim = A | Car | Cdr deriving (Show, Eq)

> type Decl = Name
> data Defn
>   = Name := (Maybe Tm, Tm)  -- named, maybe defined, typed
>   deriving Show
> instance Eq Defn where
>   (f := _) == (g := _) = f == g

> newtype Name = Nm {nm :: [(String, Int)]} deriving (Show, Eq)

Some things compute, given an environment for free de Bruijn variables.

> class Eval t where
>   eval :: [Tm] -> t -> Tm
>   shunt, shunts :: Level -> t -> t   -- the same things can be level-shunted
>   shunt (U 0) t = t                  -- speed up the identity shunt...
>   shunt l     t = shunts l t         -- ...else call the worker

For example, de Bruijn indices compute by projection from an environment

> instance Eval Int where
>   eval = (!!)
>   shunts _ i = i

Terms compute structurally: the real work happens in tips.

> instance Eval Tm where
>   eval g (s :^ l)  = s :^ l
>   eval g (L g' b)  = L (map (eval g) g' ++ g) b
>   eval g (a :& d)  = eval g a :& eval g d
>   eval g (R t)     = R (eval g t)
>   eval g (k :+ t)  = k /+ eval g t
>   shunts l (s :^ m)  = s :^ (mappend l m)
>   shunts l (L g b)   = L (map (shunts l) g) (shunts l b)
>   shunts l (a :& d)  = shunts l a :& shunts l d
>   shunts l (R t)     = R (shunts l t)
>   shunts l (i :+ t)  = i :+ shunts l t

> instance Eval Tip where
>   eval g Z         = 0 :+ Z     -- zero gives back zero
>   eval g (N n)     = eval g n   -- otherwise evaluate the neutral
>   shunts l Z      = Z
>   shunts l (N n)  = N (shunts l n)

> (/+) :: Integer -> Tm -> Tm
> 0 /+ v         = v              -- adding 0 is always ok
> j /+ (k :+ t)  = (j + k) :+ t   -- adding more works only for numbers

If we have a definition or an elimination, make it go!

> instance Eval Ne where
>   eval g (V i)                        = eval g i
>   eval g ((_ := (Just v, _)) :$^ l)   = shunt l v
>   eval g (n :$ (e, ts))               = eval g n /$ (e, map (eval g) ts)
>   eval g n                            = ne n
>   shunts l (d :$^ m)        = d :$^ (mappend l m)
>   shunts l (n :$ (e, ts))   = shunts l n :$ (e, map (shunts l) ts)
>   shunts l n                = n

> (/$) :: Tm -> (Elim, [Tm]) -> Tm
> (0 :+ N n)  /$ ets         = 0 :+ N (n :$ ets)   -- neutrals get stuck
> (L g b)     /$ (A, [v])    = eval (v : g) b      -- application goes
> (a :& d)    /$ (Car, [])   = a                   -- project
> (a :& d)    /$ (Cdr, [])   = d                   -- project

