{-# LANGUAGE GeneralizedNewtypeDeriving, OverloadedStrings #-}

module Env (
  Env(..),
  empty,
  lookup,
  remove,
  extend,
  extends,
  merge,
  mergeEnvs,
  singleton,
  keys,
  fromList,
  toList,
) where

import Prelude hiding (lookup)

import Syntax
import Type

import qualified Data.Map as Map

-------------------------------------------------------------------------------
-- Typing Environment
-------------------------------------------------------------------------------

data Env = TypeEnv { types :: Map.Map Name Scheme }
  deriving (Show)

empty :: Env
empty = TypeEnv Map.empty

extend :: Env -> (Name, Scheme) -> Env
extend env (x, s) = env { types = Map.insert x s (types env) }

remove :: Env -> Name -> Env
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

extends :: Env -> [(Name, Scheme)] -> Env
extends env xs = env { types = Map.union (Map.fromList xs) (types env) }

lookup :: Name -> Env -> Maybe Scheme
lookup key (TypeEnv tys) = Map.lookup key tys

merge :: Env -> Env -> Env
merge (TypeEnv a) (TypeEnv b) = TypeEnv (Map.union a b)

mergeEnvs :: [Env] -> Env
mergeEnvs = foldl' merge empty

singleton :: Name -> Scheme -> Env
singleton x y = TypeEnv (Map.singleton x y)

keys :: Env -> [Name]
keys (TypeEnv env) = Map.keys env

fromList :: [(Name, Scheme)] -> Env
fromList xs = TypeEnv (Map.fromList xs)

toList :: Env -> [(Name, Scheme)]
toList (TypeEnv env) = Map.toList env

instance Semigroup Env where
  a <> b = merge a b

instance Monoid Env where
  mempty = empty

eqEnv :: Env
eqEnv =
  singleton "eq" $
    Forall [Qual [Pred (CName "Eq") $ TVar "a"]
                 "a"
           ] $
      TArr (TVar "a") $
        TArr (TVar "a") typeBool

--try
--let Right ex2 = parseExpr "\\m -> (let y = m in (let x = eq (y True) (y False) in x))"
--pPrint $ runInfer $ do { inferType eqEnv ex2 }
