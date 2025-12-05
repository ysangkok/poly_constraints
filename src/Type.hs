{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Type where

import Data.String

newtype TVar = TV String
  deriving (Show, Eq, Ord, IsString)

data Type
  = TVar TVar
  | TCon String
  | TArr Type Type
  deriving (Show, Eq, Ord)

-- Class name
newtype CName = CName { cNameToString :: String }
  deriving (Show, Eq, Ord)

data Qual t = Qual
  { qualPreds :: [Pred]
  , qualT :: t
  }
  deriving Show

data Pred = Pred
  { predCName :: CName
  , predInst :: Type
  }
  deriving (Eq, Show)

newtype ClassEnv = ClassEnv
  { getInsts :: [Qual Pred]
  }

data Scheme = Forall [Qual TVar] Type
  deriving (Show)

typeInt, typeBool :: Type
typeInt  = TCon "Int"
typeBool = TCon "Bool"
