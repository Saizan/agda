{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}
module Agda.TypeChecking.IApplyConfluence where

import Prelude hiding (null, (!!))  -- do not use partial functions like !!

import Control.Monad
import Control.Arrow (first,second)
import Control.Monad.Reader
import Control.Monad.Trans ( lift )

import Data.Either (lefts)
import qualified Data.List as List
import Data.Monoid (Any(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as Trav

import Agda.Syntax.Common
import Agda.Syntax.Position
-- import Agda.Syntax.Literal
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.Interaction.Options

import Agda.TypeChecking.Names
import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Primitive.Cubical
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin

-- import Agda.TypeChecking.Rules.LHS (checkSortOfSplitVar)
-- import Agda.TypeChecking.Rules.LHS.Problem (allFlexVars)
-- import Agda.TypeChecking.Rules.LHS.Unify

-- import Agda.TypeChecking.Coverage.Match
-- import Agda.TypeChecking.Coverage.SplitTree

import Agda.TypeChecking.Conversion (tryConversion, equalType, equalTermOnFace, forallFaceMaps)
-- import Agda.TypeChecking.Datatypes (getConForm)
-- import {-# SOURCE #-} Agda.TypeChecking.Empty (isEmptyTel)
-- import Agda.TypeChecking.Free
-- import Agda.TypeChecking.Irrelevance
-- import Agda.TypeChecking.Patterns.Internal (dotPatternsToPatterns)
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Records
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Telescope.Path
-- import Agda.TypeChecking.MetaVars
-- import Agda.TypeChecking.Warnings

-- import Agda.Interaction.Options

import Agda.Utils.Either
import Agda.Utils.Except
  ( ExceptT
  , MonadError(catchError, throwError)
  , runExceptT
  )
import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Permutation
import Agda.Utils.Pretty (prettyShow)
import Agda.Utils.Size
import Agda.Utils.Tuple
import Agda.Utils.Lens

#include "undefined.h"
import Agda.Utils.Impossible

checkIApplyConfluence_ :: QName -> TCM ()
checkIApplyConfluence_ f = whenM (optCubical <$> pragmaOptions) $ do
  -- Andreas, 2019-03-27, iapply confluence should only be checked when --cubical.
  -- See test/Succeed/CheckIApplyConfluence.agda.
  -- We cannot reach the following crash point unless --cubical.
  __CRASH_WHEN__ "tc.cover.iapply.confluence.crash" 666
  reportSDoc "tc.cover.iapply" 10 $ text "Checking IApply confluence of" <+> pretty f
  inConcreteOrAbstractMode f $ \ d -> do
  case theDef d of
    Function{funClauses = cls', funCovering = cls} -> do
      reportSDoc "tc.cover.iapply" 10 $ text "length cls =" <+> pretty (length cls)
      when (null cls && not (null $ concatMap (iApplyVars . namedClausePats) cls')) $
        __IMPOSSIBLE__
      modifySignature $ updateDefinition f $ updateTheDef
        $ updateCovering (const [])

      forM_ cls $ checkIApplyConfluence f
    _ -> return ()

-- | @addClause f (Clause {namedClausePats = ps})@ checks that @f ps@
-- reduces in a way that agrees with @IApply@ reductions.
checkIApplyConfluence :: QName -> Closure Clause -> TCM ()
checkIApplyConfluence f clos = do
  enterClosure clos $ \ cl ->
    case cl of
      Clause {clauseBody = Nothing} -> return ()
      Clause {clauseType = Nothing} -> __IMPOSSIBLE__
      cl@Clause { clauseTel = clTel
                , namedClausePats = ps
                , clauseType = Just t
                , clauseBody = Just body
                } -> setCurrentRange (getRange f) $ do
          let
            trhs = unArg t
          reportSDoc "tc.cover.iapply" 40 $ "tel =" <+> prettyTCM tel
          reportSDoc "tc.cover.iapply" 40 $ "ps =" <+> pretty ps
          ps <- normaliseProjP ps
          forM_ (iApplyVars ps) $ \ i -> do
            unview <- intervalUnview'
            let phi = unview $ IMax (argN $ unview (INeg $ argN $ var i)) $ argN $ var i
            let es = patternsToElims ps
            let lhs = Def f es

            reportSDoc "tc.iapply" 40 $ text "clause:" <+> pretty ps <+> "->" <+> pretty body
            reportSDoc "tc.iapply" 20 $ "body =" <+> prettyTCM body

            equalTermOnFace phi trhs lhs body
            case body of
              MetaV m es_m ->
                caseMaybeM (isInteractionMeta m) (return ()) $ \ ii -> do
                cs' <- do
                  mv <- lookupMeta m
                  enterClosure (getMetaInfo mv) $ \ _ -> do
                  -- ty <- getMetaType m
                  mTel <- getContextTelescope
                  -- TODO extend telescope to handle extra elims
                  unless (size mTel == size es_m) $ reportSDoc "tc.iapply.ip" 20 $ "funny number of elims"
                  addContext clTel $ do
                    forallFaceMaps phi __IMPOSSIBLE__ $ \ alpha -> do
                    -- TelV tel _ <- telViewUpTo (size es) ty
                    reportSDoc "tc.iapply.ip" 40 $ "i0S =" <+> pretty alpha
                    es <- reduce (alpha `applySubst` es)
                    let
                        idG = raise (size clTel) $ (teleElims mTel [])
                    reportSDoc "tc.iapply.ip" 40 $ "cxt1 =" <+> (prettyTCM =<< getContextTelescope)
                    reportSDoc "tc.iapply.ip" 40 $ prettyTCM $ alpha `applySubst` ValueCmpOnFace CmpEq phi trhs lhs (MetaV m idG)
                    unifyElims (teleElims mTel []) (alpha `applySubst` es_m) $ \ sigma eqs -> do
                    reportSDoc "tc.iapply.ip" 40 $ "cxt2 =" <+> (prettyTCM =<< getContextTelescope)
                    reportSDoc "tc.iapply.ip" 40 $ "sigma =" <+> pretty sigma
                    reportSDoc "tc.iapply.ip" 20 $ "eqs =" <+> prettyTCM eqs
                    buildClosure $ (eqs
                                   , sigma `applySubst`
                                       (ValueCmp CmpEq (alpha `applySubst` trhs) (Def f es) (alpha `applySubst` MetaV m es_m)))
                let f ip = ip { ipClause = case ipClause ip of
                                             ipc@IPClause{ipcBoundary = b}
                                               -> ipc {ipcBoundary = b ++ cs'}
                                             ipc@IPNoClause{} -> ipc}
                modifyInteractionPoints (Map.adjust f ii)
              _ -> return ()


-- | current context is of the form Γ.Δ
unifyElims :: Elims
              -- ^ variables to keep   Γ ⊢ x_n .. x_0 : Γ
           -> Elims
              -- ^ variables to solve  Γ.Δ ⊢ es : Γ
           -> (Substitution -> [(Term,Term)] -> TCM a)
              -- Γ.Δ' ⊢ σ : Γ.Δ
              -- Γ.Δ' new current context.
              -- Γ.Δ' ⊢ [(x = u)]
              -- Γ.Δ', [(x = u)] ⊢ id_g = es[σ] : Γ
           -> TCM a
unifyElims idg es k | Just vs <- allApplyElims idg
                    , Just ts <- allApplyElims es = do
                      dom <- getContext 
                      let (binds' , eqs' ) = candidate (map unArg vs) (map unArg ts)
                          (binds'', eqss') =
                            unzip $ map (\ (j,t:ts) -> ((j,t),map (,var j) ts)) $ Map.toList $ Map.fromListWith (++) (map (second (:[])) binds')
                          cod   = codomain s (map fst binds) dom
                          binds = map (second (raise (size cod - size vs))) binds''
                          eqs   = map (first  (raise $ size dom - size vs)) $ eqs' ++ concat eqss'
                          s     = bindS binds
                      updateContext s (codomain s (map fst binds)) $ do
                      k s (s `applySubst` eqs)
                  | otherwise = __IMPOSSIBLE__
  where
    candidate :: [Term] -> [Term] -> ([(Nat,Term)],[(Term,Term)])
    candidate (i:is) (Var j []:ts) = first ((j,i):) (candidate is ts)
    candidate (i:is) (t:ts)        = second ((i,t):) (candidate is ts)
    candidate [] [] = ([],[])
    candidate _ _ = __IMPOSSIBLE__


    bindS binds = parallelS (for [0..maximum (-1:map fst binds)] $ (\ i -> fromMaybe (deBruijnVar i) (List.lookup i binds)))

    codomain :: Substitution
             -> [Nat] -- ^ support
             -> Context -> Context
    codomain s vs cxt = map snd $ filter (\ (i,c) -> i `List.notElem` vs) $ zip [0..] cxt'
     where
      cxt' = zipWith (\ n d -> dropS n s `applySubst` d) [1..] cxt
