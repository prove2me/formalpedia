-- Prove2me | solution 1 for MatchingLogic.FV_app
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:53.101774+00:00
-- url     : https://prove2.me/submissions/a13a97e1-11e4-4f86-a4fb-71cadddbdda5

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Semantics

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
omit [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution (σ : S.Sym) (f : Fin (S.arity σ) → Pattern S Var) :
    FV (.app σ f) = ⋃ i, FV (f i) := rfl
end MatchingLogic
