-- Prove2me | solution 1 for MatchingLogic.FV_imp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:14:52.434957+00:00
-- url     : https://prove2.me/submissions/4382fc29-6538-498e-99ec-3cea5d21af43

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
theorem _root_.solution (φ ψ : Pattern S Var) : FV (.imp φ ψ) = FV φ ∪ FV ψ := rfl
end MatchingLogic
