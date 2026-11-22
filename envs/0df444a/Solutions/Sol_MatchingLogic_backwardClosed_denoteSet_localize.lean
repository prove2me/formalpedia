-- Prove2me | solution 1 for MatchingLogic.backwardClosed_denoteSet_localize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:19.667007+00:00
-- url     : https://prove2.me/submissions/d95bb6c2-26e3-4dd8-be57-be9f1ec3bc4a

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Localization
public import Theorems.Thm_MatchingLogic_denoteSet_localize

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution (M : Model S) (ρ : Var → M.carrier)
    (Γ : Set (Pattern S Var)) :
    M.BackwardClosed (M.denoteSet ρ (localize Γ)) ∧
      M.denoteSet ρ (localize Γ) ⊆ M.denoteSet ρ Γ := by
  constructor
  · rw [denoteSet_localize]
    intro u hu v huv w hvw
    exact hu w (Relation.ReflTransGen.head huv hvw)
  · rw [denoteSet_localize]
    intro u hu
    exact hu u Relation.ReflTransGen.refl
end MatchingLogic
