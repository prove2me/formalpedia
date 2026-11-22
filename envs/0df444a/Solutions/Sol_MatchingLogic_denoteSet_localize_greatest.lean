-- Prove2me | solution 1 for MatchingLogic.denoteSet_localize_greatest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:30.362987+00:00
-- url     : https://prove2.me/submissions/77378edb-94f6-4c43-944c-95e6af7a63f5

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
    (Γ : Set (Pattern S Var)) {U : Set M.carrier}
    (hU : M.BackwardClosed U) (hUΓ : U ⊆ M.denoteSet ρ Γ) :
    U ⊆ M.denoteSet ρ (localize Γ) := by
  rw [denoteSet_localize]
  intro u hu v huv
  apply hUΓ
  induction huv with
  | refl => exact hu
  | tail _ hyz ih => exact hU ih hyz
end MatchingLogic
