-- Prove2me | solution 1 for MatchingLogic.denote_boxes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:49.357717+00:00
-- url     : https://prove2.me/submissions/b137cf3a-e594-424f-8d70-44e7a7f259e4

module
public import Definitions.Def_LeanPool_MatchingLogic_Semantics
public import Mathlib.Logic.Relation
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_denote_box
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var


attribute [local simp] MatchingLogic.boxes_nil
attribute [local simp] MatchingLogic.boxes_cons
attribute [local simp] MatchingLogic.Model.reachWord_nil
attribute [local simp] MatchingLogic.Model.reachWord_cons

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type}
variable [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution (M : Model S) (ρ : Var → M.carrier) (p : List (Coord S))
    (ψ : Pattern S Var) :
    M.denote ρ (boxes p ψ) = {u | ∀ v, M.reachWord p u v → v ∈ M.denote ρ ψ} := by
  induction p with
  | nil =>
    ext u
    simp
  | cons e p ih =>
    ext u
    simp only [boxes_cons, denote_box, Model.reachWord_cons, Set.mem_ofPred_eq]
    constructor
    · rintro h v ⟨w, hstep, hrest⟩
      have hw : w ∈ M.denote ρ (boxes p ψ) := h w hstep
      rw [ih] at hw
      exact hw v hrest
    · intro h v hstep
      rw [ih]
      intro w hrest
      exact h w ⟨v, hstep, hrest⟩
end MatchingLogic
