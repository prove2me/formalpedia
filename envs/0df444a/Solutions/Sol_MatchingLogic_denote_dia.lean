-- Prove2me | solution 1 for MatchingLogic.denote_dia
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:18.141974+00:00
-- url     : https://prove2.me/submissions/d7886f20-0927-4e82-b716-0105f67671cc

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
theorem _root_.solution (M : Model S) (ρ : Var → M.carrier) (e : Coord S)
    (ψ : Pattern S Var) :
    M.denote ρ (dia e ψ) = {u | ∃ v, M.stepAt e u v ∧ v ∈ M.denote ρ ψ} := by
  ext u
  simp only [dia, denote_app, Model.app, Model.stepAt, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, hu⟩
    exact ⟨a e.2, ⟨a, hu, rfl⟩, by simpa using ha e.2⟩
  · rintro ⟨v, ⟨a, hu, rfl⟩, hv⟩
    refine ⟨a, fun j => ?_, hu⟩
    by_cases hj : j = e.2
    · subst hj; simpa using hv
    · simp [hj]
end MatchingLogic
