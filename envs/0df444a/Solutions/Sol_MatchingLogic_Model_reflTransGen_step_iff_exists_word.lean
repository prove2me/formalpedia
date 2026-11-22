-- Prove2me | solution 1 for MatchingLogic.Model.reflTransGen_step_iff_exists_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:21:55.289424+00:00
-- url     : https://prove2.me/submissions/9ea2397f-636f-4b4b-8659-28b0620e9d2f

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
public import Theorems.Thm_MatchingLogic_Model_step_iff_exists_coord
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
open MatchingLogic.Model
variable (M : Model S)
namespace MatchingLogic.Model
theorem _root_.solution (u v : M.carrier) :
    Relation.ReflTransGen M.Step u v ↔ ∃ p : List (Coord S), M.reachWord p u v := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[], rfl⟩
    | head hac _ ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨e, he⟩ := (M.step_iff_exists_coord _ _).mp hac
      exact ⟨e :: p, _, he, hp⟩
  · rintro ⟨p, hp⟩
    induction p generalizing u with
    | nil =>
      simp only [Model.reachWord_nil] at hp
      exact hp ▸ Relation.ReflTransGen.refl
    | cons e p ih =>
      obtain ⟨w, hstep, hrest⟩ := (M.reachWord_cons e p u v).mp hp
      exact Relation.ReflTransGen.head ((M.step_iff_exists_coord u w).mpr ⟨e, hstep⟩) (ih w hrest)
end MatchingLogic.Model
