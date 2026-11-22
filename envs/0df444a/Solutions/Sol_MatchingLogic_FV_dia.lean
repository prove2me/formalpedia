-- Prove2me | solution 1 for MatchingLogic.FV_dia
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:16:19.569799+00:00
-- url     : https://prove2.me/submissions/55393154-06e0-4fe1-9227-2ad86e55ae8e

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
namespace MatchingLogic
theorem _root_.solution (e : Coord S) (ψ : Pattern S Var) : FV (dia e ψ) = FV ψ := by
  apply Set.Subset.antisymm
  · simp only [dia, FV_app]
    apply Set.iUnion_subset
    intro i
    split_ifs with h
    · exact le_refl _
    · simp [Pattern.tp]
  · simp only [dia, FV_app]
    intro x hx
    exact Set.mem_iUnion.mpr ⟨e.2, by simpa using hx⟩
end MatchingLogic
