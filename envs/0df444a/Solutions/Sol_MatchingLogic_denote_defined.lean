-- Prove2me | solution 1 for MatchingLogic.denote_defined
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:25.950267+00:00
-- url     : https://prove2.me/submissions/1286da49-98b3-42e6-8453-71ddcc4750d2

module
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Definitions.Def_LeanPool_MatchingLogic_Soundness
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_Definedness
public import Theorems.Thm_MatchingLogic_FV_app
public import Theorems.Thm_MatchingLogic_FV_bot
public import Theorems.Thm_MatchingLogic_FV_box
public import Theorems.Thm_MatchingLogic_FV_boxes
public import Theorems.Thm_MatchingLogic_FV_dia
public import Theorems.Thm_MatchingLogic_FV_ex
public import Theorems.Thm_MatchingLogic_FV_imp
public import Theorems.Thm_MatchingLogic_FV_var
public import Theorems.Thm_MatchingLogic_Model_reachWord_cons
public import Theorems.Thm_MatchingLogic_Model_reachWord_nil
public import Theorems.Thm_MatchingLogic_boxes_cons
public import Theorems.Thm_MatchingLogic_boxes_nil
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
attribute [local simp] MatchingLogic.FV_app
attribute [local simp] MatchingLogic.FV_bot
attribute [local simp] MatchingLogic.FV_box
attribute [local simp] MatchingLogic.FV_boxes
attribute [local simp] MatchingLogic.FV_dia
attribute [local simp] MatchingLogic.FV_ex
attribute [local simp] MatchingLogic.FV_imp
attribute [local simp] MatchingLogic.FV_var
attribute [local simp] MatchingLogic.Model.reachWord_cons
attribute [local simp] MatchingLogic.Model.reachWord_nil
attribute [local simp] MatchingLogic.boxes_cons
attribute [local simp] MatchingLogic.boxes_nil
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var



set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
namespace MatchingLogic
theorem _root_.solution (M : Model S) (ρ : Var → M.carrier)
    (φ : Pattern (defSig S) Var) :
    ((expand M).denote ρ (defined φ) = Set.univ ↔ ((expand M).denote ρ φ).Nonempty) ∧
      ((expand M).denote ρ (defined φ) = ∅ ↔ (expand M).denote ρ φ = ∅) := by
  have hmem (u : M.carrier) :
      u ∈ (expand M).denote ρ (defined φ) ↔
        ((expand M).denote ρ φ).Nonempty := by
    constructor
    · rintro ⟨a, ha, -⟩
      exact ⟨a 0, ha 0⟩
    · rintro ⟨a, ha⟩
      exact ⟨fun _ => a, fun _ => ha, Set.mem_univ u⟩
  constructor
  · constructor
    · intro h
      let u : M.carrier := Classical.choice M.nonempty
      apply (hmem u).mp
      rw [h]
      exact Set.mem_univ u
    · intro ha
      apply Set.eq_univ_iff_forall.mpr
      intro u
      exact (hmem u).mpr ha
  · constructor
    · intro h
      ext a
      simp only [Set.mem_empty_iff_false, iff_false]
      intro ha
      have hu := (hmem a).mpr ⟨a, ha⟩
      rw [h] at hu
      exact hu
    · intro h
      ext u
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hu
      obtain ⟨a, ha⟩ := (hmem u).mp hu
      rw [h] at ha
      exact ha
end MatchingLogic
