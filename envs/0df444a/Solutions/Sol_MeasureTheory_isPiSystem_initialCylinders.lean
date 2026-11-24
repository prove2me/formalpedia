-- Prove2me | solution 1 for MeasureTheory.isPiSystem_initialCylinders
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:39:34.158838+00:00
-- url     : https://prove2.me/submissions/f77fa05e-f77f-4753-8e0a-95bf606b0713

module
public import Definitions.Def_AddUN_CantorMeasure
public import Definitions.Def_AddUN_InitialCylinder
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_mem_cylinderOn
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution : IsPiSystem initialCylinders := by
  rintro _ ⟨n, v, rfl⟩ _ ⟨m, v', rfl⟩ ⟨w, hw, hw'⟩
  refine ⟨max n m, w, ?_⟩
  ext y
  simp only [mem_inter_iff, mem_cylinderOn, Finset.mem_range] at hw hw' ⊢
  constructor
  · rintro ⟨h1, h2⟩ i hi
    rcases lt_max_iff.1 hi with h | h
    · rw [h1 i h, hw i h]
    · rw [h2 i h, hw' i h]
  · intro h
    exact ⟨fun i hi ↦ (h i (lt_max_of_lt_left hi)).trans (hw i hi),
      fun i hi ↦ (h i (lt_max_of_lt_right hi)).trans (hw' i hi)⟩
end MeasureTheory
