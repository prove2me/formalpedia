-- Prove2me | solution 1 for MeasureTheory.measurePreserving_flipSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:32:02.2325+00:00
-- url     : https://prove2.me/submissions/79deba23-8a51-44d2-9bfa-1995eaab22cf

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_ZeroOne
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_uniformBool_map_not
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution (s : Finset ℕ) :
    MeasurePreserving (flipSet s) cantorMeasure cantorMeasure := by
  have hf : ∀ j : ℕ, Measurable (fun b : Bool ↦ if j ∈ s then !b else b) := fun j ↦ by fun_prop
  have hflip : flipSet s =
      fun (w : ℕ → Bool) j ↦ (fun b : Bool ↦ if j ∈ s then !b else b) (w j) := rfl
  refine ⟨by rw [hflip]; fun_prop, ?_⟩
  rw [hflip, cantorMeasure, Measure.infinitePi_map_pi _ hf]
  congr 1
  ext1 j
  by_cases h : j ∈ s
  · simp only [h, if_true]
    exact uniformBool_map_not
  · simp only [h, if_false]
    exact Measure.map_id'
end MeasureTheory
