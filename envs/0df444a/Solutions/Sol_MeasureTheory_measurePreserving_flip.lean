-- Prove2me | solution 1 for MeasureTheory.measurePreserving_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:29:22.730802+00:00
-- url     : https://prove2.me/submissions/14dae366-48e1-4fab-8140-da22f2bf66b0

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_uniformBool_map_not
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution (i : ℕ) :
    MeasurePreserving (flip i) cantorMeasure cantorMeasure := by
  have hf : ∀ j : ℕ, Measurable (fun b : Bool ↦ if j = i then !b else b) := fun j ↦ by fun_prop
  have hflip : flip i = fun (w : ℕ → Bool) j ↦ (fun b : Bool ↦ if j = i then !b else b) (w j) :=
    rfl
  refine ⟨by rw [hflip]; fun_prop, ?_⟩
  rw [hflip, cantorMeasure, Measure.infinitePi_map_pi _ hf]
  congr 1
  ext1 j
  by_cases h : j = i
  · simp only [h, if_true]
    exact uniformBool_map_not
  · simp only [h, if_false]
    exact Measure.map_id'
end MeasureTheory
