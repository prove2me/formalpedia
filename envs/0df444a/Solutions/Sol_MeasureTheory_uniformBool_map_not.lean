-- Prove2me | solution 1 for MeasureTheory.uniformBool_map_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:28:00.948879+00:00
-- url     : https://prove2.me/submissions/0efebdc3-da68-4f13-b461-6e4e2ec3f241

module
public import Definitions.Def_AddUN_UniversallyNull
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.ClopenBox
public import Definitions.Def_AddUN_CantorMeasure
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology TopologicalSpace
open scoped ENNReal
open MeasureTheory
namespace MeasureTheory
theorem _root_.solution :
    (PMF.uniformOfFintype Bool).toMeasure.map (fun b ↦ !b) =
      (PMF.uniformOfFintype Bool).toMeasure := by
  refine Measure.ext_of_singleton fun a ↦ ?_
  have h : (fun b : Bool ↦ !b) ⁻¹' {a} = {!a} := by
    ext b
    cases a <;> cases b <;> simp
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton a), h,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp [PMF.uniformOfFintype_apply]
end MeasureTheory
