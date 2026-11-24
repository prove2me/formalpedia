-- Prove2me | solution 1 for MeasureTheory.map_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:44:30.156259+00:00
-- url     : https://prove2.me/submissions/d207ef36-44a8-483f-ba8e-5ab2e37fef20

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
public import Theorems.Thm_MeasureTheory_measure_cell
public import Theorems.Thm_MeasureTheory_length_revPrefix
public import Theorems.Thm_MeasureTheory_split_preimage_cylinderOn
public import Theorems.Thm_MeasureTheory_measurable_split
public import Theorems.Thm_MeasureTheory_Determined_univ
public import Theorems.Thm_MeasureTheory_Measure_ext_of_initialCylinders
public import Theorems.Thm_MeasureTheory_cantorMeasure_cylinderOn
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_measurableSet_cylinderOn
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip


attribute [local simp] MeasureTheory.length_revPrefix

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open MeasureTheory
variable (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] [NullSingletonClass μ]
namespace MeasureTheory
theorem _root_.solution : μ.map (split μ) = μ univ • cantorMeasure := by
  refine Measure.ext_of_initialCylinders fun n v ↦ ?_
  rw [Measure.map_apply (measurable_split μ) (measurableSet_cylinderOn _ _),
    split_preimage_cylinderOn, measure_cell, Measure.smul_apply, cantorMeasure_cylinderOn,
    smul_eq_mul, Finset.card_range, length_revPrefix]
end MeasureTheory
