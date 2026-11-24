-- Prove2me | solution 1 for MeasureTheory.measure_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:40:23.681439+00:00
-- url     : https://prove2.me/submissions/2c6e1953-2950-4554-90e4-1323936d834e

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
public import Theorems.Thm_MeasureTheory_half_subset
public import Theorems.Thm_MeasureTheory_measurableSet_half
public import Theorems.Thm_MeasureTheory_measure_half
public import Theorems.Thm_MeasureTheory_measurableSet_cell
public import Theorems.Thm_MeasureTheory_Determined_univ
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
attribute [local simp] MeasureTheory.flip_apply_self
attribute [local simp] MeasureTheory.flip_flip



set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open MeasureTheory
variable (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] [NullSingletonClass μ]
namespace MeasureTheory
theorem _root_.solution (s : List Bool) : μ (cell μ s) = μ univ * 2⁻¹ ^ s.length := by
  induction s with
  | nil => simp [cell]
  | cons b s ih =>
    have hh := measure_half μ (measurableSet_cell μ s)
    cases b
    · simp only [cell, Bool.false_eq_true, if_false, List.length_cons]
      rw [measure_sdiff (half_subset μ _) (measurableSet_half μ _).nullMeasurableSet
        (measure_ne_top _ _), hh, ENNReal.sub_half (measure_ne_top _ _), ih, pow_succ,
        div_eq_mul_inv, mul_assoc]
    · simp only [cell, if_true, List.length_cons]
      rw [hh, ih, pow_succ, div_eq_mul_inv, mul_assoc]
end MeasureTheory
