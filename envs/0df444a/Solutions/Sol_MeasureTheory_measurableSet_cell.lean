-- Prove2me | solution 1 for MeasureTheory.measurableSet_cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:32:01.419472+00:00
-- url     : https://prove2.me/submissions/1b327501-acfd-4434-a08c-f3db52f5146a

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
public import Theorems.Thm_MeasureTheory_measurableSet_half
public import Theorems.Thm_MeasureTheory_Determined_diff
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
theorem _root_.solution (s : List Bool) : MeasurableSet (cell μ s) := by
  induction s with
  | nil => exact .univ
  | cons b s ih =>
    cases b
    · simpa [cell] using ih.diff (measurableSet_half μ _)
    · simpa [cell] using measurableSet_half μ _
end MeasureTheory
