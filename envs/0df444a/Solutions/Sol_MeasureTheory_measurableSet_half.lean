-- Prove2me | solution 1 for MeasureTheory.measurableSet_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:31:13.954408+00:00
-- url     : https://prove2.me/submissions/ef7757f7-2d01-484f-9f11-b9a9876f9341

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity

set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open MeasureTheory
variable (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] [NullSingletonClass μ]
namespace MeasureTheory
theorem _root_.solution (B : Set (ℕ → Bool)) : MeasurableSet (half μ B) := by
  unfold half
  split_ifs with hB
  · exact (exists_measurableSet_subset_measure_eq_half μ hB).choose_spec.2.1
  · exact .empty
end MeasureTheory
