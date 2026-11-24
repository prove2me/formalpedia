-- Prove2me | solution 1 for MeasureTheory.half_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:31:13.433852+00:00
-- url     : https://prove2.me/submissions/334477cb-e281-40ed-8185-ebafd6a7f216

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
theorem _root_.solution (B : Set (ℕ → Bool)) : half μ B ⊆ B := by
  unfold half
  split_ifs with hB
  · exact (exists_measurableSet_subset_measure_eq_half μ hB).choose_spec.1
  · exact empty_subset _
end MeasureTheory
