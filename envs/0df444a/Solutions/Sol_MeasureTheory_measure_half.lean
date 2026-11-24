-- Prove2me | solution 1 for MeasureTheory.measure_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:39:36.938672+00:00
-- url     : https://prove2.me/submissions/bdd63435-55ef-4f5c-b9e5-9a9b6a4a8bf8

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
theorem _root_.solution {B : Set (ℕ → Bool)} (hB : MeasurableSet B) : μ (half μ B) = μ B / 2 := by
  unfold half
  rw [dif_pos hB]
  exact (exists_measurableSet_subset_measure_eq_half μ hB).choose_spec.2.2
end MeasureTheory
