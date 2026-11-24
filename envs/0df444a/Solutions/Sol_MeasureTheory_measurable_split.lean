-- Prove2me | solution 1 for MeasureTheory.measurable_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:43:31.462442+00:00
-- url     : https://prove2.me/submissions/28ea031f-a3e5-4c53-bb8c-90f578360303

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
public import Theorems.Thm_MeasureTheory_measurableSet_cell
public import Theorems.Thm_MeasureTheory_split_preimage_cylinderOn
public import Theorems.Thm_MeasureTheory_generateFrom_initialCylinders


set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal MeasureTheory IdealInvariant
open scoped ENNReal
open MeasureTheory
variable (μ : Measure (ℕ → Bool)) [IsFiniteMeasure μ] [NullSingletonClass μ]
namespace MeasureTheory
theorem _root_.solution : Measurable (split μ) := by
  have h := @measurable_generateFrom (ℕ → Bool) (ℕ → Bool) _ initialCylinders (split μ) (by
    rintro _ ⟨n, v, rfl⟩
    rw [split_preimage_cylinderOn]
    exact measurableSet_cell μ _)
  rwa [← generateFrom_initialCylinders] at h
end MeasureTheory
