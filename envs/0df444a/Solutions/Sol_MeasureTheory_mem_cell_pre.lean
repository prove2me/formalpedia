-- Prove2me | solution 1 for MeasureTheory.mem_cell_pre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:39:59.041529+00:00
-- url     : https://prove2.me/submissions/fd266109-0df4-4495-b703-f35f457002f7

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
public import Theorems.Thm_MeasureTheory_length_revPrefix
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
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
theorem _root_.solution (x : ℕ → Bool) (n : ℕ) : x ∈ cell μ (pre μ x n) := by
  induction n with
  | zero => exact mem_univ x
  | succ n ih =>
    by_cases hx : x ∈ half μ (cell μ (pre μ x n))
    · simp [pre, cell, hx]
    · simpa [pre, cell, hx] using ih
end MeasureTheory
