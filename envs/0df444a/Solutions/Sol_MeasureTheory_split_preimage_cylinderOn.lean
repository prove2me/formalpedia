-- Prove2me | solution 1 for MeasureTheory.split_preimage_cylinderOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:42:21.878581+00:00
-- url     : https://prove2.me/submissions/e4a69f8a-0c2c-4f7e-b758-96325e3277c4

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
public import Theorems.Thm_MeasureTheory_length_revPrefix
public import Theorems.Thm_MeasureTheory_mem_cell_revPrefix_iff
public import Theorems.Thm_MeasureTheory_flip_apply_self
public import Theorems.Thm_MeasureTheory_flip_flip
public import Theorems.Thm_MeasureTheory_mem_cylinderOn
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
theorem _root_.solution (n : ℕ) (v : ℕ → Bool) :
    split μ ⁻¹' cylinderOn (Finset.range n) v = cell μ (revPrefix v n) := by
  ext x
  simp [mem_cylinderOn, mem_cell_revPrefix_iff]
end MeasureTheory
