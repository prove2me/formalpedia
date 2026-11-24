-- Prove2me | solution 1 for MeasureTheory.length_revPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:24:31.38666+00:00
-- url     : https://prove2.me/submissions/cac65e3f-7aca-4d7c-9820-4372aa27428b

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
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
theorem _root_.solution (v : ℕ → Bool) (n : ℕ) : (revPrefix v n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [revPrefix, ih]
end MeasureTheory
