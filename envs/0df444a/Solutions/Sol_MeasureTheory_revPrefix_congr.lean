-- Prove2me | solution 1 for MeasureTheory.revPrefix_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:39:38.53313+00:00
-- url     : https://prove2.me/submissions/de24671d-0ec0-4616-b85e-670a9f42aa25

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
theorem _root_.solution {v v' : ℕ → Bool} {n : ℕ} (h : ∀ i < n, v i = v' i) :
    revPrefix v n = revPrefix v' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [revPrefix]
    rw [h n (Nat.lt_succ_self n), ih fun i hi ↦ h i (Nat.lt_succ_of_lt hi)]
end MeasureTheory
