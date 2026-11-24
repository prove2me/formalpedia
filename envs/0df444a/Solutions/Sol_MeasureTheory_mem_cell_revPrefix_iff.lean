-- Prove2me | solution 1 for MeasureTheory.mem_cell_revPrefix_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:41:03.685805+00:00
-- url     : https://prove2.me/submissions/97efd286-7bd6-4c6d-90be-4687c847d579

module
public import Definitions.Def_AddUN_InitialCylinder
public import Definitions.Def_AddUN_Statements
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
public import Definitions.Def_AddUN_Uniformity
public import Theorems.Thm_MeasureTheory_half_subset
public import Theorems.Thm_MeasureTheory_length_revPrefix
public import Theorems.Thm_MeasureTheory_revPrefix_congr
public import Theorems.Thm_MeasureTheory_pre_eq
public import Theorems.Thm_MeasureTheory_mem_cell_pre
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
theorem _root_.solution (x v : ℕ → Bool) (n : ℕ) :
    x ∈ cell μ (revPrefix v n) ↔ ∀ i < n, split μ x i = v i := by
  constructor
  · induction n with
    | zero => exact fun _ i hi ↦ absurd hi (Nat.not_lt_zero i)
    | succ n ih =>
      intro hx
      have hsub : x ∈ cell μ (revPrefix v n) := by
        simp only [revPrefix, cell] at hx
        split_ifs at hx
        · exact half_subset μ _ hx
        · exact hx.1
      have hlow := ih hsub
      have hpre : pre μ x n = revPrefix v n := by rw [pre_eq, revPrefix_congr hlow]
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact hlow i h
      · simp only [revPrefix, cell] at hx
        unfold split
        rw [hpre]
        split_ifs at hx with hv
        · rw [hv]
          simpa using hx
        · rw [Bool.eq_false_iff.2 hv]
          simpa using hx.2
  · intro h
    rw [← revPrefix_congr h, ← pre_eq]
    exact mem_cell_pre μ x n
end MeasureTheory
