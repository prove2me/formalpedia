-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41FiniteCellGeometryV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:07:02.538915+00:00
-- url     : https://prove2.me/submissions/e945ba53-4b29-4f0c-bf5c-dcf18c99220c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41GridFirstMemberV3
import Theorems.Thm_Kyprianou_Ch04_exercise41SuccessfulCellsV2
import Definitions.Def_Kyprianou_Ch04_exercise41GridFirstV2
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    (x : NNReal → ℝ) (I : Finset ℕ)
    (D : ℕ → Finset NNReal) (b : ℕ → NNReal) (R : Finset NNReal)
    (a h d : ℝ) (hh : 0 < h) (hd : 0 < d)
    (hcell : ∀ i ∈ I, ∀ t ∈ D i,
      a + (i : ℝ) * h ≤ (t : ℝ) ∧
      (t : ℝ) < a + ((i : ℝ) + 1) * h)
    (hR : ∀ i ∈ I, ∀ j ∈ I, i < j →
      ∀ s ∈ D i, ∀ t ∈ D j, t - s ∈ R) :
    let C : NNReal → Set Unit := fun t => {w | |x t| < d * h / 8}
    let τ : ℕ → NNReal := fun i => exercise41GridFirstV2 (D i) C (b i) ()
    let S := I.filter fun i =>
      (∃ t ∈ D i, () ∈ C t) ∧
        ∀ u ∈ R, d / 2 * (u : ℝ) ≤ x (τ i + u) - x (τ i)
    S.card ≤ 2 := by
  dsimp only
  let C : NNReal → Set Unit := fun t => {w | |x t| < d * h / 8}
  let τ : ℕ → NNReal := fun i => exercise41GridFirstV2 (D i) C (b i) ()
  let S := I.filter fun i =>
    (∃ t ∈ D i, () ∈ C t) ∧
      ∀ u ∈ R, d / 2 * (u : ℝ) ≤ x (τ i + u) - x (τ i)
  change S.card ≤ 2
  have hmem (i : ℕ) (hi : i ∈ S) :
      i ∈ I ∧ τ i ∈ D i ∧ |x (τ i)| < d * h / 8 := by
    have hi' := Finset.mem_filter.mp hi
    have hm := exercise41GridFirstMemberV3 (D i) C (b i) () hi'.2.1
    exact ⟨hi'.1, hm.1, hm.2⟩
  apply exercise41SuccessfulCellsV2 S (fun i => (τ i : ℝ))
    (fun i => x (τ i)) a h d hh hd
  · intro i hi
    exact hcell i (hmem i hi).1 _ (hmem i hi).2.1
  · intro i hi
    exact (hmem i hi).2.2
  · intro i hi j hj hij
    have hi' := hmem i hi
    have hj' := hmem j hj
    have hci := hcell i hi'.1 _ hi'.2.1
    have hcj := hcell j hj'.1 _ hj'.2.1
    have hidx : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
    have hlt : (τ i : ℝ) < (τ j : ℝ) := by nlinarith
    have ht : τ i ≤ τ j := by exact_mod_cast hlt.le
    have hr := hR i hi'.1 j hj'.1 hij _ hi'.2.1 _ hj'.2.1
    have hs := (Finset.mem_filter.mp hi).2.2 _ hr
    have hadd : τ i + (τ j - τ i) = τ j := by
      rw [add_comm, tsub_add_cancel_of_le ht]
    rw [hadd, NNReal.coe_sub ht] at hs
    exact hs
