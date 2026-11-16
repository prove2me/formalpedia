-- Prove2me | solution 1 for Kyprianou.Ch01.randomWalkReversal_pathCombinatorics
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T17:19:02.763475+00:00
-- url     : https://prove2.me/submissions/addbf1df-7242-47a4-94ee-ec2bf2004e01

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped BigOperators ENNReal
set_option autoImplicit false

/-- The first j reversed increments sum to the original tail of length j. -/
private theorem reverse_prefix_sum_eq_tail
    (a : ℕ → ℝ) (n j : ℕ) (hj : j ≤ n) :
    (∑ i ∈ range j, a (n - 1 - i)) =
      (∑ i ∈ range n, a i) - (∑ i ∈ range (n - j), a i) := by
  induction j with
  | zero => simp
  | succ k ih =>
    have hk : k ≤ n := by omega
    have hstep : n - k = (n - (k + 1)) + 1 := by omega
    have hidx : n - (k + 1) = n - 1 - k := by omega
    calc
      (∑ i ∈ range (k + 1), a (n - 1 - i)) =
          (∑ i ∈ range k, a (n - 1 - i)) + a (n - 1 - k) := by
            rw [sum_range_succ]
      _ = (∑ i ∈ range n, a i) -
          (∑ i ∈ range (n - k), a i) + a (n - 1 - k) := by rw [ih hk]
      _ = (∑ i ∈ range n, a i) -
          (∑ i ∈ range (n - (k + 1)), a i) := by
            rw [hstep, sum_range_succ, hidx]
            ring

/-- Strict terminal-record paths become strictly positive paths under reversal. -/
theorem solution
    (a : ℕ → ℝ) (n : ℕ) (B : Set ℝ) :
    ((∑ i ∈ Finset.range n, a i) ∈ B ∧
      ∀ j : ℕ, j < n →
        (∑ i ∈ Finset.range j, a i) < (∑ i ∈ Finset.range n, a i)) ↔
    ((∑ i ∈ Finset.range n, a (n - 1 - i)) ∈ B ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ n →
        0 < (∑ i ∈ Finset.range j, a (n - 1 - i))) := by
  constructor
  · rintro ⟨hB, hmax⟩
    constructor
    · simpa only [sum_range_reflect] using hB
    · intro j hj hjn
      have hlt : n - j < n := by omega
      have h := hmax (n - j) hlt
      rw [reverse_prefix_sum_eq_tail a n j hjn]
      linarith
  · rintro ⟨hB, hpos⟩
    constructor
    · simpa only [sum_range_reflect] using hB
    · intro j hjn
      have hk : 1 ≤ n - j := by omega
      have hkn : n - j ≤ n := by omega
      have h := hpos (n - j) hk hkn
      rw [reverse_prefix_sum_eq_tail a n (n - j) hkn] at h
      have hjj : n - (n - j) = j := by omega
      rw [hjj] at h
      linarith
