-- Prove2me | solution 1 for GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T02:38:40.15638+00:00
-- url     : https://prove2.me/submissions/74bcb9ca-702f-4e27-bed2-1666015253e4

import Mathlib


theorem solution : ∀ {K : Type} [inst : Field K] (g : ℕ → K) (N : ℕ),
    (∀ (i : ℕ), g (N + i) = g i) → ∀ (k : ℕ),
      ∑ i ∈ Finset.range (N * k), g i = (↑k : K) * ∑ i ∈ Finset.range N, g i := by
  intro K _ g N hg k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm (N*k) N, Finset.sum_range_add]
    simp only [hg, ih, Nat.cast_succ]
    ring
