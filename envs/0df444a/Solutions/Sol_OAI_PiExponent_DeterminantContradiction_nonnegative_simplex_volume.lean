-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:05:53.80071+00:00
-- url     : https://prove2.me/submissions/43a8e570-dc21-44dd-b209-1c04ce26a0a1

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nonnegative_simplex_volume_zero
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nonnegative_simplex_volume_succ

open scoped BigOperators

theorem solution
    (m : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    (MeasureTheory.volume
      {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ U}).toReal =
      U ^ m / (Nat.factorial m : ℝ) := by
  revert U hU
  induction m with
  | zero =>
      intro U hU
      exact OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_zero U hU
  | succ m ih =>
      intro U hU
      apply OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_succ m ?_ U hU
      intro V hV
      exact ih V hV