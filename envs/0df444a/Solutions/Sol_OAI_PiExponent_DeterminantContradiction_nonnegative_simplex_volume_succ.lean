-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_succ
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T03:09:56.839989+00:00
-- url     : https://prove2.me/submissions/38475df5-824a-4150-bbd8-4b809cbf2bd2

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nonnegative_simplex_volume_succ_slice
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nonnegative_simplex_volume_succ_integral

open scoped BigOperators

theorem solution
    (m : ℕ)
    (hprev : ∀ (V : ℝ), 0 ≤ V →
      (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ V}).toReal =
        V ^ m / (Nat.factorial m : ℝ))
    (U : ℝ) (hU : 0 ≤ U) :
    (MeasureTheory.volume
      {x : Fin (m + 1) → ℝ |
        (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ U}).toReal =
      U ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by
  rw [OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_succ_slice
    m U hU]
  exact OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_volume_succ_integral
    m hprev U hU