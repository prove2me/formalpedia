-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.nonnegative_simplex_slice_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T09:59:30.380985+00:00
-- url     : https://prove2.me/submissions/a189afef-1161-4ca8-8e4b-3f9b8cf0d922

import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_slice_volume
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_normalized_simplex_power_integral

open scoped BigOperators

theorem solution (m : ℕ) (U : ℝ) (hU : 0 ≤ U) :
    ∫ t in (0 : ℝ)..U,
      (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ U - t}).toReal =
      (U ^ (m + 1)) / (Nat.factorial (m + 1) : ℝ) := by
  have hfun : ∀ t ∈ Set.uIcc (0 : ℝ) U,
      (MeasureTheory.volume
        {x : Fin m → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, x i ≤ U - t}).toReal =
      (U - t) ^ m / (Nat.factorial m : ℝ) := by
    intro t ht
    have htU : t ≤ U := by
      rcases (Set.mem_uIcc.mp ht) with h | h
      · exact h.2
      · linarith [hU, h.1]
    have hv := OAI.PiExponent.DeterminantContradiction.simplex_slice_volume
      m (U - t) (by linarith)
    simpa using hv
  rw [intervalIntegral.integral_congr hfun]
  exact OAI.PiExponent.DeterminantContradiction.normalized_simplex_power_integral m U hU