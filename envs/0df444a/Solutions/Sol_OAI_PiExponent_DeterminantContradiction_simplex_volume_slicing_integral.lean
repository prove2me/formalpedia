-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_slicing_integral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-17T21:51:29.737136+00:00
-- url     : https://prove2.me/submissions/a36f0176-b93f-4e1a-a147-8306c21baa1e

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_simplex_content_closed_form
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_power_integral_factorial_identity

open scoped BigOperators

theorem solution
    (n : ℕ) (r : ℝ) (hr : 0 < r) :
    (MeasureTheory.volume
      {x : Fin (n + 1) → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (n + 1), x i ≤ r}).toReal =
      (MeasureTheory.volume
        {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin n, x i ≤ 1}).toReal *
        (∫ t in (0 : ℝ)..r, (r - t) ^ n) := by
  rw [OAI.PiExponent.DeterminantContradiction.simplex_content_closed_form
    (n + 1) r (le_of_lt hr)]
  rw [OAI.PiExponent.DeterminantContradiction.simplex_content_closed_form
    n 1 (by norm_num)]
  exact OAI.PiExponent.DeterminantContradiction.power_integral_factorial_identity n r