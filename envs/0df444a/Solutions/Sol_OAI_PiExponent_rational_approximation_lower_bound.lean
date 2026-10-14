-- Prove2me | solution 1 for OAI.PiExponent.rational_approximation_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-12T19:43:39.769904+00:00
-- url     : https://prove2.me/submissions/59f084a4-96ea-47cb-ba42-72de1e7176f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Theorems.Thm_OAI_PiExponent_rational_approximation_local_bound
import Theorems.Thm_OAI_PiExponent_rational_approximation_far_numerator_bound

theorem solution (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ (p : ℤ) (q : ℕ), Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by
  obtain ⟨Q, hQ, hlocal⟩ := OAI.PiExponent.rational_approximation_local_bound nu hnu
  refine ⟨Q, hQ, ?_⟩
  intro p q hq
  by_cases hnear : |(p : ℝ)| ≤ 4 * (q : ℝ)
  · exact hlocal p q hq hnear
  · exact OAI.PiExponent.rational_approximation_far_numerator_bound nu hnu p q (le_trans hQ hq) (lt_of_not_ge hnear)
