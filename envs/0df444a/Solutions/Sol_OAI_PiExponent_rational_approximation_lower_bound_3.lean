-- Prove2me | solution 3 for OAI.PiExponent.rational_approximation_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T13:49:56.150658+00:00
-- url     : https://prove2.me/submissions/e2693d49-1f0c-49cb-9b62-aa6145508f5b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_rational_approximation_local_bound
import Theorems.Thm_OAI_PiExponent_rational_approximation_far_numerator_bound
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ (p : ℤ) (q : ℕ), Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by
  obtain ⟨Q, hQ, hlocal⟩ :=
    OAI.PiExponent.rational_approximation_local_bound nu hnu
  refine ⟨Q, hQ, ?_⟩
  intro p q hq
  by_cases hlarge : 4 * (q : ℝ) < |(p : ℝ)|
  · exact OAI.PiExponent.rational_approximation_far_numerator_bound
      nu hnu p q (hQ.trans hq) hlarge
  · exact hlocal p q hq (le_of_not_gt hlarge)
