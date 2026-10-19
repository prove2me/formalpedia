-- Prove2me | solution 4 for OAI.PiExponent.rational_approximation_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T06:13:48.671403+00:00
-- url     : https://prove2.me/submissions/56993444-fc1c-43a8-b720-d93ababa182d
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

/-- Combine the local numerator estimate and the already proved
far-numerator estimate to cover every integer numerator. -/
theorem solution (nu : ℝ) (hnu : 2 < nu) :
    ∃ Q : ℕ, 2 ≤ Q ∧
      ∀ (p : ℤ) (q : ℕ), Q ≤ q →
        (q : ℝ) ^ (-nu) ≤ |Real.pi - (p : ℝ) / (q : ℝ)| := by
  obtain ⟨Q, hQ, hlocal⟩ :=
    OAI.PiExponent.rational_approximation_local_bound nu hnu
  refine ⟨Q, hQ, ?_⟩
  intro p q hq
  by_cases hp : |(p : ℝ)| ≤ 4 * (q : ℝ)
  · exact hlocal p q hq hp
  · exact OAI.PiExponent.rational_approximation_far_numerator_bound
      nu hnu p q (le_trans hQ hq) (lt_of_not_ge hp)
