-- Prove2me | solution 4 for OAI.PiExponent.pi_eventual_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T13:53:08.147307+00:00
-- url     : https://prove2.me/submissions/e6466956-3478-479c-8caa-f2f624c879ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_rational_approximation_lower_bound
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OAI.PiExponent

theorem solution : PiEventualLowerBound := by
  change ∀ nu : ℝ, 2 < nu →
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ (p : ℤ) (q : ℕ), Q ≤ q →
      (q : ℝ) ^ (-nu) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|
  intro nu hnu
  exact OAI.PiExponent.rational_approximation_lower_bound nu hnu
