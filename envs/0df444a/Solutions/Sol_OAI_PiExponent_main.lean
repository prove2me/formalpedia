-- Prove2me | solution 1 for OAI.PiExponent.main
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:21:54.610514+00:00
-- url     : https://prove2.me/submissions/ba3b6b68-b76a-4a05-bf7f-d9733219f369
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_pi_eventual_lower_bound
import Theorems.Thm_OAI_PiExponent_eventualLowerBound_iff_integer
import Theorems.Thm_OAI_PiExponent_pi_irrationalityExponent_eq_two_of_eventualLowerBound

theorem solution :
  (∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
    ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) ∧
  sSup {ν : ℝ | 0 < ν ∧
    Set.Infinite {r : ℚ | 2 ≤ r.den ∧
      0 < |Real.pi - (r : ℝ)| ∧
      |Real.pi - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}} = 2 := by
  constructor
  · exact (OAI.PiExponent.eventualLowerBound_iff_integer Real.pi).mp
      OAI.PiExponent.pi_eventual_lower_bound
  · exact OAI.PiExponent.pi_irrationalityExponent_eq_two_of_eventualLowerBound
      OAI.PiExponent.pi_eventual_lower_bound
