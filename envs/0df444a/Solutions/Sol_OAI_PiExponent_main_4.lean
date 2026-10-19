-- Prove2me | solution 4 for OAI.PiExponent.main
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T06:48:07.061823+00:00
-- url     : https://prove2.me/submissions/7d06b971-d241-4354-99d0-8a10dc8a8198
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Theorems.Thm_OAI_PiExponent_rational_approximation_lower_bound
import Theorems.Thm_OAI_PiExponent_eventualLowerBound_iff_integer
import Theorems.Thm_OAI_PiExponent_pi_irrationalityExponent_eq_two_of_eventualLowerBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open OAI.PiExponent

theorem solution :
  (∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
    ∀ p q : ℤ, Q ≤ q →
      (q : ℝ) ^ (-ν) ≤ |Real.pi - (p : ℝ) / (q : ℝ)|) ∧
  sSup {ν : ℝ | 0 < ν ∧
    Set.Infinite {r : ℚ | 2 ≤ r.den ∧
      0 < |Real.pi - (r : ℝ)| ∧
      |Real.pi - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}} = 2 := by
  have hpi : PiEventualLowerBound := by
    intro ν hν
    exact rational_approximation_lower_bound ν hν
  constructor
  · exact (eventualLowerBound_iff_integer Real.pi).mp hpi
  · exact pi_irrationalityExponent_eq_two_of_eventualLowerBound hpi
