-- Prove2me | solution 1 for Kyprianou.Ch01.geometricMeasure_one_eqDiracZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:46:05.665558+00:00
-- url     : https://prove2.me/submissions/deab8f36-f0f9-4e73-a8f8-db6769ee0a22

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution :
    ProbabilityTheory.geometricMeasure (1 : unitInterval.Elem) =
      Measure.dirac (0 : ℕ) := by
  apply Measure.ext_of_singleton
  intro k
  have hp : (1 : unitInterval.Elem) ≠ 0 := one_ne_zero
  rw [ProbabilityTheory.geometricMeasure_singleton hp k]
  by_cases hk : k = 0
  · subst k
    norm_num
  · simp [hk]
