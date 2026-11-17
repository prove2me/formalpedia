-- Prove2me | solution 1 for Kyprianou.Ch01.diracZeroInfinitelyDivisibleLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:42:19.886194+00:00
-- url     : https://prove2.me/submissions/31612747-0af8-423d-94a7-c576cdf3b93d

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory LevyFoundations
set_option autoImplicit false

theorem solution :
    LevyFoundations.isInfinitelyDivisibleLaw
      (Measure.dirac (0 : ℝ)) := by
  have hconv : ∀ n : ℕ,
      LevyFoundations.iteratedConvolutionPower (Measure.dirac (0 : ℝ)) n =
        Measure.dirac (0 : ℝ) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [LevyFoundations.iteratedConvolutionPower, ih]
      simp
  intro n hn
  exact ⟨Measure.dirac (0 : ℝ), inferInstance, (hconv n).symm⟩
