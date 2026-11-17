-- Prove2me | solution 1 for Kyprianou.Ch01.geometricMeasure_oneInfinitelyDivisible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:55:39.897674+00:00
-- url     : https://prove2.me/submissions/8aa0b234-3550-4c8a-b48c-a46e5fcb155d

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
import Theorems.Thm_Kyprianou_Ch01_diracZeroInfinitelyDivisibleLaw
import Theorems.Thm_Kyprianou_Ch01_geometricMeasure_one_eqDiracZero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory LevyFoundations
set_option autoImplicit false

theorem solution :
    LevyFoundations.isInfinitelyDivisibleLaw
      ((ProbabilityTheory.geometricMeasure (1 : unitInterval.Elem)).map
        (fun k : ℕ => (k : ℝ))) := by
  rw [Kyprianou.Ch01.geometricMeasure_one_eqDiracZero]
  have hmap :
      (Measure.dirac (0 : ℕ)).map (fun k : ℕ => (k : ℝ)) =
        Measure.dirac (0 : ℝ) := by simp
  rw [hmap]
  exact Kyprianou.Ch01.diracZeroInfinitelyDivisibleLaw
