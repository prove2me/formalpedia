-- Prove2me | solution 1 for Kyprianou.Ch01.geometricMeasureInfinitelyDivisible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:56:05.230485+00:00
-- url     : https://prove2.me/submissions/fa304905-a05e-4a16-b03d-8c146e1e65a1

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
import Theorems.Thm_Kyprianou_Ch01_diracZeroInfinitelyDivisibleLaw
import Theorems.Thm_Kyprianou_Ch01_geometricMeasure_one_eqDiracZero
import Theorems.Thm_Kyprianou_Ch01_geometricMeasureInfDiv_strict
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory LevyFoundations
set_option autoImplicit false

theorem solution (p : unitInterval.Elem) (hp : p ≠ 0) :
    LevyFoundations.isInfinitelyDivisibleLaw
      ((ProbabilityTheory.geometricMeasure p).map
        (fun k : ℕ => (k : ℝ))) := by
  by_cases hOne : p = 1
  · subst p
    rw [Kyprianou.Ch01.geometricMeasure_one_eqDiracZero]
    have hmap :
        (Measure.dirac (0 : ℕ)).map (fun k : ℕ => (k : ℝ)) =
          Measure.dirac (0 : ℝ) := by simp
    rw [hmap]
    exact Kyprianou.Ch01.diracZeroInfinitelyDivisibleLaw
  · have hpLt : (p : ℝ) < 1 := by
      have hne : (p : ℝ) ≠ 1 := by
        intro heq
        exact hOne (Subtype.ext heq)
      exact lt_of_le_of_ne p.property.2 hne
    exact Kyprianou.Ch01.geometricMeasureInfDiv_strict p hp hpLt
