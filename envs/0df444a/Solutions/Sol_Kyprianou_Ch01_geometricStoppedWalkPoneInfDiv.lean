-- Prove2me | solution 1 for Kyprianou.Ch01.geometricStoppedWalkPoneInfDiv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:53:10.775277+00:00
-- url     : https://prove2.me/submissions/f2fffd41-b16e-4d26-b2fd-ed6a57f10c19

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
import Theorems.Thm_Kyprianou_Ch01_zeroCountStoppedWalkEqDirac
import Theorems.Thm_Kyprianou_Ch01_diracZeroInfinitelyDivisibleLaw
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory LevyFoundations
open scoped ENNReal BigOperators
set_option autoImplicit false

/-! The p=1 geometric count makes the stopped random walk zero a.s. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hGeometricOne : ∀ k : ℕ,
      P {ω | N ω = k} =
        ENNReal.ofReal ((1 : ℝ) * (1 - (1 : ℝ)) ^ k)) :
    LevyFoundations.isInfinitelyDivisibleLaw
      (P.map (fun ω =>
        ∑ i ∈ Finset.range (N ω), increment i ω)) := by
  have hNzero : P {ω | N ω = 0} = 1 := by
    simpa using hGeometricOne 0
  rw [Kyprianou.Ch01.zeroCountStoppedWalkEqDirac
    P increment N hNmeas hNzero]
  exact Kyprianou.Ch01.diracZeroInfinitelyDivisibleLaw
