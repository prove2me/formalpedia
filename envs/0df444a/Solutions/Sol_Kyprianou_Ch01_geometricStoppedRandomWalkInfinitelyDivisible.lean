-- Prove2me | solution 1 for Kyprianou.Ch01.geometricStoppedRandomWalkInfinitelyDivisible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:55:23.76194+00:00
-- url     : https://prove2.me/submissions/a913672f-67dd-4224-a55d-aa5e6dc1b55f

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
import Theorems.Thm_Kyprianou_Ch01_geometricStoppedWalkPoneInfDiv
import Theorems.Thm_Kyprianou_Ch01_geometricStoppedWalkStrictInfDiv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory LevyFoundations
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-! Exact split of the source theorem into p=1 and 0<p<1. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hIncMeas : ∀ n : ℕ, Measurable (increment n))
    (hIID : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hCommon : ∀ n : ℕ,
      HasLaw (increment n) jumpLaw P)
    (hGeometric : ∀ k : ℕ,
      P {ω | N ω = k} =
        ENNReal.ofReal (p * (1 - p) ^ k))
    (hIndependent : IndepFun N
      (fun ω => fun n : ℕ => increment n ω) P) :
    LevyFoundations.isInfinitelyDivisibleLaw
      (P.map (fun ω =>
        ∑ i ∈ Finset.range (N ω), increment i ω)) := by
  by_cases hp : p = 1
  · have hGeomOne :
        ∀ k : ℕ, P {ω | N ω = k} =
          ENNReal.ofReal ((1 : ℝ) * (1 - (1 : ℝ)) ^ k) := by
      intro k
      simpa [hp] using hGeometric k
    exact Kyprianou.Ch01.geometricStoppedWalkPoneInfDiv
      P increment N hNmeas hGeomOne
  · have hstrict : p < 1 := lt_of_le_of_ne hp1 hp
    exact Kyprianou.Ch01.geometricStoppedWalkStrictInfDiv
      P p hp0 hstrict increment N hNmeas hIncMeas hIID
      jumpLaw hCommon hGeometric hIndependent
