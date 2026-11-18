-- Prove2me | solution 2 for Kyprianou.Ch01.geometricStoppedWalkStrictInfDiv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:19:57.364736+00:00
-- url     : https://prove2.me/submissions/41baf955-7ee8-432b-b79a-d4f5fc002c52

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
import Theorems.Thm_Kyprianou_Ch01_geometricStoppedWalkStrictDiracOrCompoundPoissonRealisation
import Theorems.Thm_Kyprianou_Ch01_diracZeroInfinitelyDivisibleLaw
import Theorems.Thm_levy_foundations_isInfinitelyDivisibleLaw_iff_real
import Theorems.Thm_levy_foundations_compoundPoissonMarginalInfinitelyDivisible
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory LevyFoundations
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-! Discharge the two mathematically exhaustive compound-geometric law cases. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
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
  rcases Kyprianou.Ch01.geometricStoppedWalkStrictDiracOrCompoundPoissonRealisation
      P p hp0 hp1 increment N hNmeas hIncMeas hIID
      jumpLaw hCommon hGeometric hIndependent with hzero | hcp
  · rw [hzero]
    exact Kyprianou.Ch01.diracZeroInfinitelyDivisibleLaw
  · obtain ⟨r, ν', Ω', m, μ, τ, Y, hν, hμ, hr, hνzero, hd, heq⟩ := hcp
    letI : MeasurableSpace Ω' := m
    letI : IsProbabilityMeasure ν' := hν
    letI : IsProbabilityMeasure μ := hμ
    rw [heq]
    exact (levy_foundations_isInfinitelyDivisibleLaw_iff_real _).mpr
      (levy_foundations_compoundPoissonMarginalInfinitelyDivisible
        hd hr hνzero 0 (1 : ℝ≥0))
