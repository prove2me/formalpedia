-- Prove2me | solution 1 for Kyprianou.Ch01.geometricStoppedWalkStrictInfDiv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:17:45.749379+00:00
-- url     : https://prove2.me/submissions/418041d2-1272-4b7c-9a20-6a36c1a4696e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
import Theorems.Thm_Kyprianou_Ch01_geometricStoppedWalkStrictCompoundPoissonRealisation
import Theorems.Thm_levy_foundations_isInfinitelyDivisibleLaw_iff_real
import Theorems.Thm_levy_foundations_compoundPoissonMarginalInfinitelyDivisible
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory LevyFoundations
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-! Strict geometric stopped IID sum: reduce to its genuine compound-Poisson representation. -/
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
  obtain ⟨r, ν', Ω', m, μ, τ, Y, hν, hμ, hr, hνzero, hd, heq⟩ :=
    Kyprianou.Ch01.geometricStoppedWalkStrictCompoundPoissonRealisation
      P p hp0 hp1 increment N hNmeas hIncMeas hIID
      jumpLaw hCommon hGeometric hIndependent
  letI : MeasurableSpace Ω' := m
  letI : IsProbabilityMeasure ν' := hν
  letI : IsProbabilityMeasure μ := hμ
  rw [heq]
  exact (levy_foundations_isInfinitelyDivisibleLaw_iff_real _).mpr
    (levy_foundations_compoundPoissonMarginalInfinitelyDivisible
      hd hr hνzero 0 (1 : ℝ≥0))
