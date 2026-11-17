-- Prove2me | solution 1 for Kyprianou.Ch01.geometricMeasureInfDiv_strict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:23:02.283816+00:00
-- url     : https://prove2.me/submissions/05d7f32b-03ce-4576-876a-c418265156e4

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
import Theorems.Thm_Kyprianou_Ch01_geometricStrictCompoundPoissonRealisation
import Theorems.Thm_levy_foundations_isInfinitelyDivisibleLaw_iff_real
import Theorems.Thm_levy_foundations_compoundPoissonMarginalInfinitelyDivisible
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory LevyFoundations
open scoped NNReal
set_option autoImplicit false

/-! Reduce the strict geometric case to a genuine compound-Poisson law identity. -/
theorem solution
    (p : unitInterval.Elem) (hp : p ≠ 0) (hp1 : (p : ℝ) < 1) :
    LevyFoundations.isInfinitelyDivisibleLaw
      ((ProbabilityTheory.geometricMeasure p).map
        (fun k : ℕ => (k : ℝ))) := by
  obtain ⟨r, ν', Ω, m, μ, τ, Y, hν, hμ, hr, hνzero, hd, heq⟩ :=
    Kyprianou.Ch01.geometricStrictCompoundPoissonRealisation p hp hp1
  letI : MeasurableSpace Ω := m
  letI : IsProbabilityMeasure ν' := hν
  letI : IsProbabilityMeasure μ := hμ
  rw [heq]
  exact (levy_foundations_isInfinitelyDivisibleLaw_iff_real _).mpr
    (levy_foundations_compoundPoissonMarginalInfinitelyDivisible
      hd hr hνzero 0 (1 : ℝ≥0))
