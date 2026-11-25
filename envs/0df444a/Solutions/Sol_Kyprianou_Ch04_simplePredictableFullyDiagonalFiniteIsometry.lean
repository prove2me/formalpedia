-- Prove2me | solution 1 for Kyprianou.Ch04.simplePredictableFullyDiagonalFiniteIsometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:19:52.426256+00:00
-- url     : https://prove2.me/submissions/6c3833d0-3c74-4f8d-a997-79d547ae6790

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Theorems.Thm_Kyprianou_Ch04_simplePredictableFiniteOrthogonalIsometry
import Theorems.Thm_Kyprianou_Ch04_simplePredictableDiagonalRealMoment
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open LevyStochCalc.Poisson.Compensated
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
universe u v

/-- Finite predictable Poisson isometry with proved orthogonality and diagonal terms. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ (inferInstance : MeasurableSpace Ω))
    (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (hPart : ∀ i : Fin φ.N, 0 ≤ φ.partition i.castSucc)
    (hAdapt : ∀ i : Fin φ.N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (φ.partition i.castSucc)) (φ.ξ i))
    (hProd : ∀ i j : Fin φ.N,
      Integrable (fun ω =>
        (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) *
        (φ.ξ j ω * N.compensated (φ.timeRect j T) ω)) P)
    (hWeightInt : ∀ i : Fin φ.N,
      Integrable (fun ω => (φ.ξ i ω) ^ 2) P) :
    ∫ ω, (∑ i : Fin φ.N,
      φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2 ∂P =
      ∑ i : Fin φ.N, (referenceIntensity ν (φ.timeRect i T)).toReal *
        ∫ ω, (φ.ξ i ω) ^ 2 ∂P := by
  apply Kyprianou.Ch04.simplePredictableFiniteOrthogonalIsometry
    P ν N ℱ hℱ φ hAdapt hProd
  intro i
  have hi : Integrable
      (fun ω => (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2) P := by
    simpa only [pow_two] using hProd i i
  exact Kyprianou.Ch04.simplePredictableDiagonalRealMoment
    P ν N ℱ hℱ φ i (hPart i) (hAdapt i) hi (hWeightInt i)
