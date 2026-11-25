-- Prove2me | solution 1 for Kyprianou.Ch04.simplePredictableFiniteL2Isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:24:27.972101+00:00
-- url     : https://prove2.me/submissions/dc1de6bb-c401-4d0c-989b-72625b5b268a

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Theorems.Thm_Kyprianou_Ch04_simplePredictableFullyDiagonalFiniteIsometry
import Theorems.Thm_Kyprianou_Ch04_integrableProductOfSquareIntegrable
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open LevyStochCalc.Poisson.Compensated
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
universe u v

/-- Finite simple predictable Poisson isometry using individual L2 hypotheses only. -/
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
    (hZMeas : ∀ i : Fin φ.N, AEStronglyMeasurable
      (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i T) ω) P)
    (hZSq : ∀ i : Fin φ.N, Integrable
      (fun ω => (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2) P)
    (hWeightInt : ∀ i : Fin φ.N,
      Integrable (fun ω => (φ.ξ i ω) ^ 2) P) :
    ∫ ω, (∑ i : Fin φ.N,
      φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2 ∂P =
      ∑ i : Fin φ.N, (referenceIntensity ν (φ.timeRect i T)).toReal *
        ∫ ω, (φ.ξ i ω) ^ 2 ∂P := by
  have hProd : ∀ i j : Fin φ.N,
      Integrable (fun ω =>
        (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) *
        (φ.ξ j ω * N.compensated (φ.timeRect j T) ω)) P := by
    intro i j
    exact Kyprianou.Ch04.integrableProductOfSquareIntegrable P _ _
      (hZMeas i) (hZMeas j) (hZSq i) (hZSq j)
  exact Kyprianou.Ch04.simplePredictableFullyDiagonalFiniteIsometry
    P ν N ℱ hℱ φ hPart hAdapt hProd hWeightInt
