-- Prove2me | solution 1 for Kyprianou.Ch04.simplePredictableDiagonalRealMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:15:31.577245+00:00
-- url     : https://prove2.me/submissions/7a0cf824-539b-4c46-8fe9-1bf7cbf876b7

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Theorems.Thm_LevyStochCalc_Poisson_Compensated_simpleIntegral_diagonal
import Theorems.Thm_Kyprianou_Ch04_squareL2IntegralEqNnnorm
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open LevyStochCalc.Poisson.Compensated
open scoped NNReal ENNReal
set_option autoImplicit false
universe u v

/-- Real second moment of one predictable compensated Poisson time cell. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ (inferInstance : MeasurableSpace Ω))
    (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N)
    (hPart : 0 ≤ φ.partition i.castSucc)
    (hAdapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i))
    (hInt : Integrable
      (fun ω => (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2) P)
    (hWeightInt : Integrable (fun ω => (φ.ξ i ω) ^ 2) P) :
    (∫ ω, (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2 ∂P) =
      (referenceIntensity ν (φ.timeRect i T)).toReal *
        ∫ ω, (φ.ξ i ω) ^ 2 ∂P := by
  calc
    (∫ ω, (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2 ∂P) =
        (∫⁻ ω, (‖φ.ξ i ω * N.compensated (φ.timeRect i T) ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal := by
      exact Kyprianou.Ch04.squareL2IntegralEqNnnorm P _ hInt
    _ = ((referenceIntensity ν (φ.timeRect i T)) *
        (∫⁻ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P)).toReal := by
      congr 1
      exact simpleIntegral_diagonal N ℱ hℱ φ i hPart hAdapt
    _ = (referenceIntensity ν (φ.timeRect i T)).toReal *
        ∫ ω, (φ.ξ i ω) ^ 2 ∂P := by
      rw [ENNReal.toReal_mul]
      rw [← Kyprianou.Ch04.squareL2IntegralEqNnnorm P (φ.ξ i) hWeightInt]
