-- Prove2me | solution 1 for Kyprianou.Ch04.simplePredictableFiniteOrthogonalIsometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T20:03:44.776107+00:00
-- url     : https://prove2.me/submissions/301be200-59bf-4b04-a317-3c9e8ac8d0c5

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Theorems.Thm_LevyStochCalc_Poisson_Compensated_simpleIntegral_offDiagonal
import Theorems.Thm_Kyprianou_Ch04_orthogonalFiniteFamilyL2Identity
open MeasureTheory ProbabilityTheory LevyStochCalc.Poisson
open LevyStochCalc.Poisson.Compensated
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
universe u v

/-- Isometry of a finite simple predictable Poisson integral from its diagonal moments. -/
theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ (inferInstance : MeasurableSpace Ω))
    (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (hAdapt : ∀ i : Fin φ.N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (φ.partition i.castSucc)) (φ.ξ i))
    (hProd : ∀ i j : Fin φ.N,
      Integrable (fun ω =>
        (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) *
        (φ.ξ j ω * N.compensated (φ.timeRect j T) ω)) P)
    (hDiag : ∀ i : Fin φ.N,
      (∫ ω, (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2 ∂P) =
        (referenceIntensity ν (φ.timeRect i T)).toReal *
          ∫ ω, (φ.ξ i ω) ^ 2 ∂P) :
    ∫ ω, (∑ i : Fin φ.N,
      φ.ξ i ω * N.compensated (φ.timeRect i T) ω) ^ 2 ∂P =
      ∑ i : Fin φ.N, (referenceIntensity ν (φ.timeRect i T)).toReal *
        ∫ ω, (φ.ξ i ω) ^ 2 ∂P := by
  let Z : Fin φ.N → Ω → ℝ :=
    fun i ω => φ.ξ i ω * N.compensated (φ.timeRect i T) ω
  have horth (i j : Fin φ.N) (hij : i ≠ j) :
      ∫ ω, Z i ω * Z j ω ∂P = 0 := by
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact simpleIntegral_offDiagonal N ℱ hℱ φ hij (hAdapt i) (hAdapt j)
    · calc
        ∫ ω, Z i ω * Z j ω ∂P =
            ∫ ω, Z j ω * Z i ω ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          exact mul_comm _ _
        _ = 0 := simpleIntegral_offDiagonal N ℱ hℱ φ hji (hAdapt j) (hAdapt i)
  calc
    ∫ ω, (∑ i : Fin φ.N, Z i ω) ^ 2 ∂P =
        ∑ i : Fin φ.N, ∫ ω, (Z i ω) ^ 2 ∂P := by
      exact Kyprianou.Ch04.orthogonalFiniteFamilyL2Identity
        P Finset.univ Z (by intro i _ j _; exact hProd i j)
          (by intro i _ j _ hij; exact horth i j hij)
    _ = ∑ i : Fin φ.N, (referenceIntensity ν (φ.timeRect i T)).toReal *
        ∫ ω, (φ.ξ i ω) ^ 2 ∂P := by
      apply Finset.sum_congr rfl
      intro i _
      exact hDiag i
