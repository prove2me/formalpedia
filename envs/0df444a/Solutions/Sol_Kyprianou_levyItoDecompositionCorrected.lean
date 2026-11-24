-- Prove2me | solution 1 for Kyprianou.levyItoDecompositionCorrected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:38:42.866261+00:00
-- url     : https://prove2.me/submissions/c8f6879a-6eb1-481c-a034-076b724c0789

import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_sigmaFinite
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyItoComponentsCoreV1
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyItoTripleExponentV1
import Theorems.Thm_Kyprianou_ProofPreparation_three_levy_partial_sum_independent_of_levy
import Theorems.Thm_Kyprianou_ProofPreparation_levy_three_sum_of_partial_independence
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou Kyprianou.Ch02
noncomputable section
theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure) :
    ∃ (hσ : SigmaFinite levyMeasure),
      letI : SigmaFinite levyMeasure := hσ
      ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
        letI : MeasurableSpace Ω := measΩ
        ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
          letI : IsProbabilityMeasure P := probP
          ∃ (B : LevyStochCalc.Brownian.BrownianMotion P)
      (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
      (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
      (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      (∀ t ω, Xgauss t ω = (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)) ∧
      (∀ t ω, Xlarge t ω = largeJumpProcess P levyMeasure N t ω) ∧
      ProbabilityTheory.IsLevyProcess Xgauss P ∧
      ProbabilityTheory.IsLevyProcess Xlarge P ∧
      ProbabilityTheory.IsLevyProcess Xsmall P ∧
      Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ ∧
      MeasureTheory.Martingale Xsmall ℱ P ∧
      (∀ t, MemLp (Xsmall t) 2 P) ∧
      (∀ᵐ ω ∂P,
        (∀ t : ℝ≥0,
          ContinuousWithinAt (fun s => Xsmall s ω) (Set.Ici t) t) ∧
        Set.Countable
          {t : ℝ≥0 | ¬ ContinuousAt (fun s => Xsmall s ω) t} ∧
        ∀ t : ℝ≥0, 0 < t →
          ∃ l : ℝ,
            Tendsto (fun s => Xsmall s ω) (nhdsWithin t (Set.Iio t)) (nhds l) ∧
            (Xsmall t ω ≠ l → |Xsmall t ω - l| < 1)) ∧
      (∀ (t : ℝ≥0) (ξ : ℝ),
        charFun (P.map (Xsmall t)) ξ =
          Complex.exp ((((t : ℝ) : ℂ)) *
            ∫ x in Set.Ioo (-1 : ℝ) 1,
              ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure)) ∧
      IndependentLevyItoComponents P Xgauss Xlarge Xsmall ∧
      ProbabilityTheory.IsLevyProcess
        (fun t ω => Xgauss t ω + Xlarge t ω + Xsmall t ω) P ∧
      ∀ (t : ℝ≥0) (ξ : ℝ),
        charFun
          (P.map (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
          Complex.exp ((((t : ℝ) : ℂ)) *
            Kyprianou.Ch01.levyTripleExponent
              ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)
 := by
  letI : SigmaFinite levyMeasure :=
    ProbabilityTheory.IsLevyMeasure.sigmaFinite hlevyMeasure
  refine ⟨inferInstance, ?_⟩
  obtain ⟨Ω, measΩ, P, probP, B, N, Xgauss, Xlarge, Xsmall, ℱ,
    hGaussDef, hLargeDef, hGLevy, hLLevy, hSLevy,
    hFiltration, hMartingale, hL2, hPaths, hSmallChar, hIndep⟩ :=
    Kyprianou.Ch02.sourceFaithfulLevyItoComponentsCoreV1
      a σ levyMeasure hlevyMeasure
  letI : MeasurableSpace Ω := measΩ
  letI : IsProbabilityMeasure P := probP
  have hPairThird :
      IndepFun
        (fun ω => fun t : ℝ≥0 => Xgauss t ω + Xlarge t ω)
        (fun ω => fun t : ℝ≥0 => Xsmall t ω) P :=
    Kyprianou.ProofPreparation.three_levy_partial_sum_independent_of_levy
      P Xgauss Xlarge Xsmall hGLevy hLLevy hSLevy hIndep
  have hSumLevy :
      IsLevyProcess
        (fun t ω => Xgauss t ω + Xlarge t ω + Xsmall t ω) P :=
    Kyprianou.ProofPreparation.levy_three_sum_of_partial_independence
      P Xgauss Xlarge Xsmall hGLevy hLLevy hSLevy hIndep hPairThird
  have hSumChar :=
    Kyprianou.Ch02.sourceFaithfulLevyItoTripleExponentV1
      a σ levyMeasure hlevyMeasure P B N Xgauss Xlarge Xsmall
      hGaussDef hLargeDef hSmallChar hIndep
  exact ⟨Ω, measΩ, P, probP, B, N, Xgauss, Xlarge, Xsmall, ℱ,
    hGaussDef, hLargeDef, hGLevy, hLLevy, hSLevy,
    hFiltration, hMartingale, hL2, hPaths, hSmallChar, hIndep,
    hSumLevy, hSumChar⟩
