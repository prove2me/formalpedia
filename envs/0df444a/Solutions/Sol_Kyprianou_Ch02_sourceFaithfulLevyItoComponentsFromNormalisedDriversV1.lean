-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulLevyItoComponentsFromNormalisedDriversV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:03:05.108632+00:00
-- url     : https://prove2.me/submissions/883b4116-c8b9-4267-8975-79a387e1f3d2

import Theorems.Thm_Kyprianou_smallJumpLimitCadlagCorrected
import Theorems.Thm_Kyprianou_largeJumpProcessLevy
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianDriftLevyZeroStartV2
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulSmallJumpCharFunOfUniformV2
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulSmallJumpJumpBoundOfUniformV2
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyItoTripleIndependentOfUniformV2
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

theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (hDrivers : ProbabilityTheory.IndepFun
      (fun ω => fun (t : ℝ) => B.W t ω)
      (fun ω => N.N ω) P)
    (hB0 : ∀ ω : Ω, B.W 0 ω = 0) :
    ∃ (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
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
      IndependentLevyItoComponents P Xgauss Xlarge Xsmall := by
  classical
  obtain ⟨M, ℱ, hM, hFil, hMart, hL2, hPath, hCount, hUniform⟩ :=
    Kyprianou.smallJumpLimitCadlagCorrected
      P levyMeasure hlevyMeasure N
  let Xgauss : ℝ≥0 → Ω → ℝ :=
    fun t ω => (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ)
  let Xlarge : ℝ≥0 → Ω → ℝ :=
    Kyprianou.largeJumpProcess P levyMeasure N
  have hGauss : ProbabilityTheory.IsLevyProcess Xgauss P :=
    Kyprianou.Ch02.sourceFaithfulGaussianDriftLevyZeroStartV2
      P a σ B hB0
  have hLarge : ProbabilityTheory.IsLevyProcess Xlarge P :=
    (Kyprianou.largeJumpProcessLevy P levyMeasure hlevyMeasure N).1
  have hBound := Kyprianou.Ch02.sourceFaithfulSmallJumpJumpBoundOfUniformV2
    P levyMeasure hlevyMeasure N M hM hUniform
  have hSmallChar :=
    Kyprianou.Ch02.sourceFaithfulSmallJumpCharFunOfUniformV2
      P levyMeasure hlevyMeasure N M hM hUniform
  have hIndep :=
    Kyprianou.Ch02.sourceFaithfulLevyItoTripleIndependentOfUniformV2
      P levyMeasure hlevyMeasure N M hM a σ B hDrivers hUniform
  have hReg :
      ∀ᵐ ω ∂P,
        (∀ t : ℝ≥0,
          ContinuousWithinAt (fun s => M s ω) (Set.Ici t) t) ∧
        Set.Countable {t : ℝ≥0 | ¬ ContinuousAt (fun s => M s ω) t} ∧
        ∀ t : ℝ≥0, 0 < t →
          ∃ l : ℝ,
            Tendsto (fun s => M s ω) (nhdsWithin t (Set.Iio t)) (nhds l) ∧
            (M t ω ≠ l → |M t ω - l| < 1) := by
    filter_upwards [hPath, hCount, hBound] with ω hp hc hb
    refine ⟨hp.1, hc, ?_⟩
    intro t ht
    obtain ⟨l, hl⟩ := hp.2 t ht
    exact ⟨l, hl, hb t ht l hl⟩
  exact ⟨Xgauss, Xlarge, M, ℱ,
    (fun _ _ => rfl), (fun _ _ => rfl),
    hGauss, hLarge, hM, hFil, hMart, hL2, hReg, hSmallChar, hIndep⟩


