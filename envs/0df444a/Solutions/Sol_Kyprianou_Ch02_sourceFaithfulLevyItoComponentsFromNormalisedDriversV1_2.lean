-- Prove2me | solution 2 for Kyprianou.Ch02.sourceFaithfulLevyItoComponentsFromNormalisedDriversV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:05:53.381218+00:00
-- url     : https://prove2.me/submissions/ccee0dae-2c3f-4112-b2ac-931435704996

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Theorems.Thm_Kyprianou_smallJumpLimitCadlagCorrected
import Theorems.Thm_Kyprianou_largeJumpProcessLevy
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianDriftLevyZeroStartV2
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulSmallJumpCharFunOfUniformV2
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulSmallJumpJumpBoundOfUniformV2
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyItoTripleIndependentOfUniformV2
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
  obtain ⟨M, ℱ, hM, hF, hmart, hLp, hcad, hcount, hunif⟩ :=
    Kyprianou.smallJumpLimitCadlagCorrected P levyMeasure hlevyMeasure N
  have hG := Kyprianou.Ch02.sourceFaithfulGaussianDriftLevyZeroStartV2
    P a σ B hB0
  have hL := (Kyprianou.largeJumpProcessLevy P levyMeasure hlevyMeasure N).1
  have hchar := Kyprianou.Ch02.sourceFaithfulSmallJumpCharFunOfUniformV2
    P levyMeasure hlevyMeasure N M hM hunif
  have hjump := Kyprianou.Ch02.sourceFaithfulSmallJumpJumpBoundOfUniformV2
    P levyMeasure hlevyMeasure N M hM hunif
  have hind := Kyprianou.Ch02.sourceFaithfulLevyItoTripleIndependentOfUniformV2
    P levyMeasure hlevyMeasure N M hM a σ B hDrivers hunif
  refine ⟨_, _, M, ℱ, fun _ _ => rfl, fun _ _ => rfl,
    hG, hL, hM, hF, hmart, hLp, ?_, hchar, hind⟩
  filter_upwards [hcad, hcount, hjump] with ω hc hn hj
  refine ⟨hc.1, hn, ?_⟩
  intro t ht
  obtain ⟨l, hl⟩ := hc.2 t ht
  exact ⟨l, hl, hj t ht l hl⟩
