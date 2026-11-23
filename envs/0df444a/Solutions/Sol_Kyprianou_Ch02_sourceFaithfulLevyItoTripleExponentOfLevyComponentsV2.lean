-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulLevyItoTripleExponentOfLevyComponentsV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:16:39.944939+00:00
-- url     : https://prove2.me/submissions/e60373a4-edd9-4df0-b26a-cc32706d3514

import Theorems.Thm_Kyprianou_ProofPreparation_three_levy_charfun_factorisation
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianDriftCharFunV1
import Theorems.Thm_Kyprianou_largeJumpProcessLevy
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyTripleExponentAlgebraV1
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
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (Xgauss Xlarge Xsmall : ℝ≥0 → Ω → ℝ)
    (hgauss : ∀ t ω, Xgauss t ω = (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ))
    (hlarge : ∀ t ω, Xlarge t ω = Kyprianou.largeJumpProcess P levyMeasure N t ω)
    (hsmall : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (Xsmall t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in Set.Ioo (-1 : ℝ) 1,
            ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure))
    (hGLevy : ProbabilityTheory.IsLevyProcess Xgauss P)
    (hLLevy : ProbabilityTheory.IsLevyProcess Xlarge P)
    (hSLevy : ProbabilityTheory.IsLevyProcess Xsmall P)
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        Kyprianou.Ch01.levyTripleExponent
          ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ) := by
  intro t ξ
  rw [Kyprianou.ProofPreparation.three_levy_charfun_factorisation
    P Xgauss Xlarge Xsmall hGLevy hLLevy hSLevy hind t ξ]
  rw [Kyprianou.Ch02.sourceFaithfulGaussianDriftCharFunV1
    a σ P B Xgauss hgauss t ξ]
  have hXlarge : Xlarge t = Kyprianou.largeJumpProcess P levyMeasure N t := by
    funext ω
    exact hlarge t ω
  rw [hXlarge]
  rw [(Kyprianou.largeJumpProcessLevy P levyMeasure hlevyMeasure N).2 t ξ]
  rw [hsmall t ξ]
  exact Kyprianou.Ch02.sourceFaithfulLevyTripleExponentAlgebraV1
    a σ levyMeasure hlevyMeasure t ξ

