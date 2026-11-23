-- Prove2me | solution 2 for Kyprianou.Ch02.sourceFaithfulLevyItoTripleExponentV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:58:38.633812+00:00
-- url     : https://prove2.me/submissions/206f0175-fae9-420d-a12c-705377a71c09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_tripleIndependentCharFun
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianLargeMarginalCharsV1
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyExponentSmallLargeSplitV1
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

open Kyprianou
noncomputable section

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
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        Kyprianou.Ch01.levyTripleExponent
          ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ) := by
  intro t ξ
  have hFactor :=
    Kyprianou.Ch02.tripleIndependentCharFun
      P Xgauss Xlarge Xsmall hind t ξ
  obtain ⟨hGaussChar, hLargeChar⟩ :=
    Kyprianou.Ch02.sourceFaithfulGaussianLargeMarginalCharsV1
      a σ levyMeasure hlevyMeasure P B N Xgauss Xlarge
      hgauss hlarge t ξ
  rw [hFactor, hGaussChar, hLargeChar, hsmall t ξ]
  rw [Kyprianou.Ch02.sourceFaithfulLevyExponentSmallLargeSplitV1
    a σ levyMeasure hlevyMeasure ξ]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring
