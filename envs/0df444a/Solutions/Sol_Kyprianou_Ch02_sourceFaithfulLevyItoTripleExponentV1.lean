-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulLevyItoTripleExponentV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:57:49.569715+00:00
-- url     : https://prove2.me/submissions/7afef359-2dc8-4c07-81cf-14bd657ce79b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulTripleCharFunProductV1
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianDriftCharFunV1
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyTripleExponentAlgebraV1
import Theorems.Thm_Kyprianou_largeJumpProcessLevy
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
    (hind : Kyprianou.IndependentLevyItoComponents P Xgauss Xlarge Xsmall) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => Xgauss t ω + Xlarge t ω + Xsmall t ω)) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        Kyprianou.Ch01.levyTripleExponent
          ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)  := by
  intro t ξ
  rw [Kyprianou.Ch02.sourceFaithfulTripleCharFunProductV1
    P Xgauss Xlarge Xsmall hind t ξ]
  have hG :=
    Kyprianou.Ch02.sourceFaithfulGaussianDriftCharFunV1
      a σ P B Xgauss hgauss t ξ
  have hL_eq :
      Xlarge t = Kyprianou.largeJumpProcess P levyMeasure N t := by
    funext ω
    exact hlarge t ω
  have hL :
      charFun (P.map (Xlarge t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in {x : ℝ | 1 ≤ |x|},
            (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂levyMeasure) := by
    rw [hL_eq]
    exact (Kyprianou.largeJumpProcessLevy P levyMeasure hlevyMeasure N).2 t ξ
  rw [hG, hL, hsmall t ξ]
  exact Kyprianou.Ch02.sourceFaithfulLevyTripleExponentAlgebraV1
    a σ levyMeasure hlevyMeasure t ξ
