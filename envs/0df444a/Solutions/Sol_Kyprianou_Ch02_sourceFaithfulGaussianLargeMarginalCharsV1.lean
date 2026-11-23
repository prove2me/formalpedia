-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulGaussianLargeMarginalCharsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:12:35.79273+00:00
-- url     : https://prove2.me/submissions/089c9846-8331-42fb-9a82-87c90f226eba

import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianDriftCharFunV1
import Theorems.Thm_Kyprianou_largeJumpProcessLevy
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
    (Xgauss Xlarge : ℝ≥0 → Ω → ℝ)
    (hgauss : ∀ t ω, Xgauss t ω = (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ))
    (hlarge : ∀ t ω, Xlarge t ω = Kyprianou.largeJumpProcess P levyMeasure N t ω) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      (charFun (P.map (Xgauss t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          (Complex.I * (((-a) * ξ : ℝ) : ℂ) -
            (((((σ ^ 2 : ℝ≥0) : ℝ) * ξ ^ 2 / 2 : ℝ)) : ℂ)))) ∧
      (charFun (P.map (Xlarge t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in (Set.Ioo (-1 : ℝ) 1)ᶜ,
            ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure))
    := by
  intro t ξ
  constructor
  · have hgaussChar :=
      Kyprianou.Ch02.sourceFaithfulGaussianDriftCharFunV1
        a σ P B Xgauss hgauss t ξ
    convert hgaussChar using 1
    congr 1
    push_cast
    ring
  · have hfun : Xlarge t = Kyprianou.largeJumpProcess P levyMeasure N t := by
      funext ω
      exact hlarge t ω
    rw [hfun]
    rw [(Kyprianou.largeJumpProcessLevy P levyMeasure hlevyMeasure N).2 t ξ]
    have hset : (Set.Ioo (-1 : ℝ) 1)ᶜ =
        {x : ℝ | 1 ≤ |x|} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_Ioo, Set.mem_setOf_eq]
      constructor
      · intro hx
        by_contra habs
        exact hx (abs_lt.mp (lt_of_not_ge habs))
      · intro hx hint
        exact (not_lt_of_ge hx) (abs_lt.mpr hint)
    have hmeas : MeasurableSet {x : ℝ | 1 ≤ |x|} :=
      measurableSet_le measurable_const continuous_abs.measurable
    have hIntegral :
        (∫ x in {x : ℝ | 1 ≤ |x|},
          Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1 ∂levyMeasure) =
        (∫ x in {x : ℝ | 1 ≤ |x|},
          ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hmeas] with x hx
      have hcomp :
          ProbabilityTheory.levyCompensatedIntegrand ξ x =
            Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1 := by
        simp only [ProbabilityTheory.levyCompensatedIntegrand,
          if_neg (not_lt_of_ge hx), mul_zero, sub_zero]
        congr 1
        push_cast
        ring
      rw [hcomp]
    rw [hset, ← hIntegral]

