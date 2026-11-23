-- Prove2me | solution 2 for Kyprianou.Ch02.sourceFaithfulGaussianLargeMarginalCharsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:13:52.337674+00:00
-- url     : https://prove2.me/submissions/d16ec907-c345-47a5-81cd-cead739c0303

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulGaussianDriftCharFunV1
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

open Kyprianou.Ch02

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
            ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure)) := by
  intro t ξ
  constructor
  · have hg :=
      Kyprianou.Ch02.sourceFaithfulGaussianDriftCharFunV1
        a σ P B Xgauss hgauss t ξ
    rw [hg]
    congr 1
    push_cast
    ring
  · have hx : Xlarge t = Kyprianou.largeJumpProcess P levyMeasure N t := by
      funext ω
      exact hlarge t ω
    rw [hx]
    have hl :=
      (Kyprianou.largeJumpProcessLevy P levyMeasure hlevyMeasure N).2 t ξ
    rw [hl]
    congr 1
    have heq : {x : ℝ | 1 ≤ |x|} = (Set.Ioo (-1 : ℝ) 1)ᶜ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Ioo]
      constructor
      · intro hbig hinterval
        exact (not_lt_of_ge hbig) (abs_lt.mpr hinterval)
      · intro hinterval
        by_contra hsmall
        exact hinterval (abs_lt.mp (lt_of_not_ge hsmall))
    rw [← heq]
    congr 1
    apply setIntegral_congr_fun
      (measurableSet_le measurable_const continuous_abs.measurable)
    intro x hx
    have hnorm : ¬ |x| < (1 : ℝ) := not_lt_of_ge hx
    simp only [ProbabilityTheory.levyCompensatedIntegrand, hnorm,
      if_false, mul_zero, sub_zero]
    congr 1
    push_cast
    ring
