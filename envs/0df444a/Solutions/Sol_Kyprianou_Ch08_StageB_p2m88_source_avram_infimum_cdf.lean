-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m88_source_avram_infimum_cdf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:52:16.722382+00:00
-- url     : https://prove2.me/submissions/63fd5bb7-01b5-49e4-8d84-a94d177b232c

import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_one_sided_passage
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_avram_down_clock_cdf
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Exponential
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

/-- Source-faithful clock-law reduction. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ (F : Filtration ℝ≥0 mΩ)
        (X : AvramDividend.Classical.SpectrallyNegativeLevy P F),
      (∀ᵐ ω ∂P, ∀ t, X.X t ω = D.X t ω) →
      ∀ q : ℝ, 0 < q → ∀ b : ℝ, 0 ≤ b →
      cdf ((P.prod (expMeasure q)).map
        (fun z : Ω × ℝ => -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ z.2.toNNReal ∧ y = X.X s z.1})) b =
        q / Phi ψ q * W q b - q * ∫ s in (0 : ℝ)..b, W q s := by
  intro Ω mΩ P hP D ψ W hψ hW F X hpath q hq b hb
  have heq : downExpectation P D.X q b = downExpectation P X.X q b := by
    unfold downExpectation
    apply integral_congr_ae
    filter_upwards [hpath] with ω hω
    simp only [tauMinus, shifted, hω]
  have hs := (source_result81_one_sided_passage Ω P D ψ hψ W hW).1 q b hq
  have hc := source_result81_avram_down_clock_cdf X q hq b
  rw [heq, hc] at hs
  unfold Zscale at hs
  linarith only [hs]
