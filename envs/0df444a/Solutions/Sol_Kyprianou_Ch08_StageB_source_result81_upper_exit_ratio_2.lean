-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.source_result81_upper_exit_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T06:02:27.633223+00:00
-- url     : https://prove2.me/submissions/83415fb2-4d8b-4f3b-bc5d-b1583d93ba65

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_convolution_series_entire
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_discount_convolution_series
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_positive_discount
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_upper_payoff_continuous_zero
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_exponent_quadratic_upper
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_scale_positive_from_quadratic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
open MeasureTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem scale_continuousWithinAt_in_discount
    (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ) (hW : HasSourceScaleFamily ψ W)
    (x q : ℝ) (hq : 0 ≤ q) :
    ContinuousWithinAt (fun r : ℝ => W r x) (Ici 0) q := by
  by_cases hx : 0 ≤ x
  · let F : ℂ → ℂ := fun z =>
      ∑' n : ℕ, z ^ n * ((scaleConvolutionPower (W 0) n x : ℝ) : ℂ)
    have hF : Continuous F :=
      (source_scale_convolution_series_entire ψ W hW x hx).continuous
    have hG : Continuous (fun r : ℝ => (F (r : ℂ)).re) :=
      Complex.continuous_re.comp (hF.comp Complex.continuous_ofReal)
    have hagree : ∀ r ∈ Ici (0 : ℝ), W r x = (F (r : ℂ)).re := by
      intro r hr
      simpa only [F, Complex.ofReal_re] using
        congrArg Complex.re (source_scale_discount_convolution_series ψ W hW x r hx hr)
    exact hG.continuousWithinAt.congr hagree (hagree q hq)
  · have hneg : x < 0 := lt_of_not_ge hx
    have hagree : ∀ r ∈ Ici (0 : ℝ), W r x = (0 : ℝ) := by
      intro r hr
      exact (hW r hr).2.1 x hneg
    exact continuous_const.continuousWithinAt.congr hagree (hagree q hq)

theorem solution
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q x a : ℝ) (hq : 0 ≤ q) (ha : 0 < a) (hxa : x ≤ a) :
    upBeforeDownExpectation P D.X q x a = W q x / W q a := by
  rcases eq_or_lt_of_le hq with hzero | hpos
  · subst q
    obtain ⟨K, hK, hbound⟩ := source_result81_exponent_quadratic_upper Ω P D ψ hψ
    have hWa : 0 < W 0 a :=
      source_result81_scale_positive_from_quadratic ψ 0 (W 0) (hW 0 le_rfl) K hK hbound a ha
    have hwx : Tendsto (fun r => W r x) (nhdsWithin 0 (Ioi 0)) (nhds (W 0 x)) :=
      (scale_continuousWithinAt_in_discount ψ W hW x 0 le_rfl).mono Ioi_subset_Ici_self
    have hwa : Tendsto (fun r => W r a) (nhdsWithin 0 (Ioi 0)) (nhds (W 0 a)) :=
      (scale_continuousWithinAt_in_discount ψ W hW a 0 le_rfl).mono Ioi_subset_Ici_self
    have hpayoff := source_result81_upper_payoff_continuous_zero Ω P D x a
    exact tendsto_nhds_unique hpayoff ((hwx.div hwa (ne_of_gt hWa)).congr' (by
      filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi (0 : ℝ))] with r hr
      exact (source_result81_upper_positive_discount Ω P D ψ hψ W hW r x a hr ha hxa).symm))
  · exact source_result81_upper_positive_discount Ω P D ψ hψ W hW q x a hpos ha hxa
