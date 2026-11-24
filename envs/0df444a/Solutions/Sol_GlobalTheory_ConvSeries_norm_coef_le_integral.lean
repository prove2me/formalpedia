-- Prove2me | solution 1 for GlobalTheory.ConvSeries.norm_coef_le_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:09:44.896495+00:00
-- url     : https://prove2.me/submissions/377f7fe4-23b1-41b6-a1c4-d07bfb8c17a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormGaussianConvolutionSeriesCoefficientLeIntegr
import Theorems.Thm_GlobalTheory_ConvSeries_CoefNorm_norm_powForm_le
import Theorems.Thm_GlobalTheory_ConvSeries_CoefNorm_norm_wt_le
import Theorems.Thm_GlobalTheory_ConvSeries_CoefNorm_continuous_wt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ConvSeries
open CoefNorm
namespace GlobalTheory.ConvSeries
theorem _root_.solution (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : SchwartzMap E ℂ) (j : ℕ) :
    ‖coef b c (⇑h) j‖ ≤ ∫ a, ‖wt b c (⇑h) a‖ * ‖a‖ ^ j := by
  unfold coef
  refine (norm_integral_le_integral_norm _).trans ?_
  have hw : Continuous (wt b c (⇑h)) := continuous_wt b c _ h.continuous
  have hint : Integrable (fun a : E => ‖a‖ ^ j * ‖h a‖) := h.integrable_pow_mul volume j
  have hint2 : Integrable (fun a : E => ‖wt b c (⇑h) a‖ * ‖a‖ ^ j) := by
    refine hint.mono' ((hw.norm.mul (continuous_norm.pow j)).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun a => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_wt_le b c hb hc _ a) (by positivity)
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => norm_nonneg _) hint2
    (Filter.Eventually.of_forall fun a => ?_)
  simp only [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_powForm_le j a) (norm_nonneg _)
end GlobalTheory.ConvSeries
