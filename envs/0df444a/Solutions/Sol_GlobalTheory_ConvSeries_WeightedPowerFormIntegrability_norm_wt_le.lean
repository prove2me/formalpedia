-- Prove2me | solution 1 for GlobalTheory.ConvSeries.WeightedPowerFormIntegrability.norm_wt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:56:12.14626+00:00
-- url     : https://prove2.me/submissions/f36a46b4-43a1-4de7-afd2-2799699ac53a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumGaussianConvolutionSeriesTermIntegral
import Theorems.Thm_GlobalTheory_ConvSeries_WeightedPowerFormIntegrability_norm_cexp_neg_ofReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.ConvSeries GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
open GlobalTheory.ConvSeries
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
theorem _root_.solution (b c : ℝ) (h : SchwartzMap E ℂ) (a : E) :
    ‖wt b c h a‖ ≤ SchwartzMap.seminorm ℝ 0 0 h * Real.exp (-((b + c) * ‖a‖ ^ 2)) := by
  unfold wt
  rw [norm_mul, norm_mul, norm_cexp_neg_ofReal, norm_cexp_neg_ofReal]
  have h1 := SchwartzMap.norm_le_seminorm ℝ h a
  have hs : Real.exp (-((b + c) * ‖a‖ ^ 2)) =
      Real.exp (-(b * ‖a‖ ^ 2)) * Real.exp (-(c * ‖a‖ ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hs]
  calc Real.exp (-(b * ‖a‖ ^ 2)) * ‖h a‖ * Real.exp (-(c * ‖a‖ ^ 2))
      = ‖h a‖ * (Real.exp (-(b * ‖a‖ ^ 2)) * Real.exp (-(c * ‖a‖ ^ 2))) := by ring
    _ ≤ SchwartzMap.seminorm ℝ 0 0 h * (Real.exp (-(b * ‖a‖ ^ 2)) * Real.exp (-(c * ‖a‖ ^ 2))) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
end GlobalTheory.ConvSeries.WeightedPowerFormIntegrability
