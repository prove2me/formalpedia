-- Prove2me | solution 1 for GlobalTheory.ConvSeries.CoefNorm.norm_wt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:44:25.194423+00:00
-- url     : https://prove2.me/submissions/a3fcb73a-31c5-4e02-bfdd-37614cdf5ee5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormGaussianConvolutionSeriesCoefficientLeIntegr

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
open GlobalTheory.ConvSeries.CoefNorm
namespace GlobalTheory.ConvSeries.CoefNorm
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b c : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : E → ℂ) (a : E) : ‖wt b c h a‖ ≤ ‖h a‖ := by
  unfold wt
  rw [norm_mul, norm_mul, ← Complex.ofReal_neg, ← Complex.ofReal_neg, Complex.norm_exp_ofReal,
    Complex.norm_exp_ofReal]
  have e1 : Real.exp (-(b * ‖a‖ ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖a‖])
  have e2 : Real.exp (-(c * ‖a‖ ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖a‖])
  calc _ ≤ 1 * ‖h a‖ * 1 := by gcongr
    _ = _ := by ring
end GlobalTheory.ConvSeries.CoefNorm
