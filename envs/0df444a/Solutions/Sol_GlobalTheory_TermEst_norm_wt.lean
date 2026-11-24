-- Prove2me | solution 1 for GlobalTheory.TermEst.norm_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:28:47.991841+00:00
-- url     : https://prove2.me/submissions/c9434b02-ddba-4327-9acc-5b2b0c04ee65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianConvolutionSeriesCoefficientDescFactoria

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.TermEst
namespace GlobalTheory.TermEst
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b c : ℝ) (h : E → ℂ) (a : E) :
    ‖GlobalTheory.ConvSeries.wt b c h a‖ = Real.exp (-((b + c) * ‖a‖ ^ 2)) * ‖h a‖ := by
  simp only [GlobalTheory.ConvSeries.wt, norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [mul_comm (Real.exp _) ‖h a‖, mul_assoc, ← Real.exp_add]
  ring_nf
end GlobalTheory.TermEst
