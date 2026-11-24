-- Prove2me | solution 1 for GlobalTheory.UnitNormRealPartBound.re_gt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:03:09.715557+00:00
-- url     : https://prove2.me/submissions/46fc5f20-7264-42d6-8d31-cbb24019b9bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ReGt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitNormRealPartBound
namespace GlobalTheory.UnitNormRealPartBound
theorem _root_.solution {w : ℂ} (hw : ‖w‖ = 1) (h : ‖w - 1‖ < 1 / 2) : 7 / 8 < w.re := by
  have h1 : ‖w - 1‖ ^ 2 < 1 / 4 := by nlinarith [norm_nonneg (w - 1)]
  have h2 : ‖w‖ ^ 2 = 1 := by rw [hw]; norm_num
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h1 h2
  simp at h1
  nlinarith
end GlobalTheory.UnitNormRealPartBound
