-- Prove2me | solution 1 for GlobalTheory.IterativeScalingBound.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:57:30.457858+00:00
-- url     : https://prove2.me/submissions/ac4ec1be-fb28-4f82-b771-d61d9c1418b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerAlt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IterativeScalingBound
namespace GlobalTheory.IterativeScalingBound
theorem _root_.solution (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have e : w ^ 2 - 1 = (w - 1) * (2 + (w - 1)) := by ring
  rw [e, norm_mul]
  have h2 : (3/2 : ℝ) ≤ ‖2 + (w - 1)‖ := by
    have t := norm_sub_le (2 + (w - 1)) (w - 1)
    have e2 : (2 + (w - 1)) - (w - 1) = (2 : ℂ) := by ring
    rw [e2] at t
    have : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  have h0 : 0 ≤ ‖w - 1‖ := norm_nonneg _
  nlinarith
end GlobalTheory.IterativeScalingBound
