-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.PhiLine.line_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:21:46.305797+00:00
-- url     : https://prove2.me/submissions/9bb1ab3e-e0f0-4cf5-82ed-8a70c39c9651

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeWeightTwoKernelPhiLineContinuousIntegrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex MeasureTheory
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.PhiLine
namespace GlobalTheory.HeckeTwo.PhiLine
theorem _root_.solution (t y : ℝ) (hy : y ≠ 0) : ((t : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hy this
end GlobalTheory.HeckeTwo.PhiLine
