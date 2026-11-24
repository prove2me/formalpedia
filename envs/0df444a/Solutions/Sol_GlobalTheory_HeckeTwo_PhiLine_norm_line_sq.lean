-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.PhiLine.norm_line_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:21:47.332165+00:00
-- url     : https://prove2.me/submissions/5c772a2e-3393-4f3f-9987-8faa845b8532

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
theorem _root_.solution (t y : ℝ) : ‖((t : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2 = t ^ 2 + y ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp; ring
end GlobalTheory.HeckeTwo.PhiLine
