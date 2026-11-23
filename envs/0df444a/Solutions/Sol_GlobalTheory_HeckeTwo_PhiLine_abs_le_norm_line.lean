-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.PhiLine.abs_le_norm_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:29.795123+00:00
-- url     : https://prove2.me/submissions/5373ab8d-9b34-42b4-8629-e80f254a5f0d

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
theorem _root_.solution (t y : ℝ) : |y| ≤ ‖((t : ℂ) + (y : ℂ) * Complex.I)‖ := by
  have := Complex.abs_im_le_norm ((t : ℂ) + (y : ℂ) * Complex.I)
  simpa using this
end GlobalTheory.HeckeTwo.PhiLine
