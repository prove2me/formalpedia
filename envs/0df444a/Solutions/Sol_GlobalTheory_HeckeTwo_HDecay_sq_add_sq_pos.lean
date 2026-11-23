-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.HDecay.sq_add_sq_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:35.433978+00:00
-- url     : https://prove2.me/submissions/eeaef227-2735-4460-8127-73e81b537261

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierTransformRapidDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped ContDiff FourierTransform
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.HDecay
variable (σ : ℂ) (y : ℝ)
variable {y}
namespace GlobalTheory.HeckeTwo.HDecay
theorem _root_.solution (hy : y ≠ 0) (t : ℝ) : 0 < t ^ 2 + y ^ 2 := by
  have : 0 < y ^ 2 := lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hy))
  positivity
end GlobalTheory.HeckeTwo.HDecay
