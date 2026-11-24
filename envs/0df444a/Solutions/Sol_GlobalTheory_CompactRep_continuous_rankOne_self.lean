-- Prove2me | solution 1 for GlobalTheory.CompactRep.continuous_rankOne_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:16:04.730813+00:00
-- url     : https://prove2.me/submissions/e3549d63-0d38-424d-b79b-5b6efe8a02ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CompactUnitaryFiniteInvariantSubspace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompactRep
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace GlobalTheory.CompactRep
theorem _root_.solution : Continuous fun w : H => rankOne ℂ w w := by
  have h : (fun w : H => rankOne ℂ w w) =
      fun w => ContinuousLinearMap.smulRightL ℂ H H (innerSL ℂ w) w := by
    funext w
    ext z
    simp [rankOne_apply]
  rw [h]
  exact (ContinuousLinearMap.smulRightL ℂ H H).continuous₂.comp
    ((innerSL ℂ).continuous.prodMk continuous_id)
end GlobalTheory.CompactRep
