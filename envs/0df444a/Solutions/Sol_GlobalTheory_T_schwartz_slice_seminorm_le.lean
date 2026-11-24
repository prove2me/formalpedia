-- Prove2me | solution 1 for GlobalTheory.T.schwartz_slice_seminorm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:22:17.976262+00:00
-- url     : https://prove2.me/submissions/71697d0d-89d0-4495-a8d1-7c33db95e83c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSliceSeminormLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSliceSeminormLeStatement
import Theorems.Thm_GlobalTheory_SchwartzFstOp_norm_pow_mul_seminorm_sliceCLM_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (j k n : ℕ), ‖x'‖ ^ k * SchwartzMap.seminorm ℂ j n (sliceCLM x' f) ≤ SchwartzMap.seminorm ℂ (j + k) n f := by
  first | exact @GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le | exact GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le | (intros; apply GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le <;> assumption)
end _root_.GlobalTheory.T
