-- Prove2me | solution 1 for GlobalTheory.sum_abs_realEmbeddings
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:27.706364+00:00
-- url     : https://prove2.me/submissions/66e0bef2-190e-4c0f-aa25-2c4fbf63d9c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_bijective_ofRealHom_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory
theorem _root_.solution (x : F) :
    ∑ σ : F →+* ℝ, |σ x| = ∑ σ : F →+* ℂ, ‖σ x‖ := by
  rw [← (bijective_ofRealHom_comp F).sum_comp (fun φ => ‖φ x‖)]
  simp
end GlobalTheory
