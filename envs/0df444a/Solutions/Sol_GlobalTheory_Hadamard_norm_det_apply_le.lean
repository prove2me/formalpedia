-- Prove2me | solution 1 for GlobalTheory.Hadamard.norm_det_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:05:20.089808+00:00
-- url     : https://prove2.me/submissions/55f21e1f-2922-43df-8f0e-1b80d830cd26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Theorems.Thm_GlobalTheory_Hadamard_re_det_gram_le_prod
import Theorems.Thm_GlobalTheory_Hadamard_norm_det_apply_sq_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
open scoped InnerProductSpace ComplexOrder
open GlobalTheory GlobalTheory.Hadamard
variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace GlobalTheory.Hadamard
theorem _root_.solution (φ : ι → E →L[𝕜] 𝕜) (x : ι → E) :
    ‖(of fun j k => φ j (x k)).det‖ ≤ (∏ k, ‖x k‖) * ∏ j, ‖φ j‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, ← Finset.prod_pow, ← Finset.prod_pow]
  exact (norm_det_apply_sq_le φ x).trans
    (mul_le_mul_of_nonneg_right (re_det_gram_le_prod x) (by positivity))
end GlobalTheory.Hadamard
