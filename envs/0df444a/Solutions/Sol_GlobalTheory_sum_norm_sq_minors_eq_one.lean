-- Prove2me | solution 1 for GlobalTheory.sum_norm_sq_minors_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:19.4521+00:00
-- url     : https://prove2.me/submissions/cfd0b100-553e-4a5b-a55a-7da1429b05ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Theorems.Thm_GlobalTheory_det_mul_conjTranspose_eq_sum_norm_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
namespace GlobalTheory
theorem _root_.solution (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) :
    ∑ S : Set.powersetCard n i, ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2 = 1 := by
  have h := det_mul_conjTranspose_eq_sum_norm_sq A
  rw [hA, det_one] at h
  exact_mod_cast h.symm
end GlobalTheory
