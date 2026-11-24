-- Prove2me | solution 1 for GlobalTheory.det_mul_conjTranspose_eq_sum_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:39.138484+00:00
-- url     : https://prove2.me/submissions/67b5e2ba-4861-42c3-b75a-b36e032ac9e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Theorems.Thm_GlobalTheory_det_mul_eq_sum_minors

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
theorem _root_.solution (A : Matrix (Fin i) n 𝕜) :
    (A * Aᴴ).det =
      ((∑ S : Set.powersetCard n i, ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2 : ℝ) : 𝕜) := by
  rw [det_mul_eq_sum_minors]
  push_cast
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← conjTranspose_submatrix, det_conjTranspose, RCLike.star_def, RCLike.mul_conj]
end GlobalTheory
