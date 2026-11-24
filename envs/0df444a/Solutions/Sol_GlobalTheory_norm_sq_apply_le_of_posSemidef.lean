-- Prove2me | solution 1 for GlobalTheory.norm_sq_apply_le_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:28:09.095141+00:00
-- url     : https://prove2.me/submissions/b24af233-02f1-4a99-9e7c-a7cde7e51361

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_OneLeDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder MatrixOrder
open GlobalTheory
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
variable [DecidableEq n]
omit [Fintype n] [DecidableEq n]
namespace GlobalTheory
theorem _root_.solution {A : Matrix n n 𝕜} (hA : A.PosSemidef) (i j : n) :
    ‖A i j‖ ^ 2 ≤ RCLike.re (A i i) * RCLike.re (A j j) := by
  have h := (hA.submatrix ![i, j]).det_nonneg
  rw [det_fin_two] at h
  simp only [submatrix_apply, cons_val_zero, cons_val_one, sub_nonneg] at h
  have h2 := (RCLike.le_iff_re_im.mp h).1
  have hi := (RCLike.nonneg_iff.mp (hA.diag_nonneg (i := i))).2
  rw [← hA.1.apply j i, RCLike.star_def, RCLike.mul_conj, RCLike.mul_re (A i i), hi] at h2
  norm_cast at h2
  simpa using h2
end GlobalTheory
