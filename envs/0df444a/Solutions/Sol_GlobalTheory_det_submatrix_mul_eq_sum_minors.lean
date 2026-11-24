-- Prove2me | solution 1 for GlobalTheory.det_submatrix_mul_eq_sum_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:42:40.556258+00:00
-- url     : https://prove2.me/submissions/3f90e57c-6964-4464-b99c-71eeeb214d1e

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
variable {R : Type*} [CommRing R]
namespace GlobalTheory
theorem _root_.solution {l n o : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix l n R) (B : Matrix n o R) (r : Fin i → l) (c : Fin i → o) :
    ((A * B).submatrix r c).det = ∑ S : Set.powersetCard n i,
      (A.submatrix r (subsetEnum S)).det * (B.submatrix (subsetEnum S) c).det := by
  rw [submatrix_mul A B r id c Function.bijective_id, det_mul_eq_sum_minors]
  rfl
end GlobalTheory
