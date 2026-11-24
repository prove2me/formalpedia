-- Prove2me | solution 1 for GlobalTheory.det_mul_eq_sum_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:04.179102+00:00
-- url     : https://prove2.me/submissions/b0551b58-ce2c-4807-8a92-8b423fe9afa0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Theorems.Thm_GlobalTheory_alternatingMap_apply_eq_sum_minors

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
theorem _root_.solution {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
    (A : Matrix (Fin i) n R) (B : Matrix n (Fin i) R) :
    (A * B).det = ∑ S : Set.powersetCard n i,
      (A.submatrix id (subsetEnum S)).det * (B.submatrix (subsetEnum S) id).det := by
  classical
  have h := alternatingMap_apply_eq_sum_minors
    ((Matrix.detRowAlternating (n := Fin i) (R := R)).compLinearMap B.vecMulLinear) A
  have h0 : (A * B).det =
      ((Matrix.detRowAlternating (n := Fin i) (R := R)).compLinearMap B.vecMulLinear) A := rfl
  rw [h0, h]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [smul_eq_mul]
  congr 1
  rw [AlternatingMap.compLinearMap_apply]
  change Matrix.det _ = _
  congr 1
  ext a c
  simp [Matrix.vecMulLinear_apply, Matrix.single_one_vecMul]
end GlobalTheory
