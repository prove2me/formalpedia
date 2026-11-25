-- Prove2me | solution 1 for GlobalTheory.compoundMatrix_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:58:31.871525+00:00
-- url     : https://prove2.me/submissions/5ef9cc86-1ed6-4d13-8c68-35c0c6be0a28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_det_submatrix_mul_eq_sum_minors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {l n o : Type*} [LinearOrder l] [LinearOrder n] [LinearOrder o]
namespace GlobalTheory
theorem _root_.solution [Fintype n] (k : ℕ) (A : Matrix l n ℂ) (A' : Matrix n o ℂ) :
    compoundMatrix k (A * A') = compoundMatrix k A * compoundMatrix k A' := by
  ext I J
  exact det_submatrix_mul_eq_sum_minors A A' _ _
end GlobalTheory
