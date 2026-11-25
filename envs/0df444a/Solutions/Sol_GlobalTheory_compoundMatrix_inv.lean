-- Prove2me | solution 1 for GlobalTheory.compoundMatrix_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:03:00.045668+00:00
-- url     : https://prove2.me/submissions/46c9b53b-51b0-4345-bae3-becf281abe56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
import Theorems.Thm_GlobalTheory_compoundMatrix_mul
import Theorems.Thm_GlobalTheory_compoundMatrix_one

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
variable [Fintype n]
namespace GlobalTheory
theorem _root_.solution (k : ℕ) {A : Matrix n n ℂ} (hA : IsUnit A) :
    (compoundMatrix k A)⁻¹ = compoundMatrix k A⁻¹ := by
  let _ := hA.invertible
  refine inv_eq_left_inv ?_
  rw [← compoundMatrix_mul, inv_mul_of_invertible, compoundMatrix_one]
end GlobalTheory
