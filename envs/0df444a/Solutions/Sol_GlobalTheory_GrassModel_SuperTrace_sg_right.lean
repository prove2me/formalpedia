-- Prove2me | solution 1 for GlobalTheory.GrassModel.SuperTrace.sg_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:54:01.569318+00:00
-- url     : https://prove2.me/submissions/921e75cf-1e6d-4e15-b27a-31bf0a4dbd54

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_VecMulVecComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TracePowGrassmannBlockCurvatureSupertraceZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open GlobalTheory GlobalTheory.GrassModel GlobalTheory.GrassModel.SuperTrace
variable {n : ℕ}
namespace GlobalTheory.GrassModel.SuperTrace
theorem _root_.solution (b : Fin n) : Sg 1 ((1 : Ext n) ⊗ₜ vec n b) := by
  intro a
  simp [Algebra.TensorProduct.tmul_mul_tmul, vec_mul_vec_comm n a b, TensorProduct.tmul_neg]
end GlobalTheory.GrassModel.SuperTrace
