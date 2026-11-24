-- Prove2me | solution 1 for GlobalTheory.GrassModel.SuperTrace.msg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:27:52.733836+00:00
-- url     : https://prove2.me/submissions/f15f7af5-8bf6-4b9d-b5d9-3d9bed18f8f6

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_VecMulVecComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TracePowGrassmannBlockCurvatureSupertraceZero
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_sg_sum
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_sg_mul

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
theorem _root_.solution {r s t : Type*} [Fintype s] {m l : ℕ} {M : Matrix r s (Big n)}
    {N : Matrix s t (Big n)} (hM : MSg m M) (hN : MSg l N) : MSg (m + l) (M * N) := by
  intro i j; rw [Matrix.mul_apply]; exact sg_sum _ _ _ fun k _ => sg_mul (hM i k) (hN k j)
end GlobalTheory.GrassModel.SuperTrace
