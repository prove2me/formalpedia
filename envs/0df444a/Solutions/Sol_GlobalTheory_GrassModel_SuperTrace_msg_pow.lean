-- Prove2me | solution 1 for GlobalTheory.GrassModel.SuperTrace.msg_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:45:37.653261+00:00
-- url     : https://prove2.me/submissions/d6554775-f6c8-4254-b7e9-d0ffbbec6ea1

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_VecMulVecComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TracePowGrassmannBlockCurvatureSupertraceZero
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_msg_mul
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_msg_one

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
theorem _root_.solution {r : Type*} [Fintype r] [DecidableEq r] {M : Matrix r r (Big n)} (hM : MSg 1 M)
    (j : ℕ) : MSg j (M ^ j) := by
  induction j with
  | zero => simpa using (msg_one : MSg 0 (1 : Matrix r r (Big n)))
  | succ j ih => rw [pow_succ]; exact msg_mul ih hM
end GlobalTheory.GrassModel.SuperTrace
