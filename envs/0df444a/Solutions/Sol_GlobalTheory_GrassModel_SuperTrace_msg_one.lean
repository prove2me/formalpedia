-- Prove2me | solution 1 for GlobalTheory.GrassModel.SuperTrace.msg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:10:56.538811+00:00
-- url     : https://prove2.me/submissions/66eb85f5-1964-4c5b-99ad-3fd71535ba9a

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_VecMulVecComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TracePowGrassmannBlockCurvatureSupertraceZero
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_sg_zero
import Theorems.Thm_GlobalTheory_GrassModel_SuperTrace_sg_one

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
theorem _root_.solution {r : Type*} [Fintype r] [DecidableEq r] : MSg 0 (1 : Matrix r r (Big n)) := by
  intro i j; rw [Matrix.one_apply]; split_ifs
  · exact sg_one
  · exact sg_zero 0
end GlobalTheory.GrassModel.SuperTrace
