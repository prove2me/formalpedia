-- Prove2me | solution 1 for GlobalTheory.GrassModel.SuperTrace.sg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:53:59.117482+00:00
-- url     : https://prove2.me/submissions/40d1bb92-25a6-4c14-bf18-c1da50f3d9d1

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
theorem _root_.solution {m l : ℕ} {z w : Big n} (hz : Sg m z) (hw : Sg l w) : Sg (m + l) (z * w) := by
  intro a
  have hc : Commute ((-1 : Big n) ^ l) z := (Commute.neg_one_left z).pow_left l
  rw [← mul_assoc, hz a, mul_assoc, mul_assoc, hw a, pow_add, ← mul_assoc z, ← hc.eq]
  simp only [mul_assoc]
end GlobalTheory.GrassModel.SuperTrace
