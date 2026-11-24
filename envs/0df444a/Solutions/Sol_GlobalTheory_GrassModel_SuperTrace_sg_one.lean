-- Prove2me | solution 1 for GlobalTheory.GrassModel.SuperTrace.sg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:54:00.483008+00:00
-- url     : https://prove2.me/submissions/00540869-ba0c-477e-a1b1-c20943be566f

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
theorem _root_.solution : Sg 0 (1 : Big n) := by intro a; simp
end GlobalTheory.GrassModel.SuperTrace
