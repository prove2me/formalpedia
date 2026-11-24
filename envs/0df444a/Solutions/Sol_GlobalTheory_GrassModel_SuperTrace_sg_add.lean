-- Prove2me | solution 1 for GlobalTheory.GrassModel.SuperTrace.sg_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:53:56.965295+00:00
-- url     : https://prove2.me/submissions/09aca35d-b7ed-4594-8fed-8a5b586cd600

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
theorem _root_.solution {m : ℕ} {z w : Big n} (hz : Sg m z) (hw : Sg m w) : Sg m (z + w) := by
  intro a; rw [mul_add, hz a, hw a, add_mul, mul_add]
end GlobalTheory.GrassModel.SuperTrace
