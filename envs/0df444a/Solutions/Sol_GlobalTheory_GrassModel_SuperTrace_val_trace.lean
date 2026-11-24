-- Prove2me | solution 1 for GlobalTheory.GrassModel.SuperTrace.val_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:09:29.695174+00:00
-- url     : https://prove2.me/submissions/c3048ecb-cb0b-4c06-aafc-95d54c57a68d

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
theorem _root_.solution {r : Type*} [Fintype r] (M : Matrix r r (EvenPart n)) :
    ((EvenPart n).val M.trace) = (M.map (EvenPart n).val).trace := by
  simp [Matrix.trace, map_sum]
end GlobalTheory.GrassModel.SuperTrace
