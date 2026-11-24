-- Prove2me | solution 1 for GlobalTheory.GrassModel.SuperTrace.val_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:54:02.946716+00:00
-- url     : https://prove2.me/submissions/a6bdd400-0a80-4b9e-9089-9711cf7a6f8c

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
theorem _root_.solution {r : Type*} [Fintype r] [DecidableEq r] (M : Matrix r r (EvenPart n)) (k : ℕ) :
    (M ^ k).map (EvenPart n).val = (M.map (EvenPart n).val) ^ k :=
  map_pow ((EvenPart n).val.toRingHom.mapMatrix) M k
end GlobalTheory.GrassModel.SuperTrace
