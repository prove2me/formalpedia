-- Prove2me | solution 1 for GlobalTheory.UnitWitt.conjTranspose_vecMulVec_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:18.600646+00:00
-- url     : https://prove2.me/submissions/b56779a9-9171-481e-abb9-2b4c98c5ab6e

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.UnitWitt
variable {E : Type} [Field E] [StarRing E] {r : ℕ}
namespace GlobalTheory.UnitWitt
theorem _root_.solution (w : Fin r → E) : (vecMulVec w (star w))ᴴ = vecMulVec w (star w) := by
  ext i j
  simp [vecMulVec, conjTranspose_apply, mul_comm]
end GlobalTheory.UnitWitt
