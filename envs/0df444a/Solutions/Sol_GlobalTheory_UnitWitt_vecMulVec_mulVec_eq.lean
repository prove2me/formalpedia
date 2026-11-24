-- Prove2me | solution 1 for GlobalTheory.UnitWitt.vecMulVec_mulVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:05:09.056331+00:00
-- url     : https://prove2.me/submissions/71ada32f-c7f4-45fe-9543-879fef1af479

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
theorem _root_.solution (w v z : Fin r → E) : vecMulVec w v *ᵥ z = (v ⬝ᵥ z) • w := by
  ext i
  simp [mulVec, vecMulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
end GlobalTheory.UnitWitt
