-- Prove2me | solution 1 for GlobalTheory.UnitWitt.star_dot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:19.317938+00:00
-- url     : https://prove2.me/submissions/df7dd356-7889-49de-8113-9acab791f70f

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
theorem _root_.solution (x y : Fin r → E) : star (star x ⬝ᵥ y) = star y ⬝ᵥ x := by
  simp [dotProduct, star_sum, mul_comm]
end GlobalTheory.UnitWitt
