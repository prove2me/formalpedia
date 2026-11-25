-- Prove2me | solution 1 for GlobalTheory.GramCount.ip_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:55:37.478539+00:00
-- url     : https://prove2.me/submissions/32ac923a-481c-4102-932a-00d9f290b42b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.GramCount
variable {A : Type} [CommRing A]
variable (c : A →+* A) {n : ℕ}
namespace GlobalTheory.GramCount
theorem _root_.solution (x x' y : Fin n → A) : ip c (x + x') y = ip c x y + ip c x' y := by
  simp only [ip, Pi.add_apply, add_mul, Finset.sum_add_distrib]
end GlobalTheory.GramCount
