-- Prove2me | solution 1 for GlobalTheory.GramCount.ip_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:54:57.825054+00:00
-- url     : https://prove2.me/submissions/f55dfbb5-c863-44ba-88d8-c03ad7e82d51

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
theorem _root_.solution (x y y' : Fin n → A) : ip c x (y + y') = ip c x y + ip c x y' := by
  simp only [ip, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
end GlobalTheory.GramCount
