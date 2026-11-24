-- Prove2me | solution 1 for GlobalTheory.GramCount.ip_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:53:50.483633+00:00
-- url     : https://prove2.me/submissions/5ced514b-c91f-4368-804a-29ffc67d3d9f

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
theorem _root_.solution (y : Fin n → A) : ip c 0 y = 0 := by
  simp [ip]
end GlobalTheory.GramCount
