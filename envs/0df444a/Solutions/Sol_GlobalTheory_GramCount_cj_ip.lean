-- Prove2me | solution 1 for GlobalTheory.GramCount.cj_ip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:55:02.876447+00:00
-- url     : https://prove2.me/submissions/d256e50e-b8f3-4735-b6fa-6be97181d0c6

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
theorem _root_.solution (hc : ∀ u, c (c u) = u) (x y : Fin n → A) : c (ip c x y) = ip c y x := by
  unfold ip
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hc, mul_comm]
end GlobalTheory.GramCount
