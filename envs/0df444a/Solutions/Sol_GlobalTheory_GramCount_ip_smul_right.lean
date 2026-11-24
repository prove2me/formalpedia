-- Prove2me | solution 1 for GlobalTheory.GramCount.ip_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:36:36.698257+00:00
-- url     : https://prove2.me/submissions/51b74097-4687-479a-ba36-55278de813b3

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
theorem _root_.solution (a : A) (x y : Fin n → A) : ip c x (a • y) = c a * ip c x y := by
  unfold ip
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  ring
end GlobalTheory.GramCount
