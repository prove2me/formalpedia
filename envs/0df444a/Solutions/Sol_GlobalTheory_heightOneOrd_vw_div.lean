-- Prove2me | solution 1 for GlobalTheory.heightOneOrd_vw_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:08:32.115227+00:00
-- url     : https://prove2.me/submissions/9e622d95-b6c5-4751-b3ef-557662259d29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Theorems.Thm_GlobalTheory_heightOneOrd_vw_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] [IsDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable {K}
variable [IsNoetherianRing A]
variable (p : Ideal A) [p.IsPrime] (hp : p.height = 1)
namespace GlobalTheory
theorem _root_.solution {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    heightOneOrd_vw p hp (x / y) = heightOneOrd_vw p hp x - heightOneOrd_vw p hp y := by
  rw [div_eq_mul_inv, heightOneOrd_vw_mul p hp hx (inv_ne_zero hy), heightOneOrd_vw_inv,
    sub_eq_add_neg]
end GlobalTheory
