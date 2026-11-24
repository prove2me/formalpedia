-- Prove2me | solution 1 for GlobalTheory.heightOneOrd_vw_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:59:07.616282+00:00
-- url     : https://prove2.me/submissions/33566eca-9331-44a7-b644-2c345924ee5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive

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
    heightOneOrd_vw p hp (x * y) = heightOneOrd_vw p hp x + heightOneOrd_vw p hp y := by
  rw [heightOneOrd_vw, map_mul,
    WithZero.log_mul ((map_ne_zero _).mpr hx) ((map_ne_zero _).mpr hy)]
  rfl
end GlobalTheory
