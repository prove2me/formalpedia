-- Prove2me | solution 1 for GlobalTheory.heightOneOrd_vw_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:59:09.863905+00:00
-- url     : https://prove2.me/submissions/ea3f2521-33fb-450c-a4b1-caa7fc87bbe9

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
theorem _root_.solution (x : K) (n : ℤ) :
    heightOneOrd_vw p hp (x ^ n) = n * heightOneOrd_vw p hp x := by
  rw [heightOneOrd_vw, map_zpow₀, WithZero.log_zpow]
  rfl
end GlobalTheory
