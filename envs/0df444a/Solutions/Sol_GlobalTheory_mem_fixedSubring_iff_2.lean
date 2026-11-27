-- Prove2me | solution 2 for GlobalTheory.mem_fixedSubring_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:40:43.976257+00:00
-- url     : https://prove2.me/submissions/e92f2930-d150-477d-a92e-d04ebf034353

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (A G : Type*) [CommRing A] [Group G] [MulSemiringAction G A]
namespace GlobalTheory
theorem _root_.solution {a : A} : a ∈ FixedPoints.subring A G ↔ ∀ g : G, g • a = a :=
  Iff.rfl
end GlobalTheory
