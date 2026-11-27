-- Prove2me | solution 1 for GlobalTheory.isIntegrallyClosed_fixedSubring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:40:06.371748+00:00
-- url     : https://prove2.me/submissions/669b3484-40c2-44af-925a-292d9b1d9c91

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_isIntegrallyClosed_of_isInvariant

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
theorem _root_.solution [IsDomain A] [IsIntegrallyClosed A] :
    IsIntegrallyClosed (FixedPoints.subring A G) :=
  (isIntegrallyClosed_of_isInvariant A G _).2
end GlobalTheory
