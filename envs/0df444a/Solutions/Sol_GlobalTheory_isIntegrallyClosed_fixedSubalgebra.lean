-- Prove2me | solution 1 for GlobalTheory.isIntegrallyClosed_fixedSubalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:38:48.530113+00:00
-- url     : https://prove2.me/submissions/1928440c-2a21-4b59-96ce-4b66bc394d42

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
theorem _root_.solution (R : Type*) [CommRing R] [Algebra R A]
    [SMulCommClass G R A] [IsDomain A] [IsIntegrallyClosed A] :
    IsIntegrallyClosed (FixedPoints.subalgebra R A G) :=
  (isIntegrallyClosed_of_isInvariant A G _).2
end GlobalTheory
