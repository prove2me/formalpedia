-- Prove2me | solution 1 for GlobalTheory.T.regular_local_ring_normal_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:56:03.36783+00:00
-- url     : https://prove2.me/submissions/36fb4e96-6869-46bf-a07b-db14951e7cf6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomainStatement
import Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_of_isRegularLocalRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (T : Type) [CommRing T] [IsRegularLocalRing T], IsDomain T ∧ IsIntegrallyClosed T := by
  first | exact @GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing | exact GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing | (intros; apply GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing <;> assumption)
end _root_.GlobalTheory.T
