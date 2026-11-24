-- Prove2me | solution 1 for GlobalTheory.T.isDomain_of_isIntegrallyClosed_of_isReduced_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:26:58.973241+00:00
-- url     : https://prove2.me/submissions/5fc331e5-2748-4500-aac2-27fefde0c3b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsDomainOfIsIntegrallyClosedOfIsReduced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsDomainOfIsIntegrallyClosedOfIsReducedStatement
import Theorems.Thm_GlobalTheory_isDomain_of_isIntegrallyClosed_of_isReduced


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsReduced R], IsIntegrallyClosed R → IsDomain R := by
  first | exact @GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced | exact GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced | (intros; apply GlobalTheory.isDomain_of_isIntegrallyClosed_of_isReduced <;> assumption)
end _root_.GlobalTheory.T
