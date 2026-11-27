-- Prove2me | solution 1 for GlobalTheory.isIntegrallyClosed_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:40:59.270031+00:00
-- url     : https://prove2.me/submissions/d35d8a9c-2ea1-49c7-b30b-789dcfa51af8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
universe u
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (A B : Type*) [CommRing A] [CommRing B] [IsDomain A]
    [IsIntegrallyClosed A] [Algebra A B] [Algebra.Smooth A B] [IsDomain B] :
    IsIntegrallyClosed B :=
  IsIntegrallyClosed.of_localization_maximal fun p _ _ ↦
    (isDomain_and_isIntegrallyClosed_atPrime_of_smooth A p _).2
end GlobalTheory
