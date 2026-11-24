-- Prove2me | solution 1 for GlobalTheory.isReduced_of_smooth_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:27:13.562571+00:00
-- url     : https://prove2.me/submissions/66031d91-3358-4bd7-9408-af63e662daa0

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
theorem _root_.solution (A B : Type*) [CommRing A] [CommRing B]
    [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Smooth A B] : IsReduced B :=
  isReduced_ofLocalizationMaximal B fun p _ ↦
    have := (isDomain_and_isIntegrallyClosed_atPrime_of_smooth A p (Localization.AtPrime p)).1
    inferInstance
end GlobalTheory
