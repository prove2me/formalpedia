-- Prove2me | solution 1 for GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:30.439811+00:00
-- url     : https://prove2.me/submissions/eeacd6b4-ab6c-4959-8e6d-f1f0ff72350f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo

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
theorem _root_.solution {B : Type*} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp :=
  ⟨IsLocalization.isDomain_of_le_nonZeroDivisors Bp p.primeCompl_le_nonZeroDivisors,
    isIntegrallyClosed_of_isLocalization Bp p.primeCompl p.primeCompl_le_nonZeroDivisors⟩
end GlobalTheory
