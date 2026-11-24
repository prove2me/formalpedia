-- Prove2me | solution 1 for GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:42.089612+00:00
-- url     : https://prove2.me/submissions/95e0fa9f-4502-42f6-95c4-baca368451af

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap

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
theorem _root_.solution (A : Type*) {B : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (hA : ∀ (q : Ideal A) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  obtain ⟨_, _⟩ := hA (p.comap (algebraMap A B))
  exact isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap (A := A) p
    (Localization.AtPrime (p.comap (algebraMap A B))) Bp
end GlobalTheory
