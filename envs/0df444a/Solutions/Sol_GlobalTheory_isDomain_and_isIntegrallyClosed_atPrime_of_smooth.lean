-- Prove2me | solution 1 for GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:19:03.213141+00:00
-- url     : https://prove2.me/submissions/4c06e96f-ecb3-4185-8ce0-3059a8a27da2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization
import Theorems.Thm_GlobalTheory_isIntegrallyClosed_mvPolynomial_fin
import Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_etale

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
theorem _root_.solution (A : Type*) {B : Type*} [CommRing A]
    [CommRing B] [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Smooth A B]
    (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  obtain ⟨f, hfm, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := p)
  have := isIntegrallyClosed_mvPolynomial_fin A n
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers f)
    (Localization.Away f) p ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_etale (MvPolynomial (Fin n) A) q _) Bp
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]
end GlobalTheory
