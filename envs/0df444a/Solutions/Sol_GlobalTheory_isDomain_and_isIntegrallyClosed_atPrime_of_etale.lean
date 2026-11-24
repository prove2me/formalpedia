-- Prove2me | solution 1 for GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:13:02.854139+00:00
-- url     : https://prove2.me/submissions/e536b0bb-3dee-4a38-be57-613d8a0d1b03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_isIntegrallyClosedIn_pi
import Theorems.Thm_GlobalTheory_isIntegrallyClosedIn_tensor_of_smooth

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
    [CommRing B] [IsDomain A] [IsIntegrallyClosed A] [Algebra A B] [Algebra.Etale A B]
    (p : Ideal B) [hp : p.IsPrime]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  let L := FractionRing A
  have h1 : IsIntegrallyClosedIn B (B ⊗[A] L) := isIntegrallyClosedIn_tensor_of_smooth
  have := Algebra.FormallyUnramified.finite_of_free L (L ⊗[A] B)
  have := Algebra.FormallyUnramified.isReduced_of_field L (L ⊗[A] B)
  have : IsArtinianRing (L ⊗[A] B) := isArtinian_of_tower L inferInstance
  let e := (Algebra.TensorProduct.comm A B L).toRingEquiv
  have : IsArtinianRing (B ⊗[A] L) := e.symm.isArtinianRing
  have : IsReduced (B ⊗[A] L) := isReduced_of_injective e e.injective
  letI (m : MaximalSpectrum (B ⊗[A] L)) : Field ((B ⊗[A] L) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  have := (((IsArtinianRing.equivPi (B ⊗[A] L)).restrictScalars B).isIntegrallyClosedIn).mp h1
  exact isDomain_and_isIntegrallyClosed_atPrime_of_isIntegrallyClosedIn_pi
    (fun m : MaximalSpectrum (B ⊗[A] L) ↦ (B ⊗[A] L) ⧸ m.asIdeal) p Bp
end GlobalTheory
