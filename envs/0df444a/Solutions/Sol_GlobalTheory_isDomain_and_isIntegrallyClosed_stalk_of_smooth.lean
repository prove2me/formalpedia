-- Prove2me | solution 1 for GlobalTheory.isDomain_and_isIntegrallyClosed_stalk_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:42.848432+00:00
-- url     : https://prove2.me/submissions/9641b121-b505-4cd7-a0b1-fabb07d44bd4

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
open AlgebraicGeometry
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) [IsDomain (Y.presheaf.stalk (f x))] [IsIntegrallyClosed (Y.presheaf.stalk (f x))] :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hx, e, -⟩ := Smooth.exists_isStandardSmooth f x
  have hs := f.smooth_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  letI := Y.presheaf.algebra_section_stalk (⟨f x, e hx⟩ : U)
  have h1 := hV.isLocalization_stalk ⟨x, hx⟩
  have h2 := hU.isLocalization_stalk ⟨f x, e hx⟩
  have h3 : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap (algebraMap Γ(Y, U) Γ(X, V)) =
      (hU.primeIdealOf ⟨f x, e hx⟩).asIdeal :=
    congrArg PrimeSpectrum.asIdeal (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV e hx)
  have h4 : IsLocalization.AtPrime (Y.presheaf.stalk (f x))
      ((hV.primeIdealOf ⟨x, hx⟩).asIdeal.comap (algebraMap Γ(Y, U) Γ(X, V))) := by
    convert h2
  exact isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap (A := Γ(Y, U))
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
end GlobalTheory
