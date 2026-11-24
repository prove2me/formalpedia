-- Prove2me | solution 1 for GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_smooth_of_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:27:12.195968+00:00
-- url     : https://prove2.me/submissions/ff794010-253a-4a95-85e1-dedc6a01d853

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Theorems.Thm_GlobalTheory_isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization
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
theorem _root_.solution {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.Smooth A B] (p : Ideal B) [hp : p.IsPrime]
    (Ap : Type*) [CommRing Ap] [Algebra A Ap]
    [IsLocalization.AtPrime Ap (p.comap (algebraMap A B))] [IsDomain Ap] [IsIntegrallyClosed Ap]
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  let M := (p.comap (algebraMap A B)).primeCompl
  letI : Algebra B (Ap ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid B M) (Ap ⊗[A] B) :=
    IsLocalization.tensorRight _ _
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization
    (Algebra.algebraMapSubmonoid B M) (Ap ⊗[A] B) p ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_smooth Ap q _) Bp
  rw [Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ h
  exact ha h
end GlobalTheory
