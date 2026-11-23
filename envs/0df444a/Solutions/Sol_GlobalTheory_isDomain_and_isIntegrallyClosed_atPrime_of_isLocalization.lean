-- Prove2me | solution 1 for GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:50.505803+00:00
-- url     : https://prove2.me/submissions/96b1be32-d1b6-4107-a4b9-3bb062a0b235

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
theorem _root_.solution {B : Type*} [CommRing B]
    (M : Submonoid B) (T : Type*) [CommRing T] [Algebra B T] [IsLocalization M T]
    (p : Ideal B) [hp : p.IsPrime] (hM : Disjoint (M : Set B) (p : Set B))
    (h : ∀ (q : Ideal T) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (Bp : Type*) [CommRing Bp] [Algebra B Bp] [IsLocalization.AtPrime Bp p] :
    IsDomain Bp ∧ IsIntegrallyClosed Bp := by
  have hq : (p.map (algebraMap B T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M T p hp hM
  have hc : (p.map (algebraMap B T)).comap (algebraMap B T) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint M T hp hM
  have h1 := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime (p.map (algebraMap B T))) (p.map (algebraMap B T))
  have h2 : IsLocalization p.primeCompl (Localization.AtPrime (p.map (algebraMap B T))) := by
    convert h1 using 1
    ext x
    simp [Ideal.primeCompl, hc]
  obtain ⟨h3, h4⟩ := h (p.map (algebraMap B T))
  let e : Localization.AtPrime (p.map (algebraMap B T)) ≃ₐ[B] Bp :=
    IsLocalization.algEquiv p.primeCompl _ _
  exact ⟨e.symm.injective.isDomain _, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩
end GlobalTheory
