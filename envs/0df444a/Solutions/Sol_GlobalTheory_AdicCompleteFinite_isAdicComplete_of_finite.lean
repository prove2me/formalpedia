-- Prove2me | solution 1 for GlobalTheory.AdicCompleteFinite.isAdicComplete_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:09:27.547793+00:00
-- url     : https://prove2.me/submissions/fd84f4c7-9c25-4267-868a-7da4b5d9d2b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsAdicCompleteOfFinite
import Theorems.Thm_GlobalTheory_AdicCompleteFinite_isPrecomplete_of_finite
import Theorems.Thm_GlobalTheory_AdicCompleteFinite_isPrecomplete_of_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.AdicCompleteFinite
namespace GlobalTheory.AdicCompleteFinite
theorem _root_.solution (R S : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [CommRing S] [IsLocalRing S] [Algebra R S]
    [Module.Finite R S] : IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
  haveI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have hcomap : (maximalIdeal S).comap (algebraMap R S) = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal S))
  have hle : (maximalIdeal R).map (algebraMap R S) ≤ maximalIdeal S :=
    Ideal.map_le_iff_le_comap.mpr hcomap.ge
  have hrad : maximalIdeal S ≤ ((maximalIdeal R).map (algebraMap R S)).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hP, hprime⟩
    have h1 : maximalIdeal R ≤ P.comap (algebraMap R S) := Ideal.map_le_iff_le_comap.mp hP
    have h2 : P.comap (algebraMap R S) = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ hprime.ne_top) h1).symm
    have h3 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P
        (h2 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h3).ge
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  haveI : IsPrecomplete (maximalIdeal R) S := isPrecomplete_of_finite _
  haveI : IsPrecomplete ((maximalIdeal R).map (algebraMap R S)) S :=
    IsPrecomplete.map_algebraMap_iff.mpr this
  haveI : IsPrecomplete (maximalIdeal S) S := isPrecomplete_of_pow_le hle hk
  exact {}
end GlobalTheory.AdicCompleteFinite
