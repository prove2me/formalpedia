-- Prove2me | solution 1 for IsRegularLocalRing.isPrime_span_singleton_and_isDiscreteValuationRing_localization_of_notMem_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d17fc60a-aa00-5962-ad19-2f892a4e5d5a

import Mathlib
import Theorems.Thm_IsRegularRing_uniqueFactorizationMonoid_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_isPrime_span_singleton_and_isDiscreteValuationRing_localization_of_notMem_sq
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open IsLocalRing

theorem solution
    (R : Type) [CommRing R] [IsDomain R] [IsRegularLocalRing R] [IsRegularRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) (hx0 : x ≠ 0) :
    ∃ hP : (Ideal.span {x}).IsPrime, (Ideal.span {x}).height = 1 ∧
      @IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {x}) (hp := hP)) _ _ := by
  classical
  haveI : UniqueFactorizationMonoid R := IsRegularRing.uniqueFactorizationMonoid_of_isLocalRing R
  have hxu : ¬ IsUnit x := (IsLocalRing.mem_maximalIdeal x).mp hx
  have hirr : Irreducible x := by
    refine ⟨hxu, fun a b hab => ?_⟩
    by_contra h
    push Not at h
    have ha : a ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal a).mpr h.1
    have hb : b ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal b).mpr h.2
    apply hx2
    rw [hab, pow_two]
    exact Ideal.mul_mem_mul ha hb
  have hprime : Prime x := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hP : (Ideal.span {x}).IsPrime := (Ideal.span_singleton_prime hx0).mpr hprime
  refine ⟨hP, ?_, ?_⟩
  · apply le_antisymm
    · haveI := hP
      exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) (Ideal.span {x})
        (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton _)
    · exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hx0)
  · haveI := hP
    haveI : IsNoetherianRing (Localization.AtPrime (Ideal.span {x})) :=
      IsLocalization.isNoetherianRing (Ideal.span {x}).primeCompl _ inferInstance
    have hinj : Function.Injective (algebraMap R (Localization.AtPrime (Ideal.span {x}))) :=
      IsLocalization.injective _ (Ideal.span {x}).primeCompl_le_nonZeroDivisors
    have hmax : maximalIdeal (Localization.AtPrime (Ideal.span {x})) =
        Ideal.span {algebraMap R (Localization.AtPrime (Ideal.span {x})) x} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
    have hnf : ¬ IsField (Localization.AtPrime (Ideal.span {x})) := by
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
      exact fun h => hx0 (hinj (h.trans (map_zero _).symm))
    have hprinc : (maximalIdeal (Localization.AtPrime (Ideal.span {x}))).IsPrincipal := by
      rw [hmax]; exact ⟨⟨_, rfl⟩⟩
    exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime (Ideal.span {x})) hnf).out 0 4).mpr hprinc

end S_IsRegularLocalRing_isPrime_span_singleton_and_isDiscreteValuationRing_localization_of_notMem_sq
end P2MW
export P2MW.S_IsRegularLocalRing_isPrime_span_singleton_and_isDiscreteValuationRing_localization_of_notMem_sq (solution)
