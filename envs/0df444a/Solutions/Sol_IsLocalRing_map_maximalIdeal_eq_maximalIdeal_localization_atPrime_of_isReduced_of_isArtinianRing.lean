-- Prove2me | solution 1 for IsLocalRing.map_maximalIdeal_eq_maximalIdeal_localization_atPrime_of_isReduced_of_isArtinianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/86874bed-6246-5043-9e55-2373c8580a8c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_map_maximalIdeal_eq_maximalIdeal_localization_atPrime_of_isReduced_of_isArtinianRing

set_option autoImplicit false

open IsLocalRing

theorem solution
    {C C' : Type} [CommRing C] [IsLocalRing C] [CommRing C'] [Algebra C C']
    (𝔫 : Ideal C') [𝔫.IsMaximal]
    (hle : (maximalIdeal C).map (algebraMap C C') ≤ 𝔫)
    [IsReduced (C' ⧸ (maximalIdeal C).map (algebraMap C C'))]
    [IsArtinianRing (C' ⧸ (maximalIdeal C).map (algebraMap C C'))] :
    (maximalIdeal C).map (algebraMap C (Localization.AtPrime 𝔫)) = maximalIdeal (Localization.AtPrime 𝔫) ∧
    IsLocalHom (algebraMap C (Localization.AtPrime 𝔫)) ∧
    Function.Surjective ((residue (Localization.AtPrime 𝔫)).comp (algebraMap C' (Localization.AtPrime 𝔫))) ∧
    RingHom.ker ((residue (Localization.AtPrime 𝔫)).comp (algebraMap C' (Localization.AtPrime 𝔫))) = 𝔫 := by
  classical
  set M' : Ideal C' := (maximalIdeal C).map (algebraMap C C') with hM'
  haveI : 𝔫.IsPrime := Ideal.IsMaximal.isPrime inferInstance

  have key : ∀ n ∈ 𝔫, ∃ s : C', s ∉ 𝔫 ∧ s * n ∈ M' := by
    intro n hn
    have hker : RingHom.ker (Ideal.Quotient.mk M') ≤ 𝔫 := by rw [Ideal.mk_ker]; exact hle
    haveI hP : (𝔫.map (Ideal.Quotient.mk M')).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    let L := Localization.AtPrime (𝔫.map (Ideal.Quotient.mk M'))

    have hmax : maximalIdeal L = ⊥ := by
      obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := L)
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_bot]
      apply IsReduced.eq_zero x
      refine ⟨N, ?_⟩
      have : x ^ N ∈ maximalIdeal L ^ N := Ideal.pow_mem_pow hx N
      rw [hN] at this
      exact (Submodule.mem_bot L).mp this
    have h1 : algebraMap (C' ⧸ M') L (Ideal.Quotient.mk M' n) = 0 := by
      have : algebraMap (C' ⧸ M') L (Ideal.Quotient.mk M' n) ∈ maximalIdeal L := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hn)
      rwa [hmax, Submodule.mem_bot] at this
    obtain ⟨⟨m, hm⟩, hmn⟩ := (IsLocalization.map_eq_zero_iff (𝔫.map (Ideal.Quotient.mk M')).primeCompl L _).mp h1
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m
    refine ⟨s, fun hs => hm (Ideal.mem_map_of_mem _ hs), ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact hmn

  have hmapC : (maximalIdeal C).map (algebraMap C (Localization.AtPrime 𝔫)) = M'.map (algebraMap C' (Localization.AtPrime 𝔫)) := by
    rw [hM', Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have h1 : (maximalIdeal C).map (algebraMap C (Localization.AtPrime 𝔫)) = maximalIdeal (Localization.AtPrime 𝔫) := by
    apply le_antisymm
    · rw [hmapC, ← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono hle
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, hmapC, Ideal.map_le_iff_le_comap]
      intro n hn
      obtain ⟨s, hs, hsn⟩ := key n hn
      have hu : IsUnit (algebraMap C' (Localization.AtPrime 𝔫) s) := IsLocalization.map_units _ (⟨s, hs⟩ : 𝔫.primeCompl)
      obtain ⟨u, hu'⟩ := hu
      rw [Ideal.mem_comap]
      have : algebraMap C' (Localization.AtPrime 𝔫) n = ↑u⁻¹ * algebraMap C' (Localization.AtPrime 𝔫) (s * n) := by
        rw [map_mul, ← hu', ← mul_assoc, Units.inv_mul, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hsn)
  refine ⟨h1, ⟨fun a ha => ?_⟩, ?_, ?_⟩
  ·
    by_contra hna
    have : algebraMap C (Localization.AtPrime 𝔫) a ∈ maximalIdeal (Localization.AtPrime 𝔫) := by
      rw [← h1]; exact Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal a).mpr hna)
    exact (IsLocalRing.mem_maximalIdeal _).mp this ha
  ·
    intro r
    obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨⟨a, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔫.primeCompl d
    obtain ⟨t, m, hm, htm⟩ := (inferInstance : 𝔫.IsMaximal).exists_inv hs
    refine ⟨a * t, ?_⟩
    show residue _ (algebraMap C' _ (a * t)) = residue _ (IsLocalization.mk' (Localization.AtPrime 𝔫) a ⟨s, hs⟩)
    have hm0 : residue (Localization.AtPrime 𝔫) (algebraMap C' _ m) = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, ← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hm
    have hst : residue (Localization.AtPrime 𝔫) (algebraMap C' _ s) * residue (Localization.AtPrime 𝔫) (algebraMap C' _ t) = 1 := by
      rw [← map_mul, ← map_mul, mul_comm s t, show t * s = 1 - m by rw [← htm]; ring, map_sub, map_one, map_sub, map_one, hm0, sub_zero]
    calc residue _ (algebraMap C' _ (a * t))
        = residue _ (algebraMap C' _ a) * residue _ (algebraMap C' _ t) := by rw [map_mul, map_mul]
      _ = residue _ (IsLocalization.mk' (Localization.AtPrime 𝔫) a ⟨s, hs⟩ * algebraMap C' _ s) * residue _ (algebraMap C' _ t) := by
          rw [IsLocalization.mk'_spec]
      _ = residue _ (IsLocalization.mk' (Localization.AtPrime 𝔫) a ⟨s, hs⟩) *
            (residue _ (algebraMap C' _ s) * residue _ (algebraMap C' _ t)) := by rw [map_mul, mul_assoc]
      _ = residue _ (IsLocalization.mk' (Localization.AtPrime 𝔫) a ⟨s, hs⟩) := by rw [hst, mul_one]
  ·
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    constructor
    · intro hx
      have : x ∈ Ideal.under C' (maximalIdeal (Localization 𝔫.primeCompl)) := hx
      rwa [Localization.AtPrime.under_maximalIdeal] at this
    · intro hx
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hx

end S_IsLocalRing_map_maximalIdeal_eq_maximalIdeal_localization_atPrime_of_isReduced_of_isArtinianRing
end P2MW
export P2MW.S_IsLocalRing_map_maximalIdeal_eq_maximalIdeal_localization_atPrime_of_isReduced_of_isArtinianRing (solution)
