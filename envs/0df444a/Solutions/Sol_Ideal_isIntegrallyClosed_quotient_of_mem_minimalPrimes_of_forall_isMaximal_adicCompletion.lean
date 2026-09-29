-- Prove2me | solution 1 for Ideal.isIntegrallyClosed_quotient_of_mem_minimalPrimes_of_forall_isMaximal_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/87cdf191-5521-5376-8e20-84574d005aa0

import Mathlib
import Theorems.Thm_IsIntegrallyClosed_localization_atPrime_of_adicCompletion
import Theorems.Thm_AdicCompletion_exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_isIntegrallyClosed_quotient_of_mem_minimalPrimes_of_forall_isMaximal_adicCompletion
p2m_attr_erase "simp" "AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply"

set_option autoImplicit false

universe u

open IsLocalRing

set_option maxHeartbeats 3200000 in

theorem solution
    (C : Type u) [CommRing C] [IsNoetherianRing C]
    (h : ∀ 𝔪 : Ideal C, 𝔪.IsMaximal → IsDomain (AdicCompletion 𝔪 C) ∧ IsIntegrallyClosed (AdicCompletion 𝔪 C))
    (𝔓 : Ideal C) (h𝔓 : 𝔓 ∈ (⊥ : Ideal C).minimalPrimes) :
    IsIntegrallyClosed (C ⧸ 𝔓) := by
  classical
  haveI h𝔓p : 𝔓.IsPrime := h𝔓.1.1
  apply IsIntegrallyClosed.of_localization_maximal
  intro 𝔫 h𝔫 h𝔫max

  let 𝔪 : Ideal C := 𝔫.comap (Ideal.Quotient.mk 𝔓)
  haveI h𝔪max : 𝔪.IsMaximal := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have h𝔓𝔪 : 𝔓 ≤ 𝔪 := by
    intro x hx
    change Ideal.Quotient.mk 𝔓 x ∈ 𝔫
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact 𝔫.zero_mem
  obtain ⟨hdomC, hicC⟩ := h 𝔪 h𝔪max

  let L := Localization.AtPrime 𝔪
  obtain ⟨T, hT⟩ := AdicCompletion.exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal (S := L) 𝔪
  haveI : IsDomain (AdicCompletion (maximalIdeal L) L) := T.symm.toMulEquiv.isDomain
  haveI : IsIntegrallyClosed (AdicCompletion (maximalIdeal L) L) := IsIntegrallyClosed.of_equiv T

  haveI : IsHausdorff (maximalIdeal L) L := by
    refine ⟨fun x hx => ?_⟩
    have hmem : x ∈ (⨅ n : ℕ, (maximalIdeal L) ^ n) := by
      rw [Submodule.mem_iInf]; intro n
      have := hx n
      rw [SModEq.zero] at this
      simpa [smul_eq_mul, Ideal.mul_top] using this
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal L).ne_top, Submodule.mem_bot] at hmem
  have hinjL : Function.Injective (algebraMap L (AdicCompletion (maximalIdeal L) L)) :=
    AdicCompletion.of_injective (maximalIdeal L) L
  haveI hdomL : IsDomain L := by
    haveI : NoZeroDivisors L := (algebraMap L (AdicCompletion (maximalIdeal L) L)).toMonoidWithZeroHom
      |>.toZeroHom |> fun f => Function.Injective.noZeroDivisors (algebraMap L _) hinjL (map_zero _) (map_mul _)
    exact NoZeroDivisors.to_isDomain L

  have hicL' : IsIntegrallyClosed (Localization.AtPrime (maximalIdeal L)) :=
    IsIntegrallyClosed.localization_atPrime_of_adicCompletion L (maximalIdeal L)
  haveI hicL : IsIntegrallyClosed L := by
    have e : L ≃ₐ[L] Localization.AtPrime (maximalIdeal L) :=
      IsLocalization.atUnits L (maximalIdeal L).primeCompl (fun x hx => by
        by_contra hu
        exact hx ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)))
    exact IsIntegrallyClosed.of_equiv e.toRingEquiv.symm

  have hker : ∀ x : C, algebraMap C L x = 0 ↔ x ∈ 𝔓 := by
    have hQ : RingHom.ker (algebraMap C L) ≤ 𝔓 := by
      intro x hx
      rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff 𝔪.primeCompl] at hx
      obtain ⟨s, hs⟩ := hx
      have hs𝔓 : (s : C) ∉ 𝔓 := fun h' => s.2 (h𝔓𝔪 h')
      exact (h𝔓p.mem_or_mem (by simpa [mul_comm] using (show (s : C) * x ∈ 𝔓 from by rw [hs]; exact 𝔓.zero_mem))).resolve_left hs𝔓
    haveI : (RingHom.ker (algebraMap C L)).IsPrime := RingHom.ker_isPrime _
    have hQ' : 𝔓 ≤ RingHom.ker (algebraMap C L) := h𝔓.2 ⟨inferInstance, bot_le⟩ hQ
    intro x; exact ⟨fun hx => hQ hx, fun hx => hQ' hx⟩

  let g : L →+* Localization.AtPrime 𝔫 := Localization.localRingHom 𝔪 𝔫 (Ideal.Quotient.mk 𝔓) rfl
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔫.primeCompl y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (s : C ⧸ 𝔓)
    refine ⟨IsLocalization.mk' L a ⟨s', show s' ∈ 𝔪.primeCompl from ?_⟩, ?_⟩
    · intro hs'𝔪; apply s.2; change Ideal.Quotient.mk 𝔓 s' ∈ 𝔫 at hs'𝔪; rwa [hs'] at hs'𝔪
    · rw [Localization.localRingHom_mk']
      congr 1
      exact Subtype.ext hs'
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl y
    rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hy
    obtain ⟨t, ht⟩ := hy
    obtain ⟨t', ht'⟩ := Ideal.Quotient.mk_surjective (t : C ⧸ 𝔓)
    have ht'𝔪 : t' ∉ 𝔪 := by intro h'; apply t.2; change Ideal.Quotient.mk 𝔓 t' ∈ 𝔫 at h'; rwa [ht'] at h'
    have hta : t' * a ∈ 𝔓 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, ht']; simpa using ht
    have ha : a ∈ 𝔓 := (h𝔓p.mem_or_mem hta).resolve_left (fun h' => ht'𝔪 (h𝔓𝔪 h'))
    have h0 : algebraMap C L a = 0 := (hker a).mpr ha
    rw [IsLocalization.map_eq_zero_iff 𝔪.primeCompl] at h0
    rw [IsLocalization.mk'_eq_zero_iff]
    exact h0
  exact IsIntegrallyClosed.of_equiv (RingEquiv.ofBijective g ⟨hginj, hgsurj⟩)

end S_Ideal_isIntegrallyClosed_quotient_of_mem_minimalPrimes_of_forall_isMaximal_adicCompletion
end P2MW
export P2MW.S_Ideal_isIntegrallyClosed_quotient_of_mem_minimalPrimes_of_forall_isMaximal_adicCompletion (solution)
