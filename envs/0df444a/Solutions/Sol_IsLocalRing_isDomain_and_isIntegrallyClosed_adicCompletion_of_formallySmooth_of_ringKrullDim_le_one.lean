-- Prove2me | solution 1 for IsLocalRing.isDomain_and_isIntegrallyClosed_adicCompletion_of_formallySmooth_of_ringKrullDim_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/f549a468-c174-5e55-855a-e4595e2341ad

import Mathlib
import Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_formallySmooth_of_ringKrullDim_le_one

set_option autoImplicit false

open IsLocalRing

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    {A₀ : Type} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] (q : A₀)
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {q})
    (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra A₀ S]
    [Algebra.EssFiniteType A₀ S] [Algebra.FormallySmooth A₀ S]
    (hq : IsUnit (algebraMap A₀ S q)) (hdim : ringKrullDim S ≤ 1) :
    IsDomain (AdicCompletion (IsLocalRing.maximalIdeal S) S) ∧
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal S) S) ∧
      algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S) (algebraMap A₀ S q) ≠ 0  := by
  classical

  obtain ⟨s, hloc⟩ := Algebra.EssFiniteType.cond (R := A₀) (S := S)
  set S₀ : Subalgebra A₀ S := Algebra.adjoin A₀ (s : Set S) with hS₀
  let 𝔭 : Ideal ↥S₀ := (maximalIdeal S).comap (algebraMap ↥S₀ S)
  haveI h𝔭 : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have hM : Submonoid.comap (algebraMap ↥S₀ S) (IsUnit.submonoid S) = 𝔭.primeCompl := by
    ext x
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, Ideal.primeCompl, 𝔭]
    show IsUnit (algebraMap ↥S₀ S x) ↔ x ∉ (maximalIdeal S).comap (algebraMap ↥S₀ S)
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  haveI hAt : IsLocalization.AtPrime S 𝔭 := by
    rw [IsLocalization.AtPrime, ← hM]; exact hloc

  haveI : Algebra.FiniteType A₀ ↥S₀ := (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset s)
  haveI : Algebra.FinitePresentation A₀ ↥S₀ := (Algebra.FinitePresentation.of_finiteType).mp inferInstance

  have hsm : (⟨𝔭, h𝔭⟩ : PrimeSpectrum ↥S₀) ∈ Algebra.smoothLocus A₀ ↥S₀ := by
    show Algebra.FormallySmooth A₀ (Localization.AtPrime 𝔭)
    let e : S ≃ₐ[↥S₀] Localization.AtPrime 𝔭 := IsLocalization.algEquiv 𝔭.primeCompl S (Localization.AtPrime 𝔭)
    exact Algebra.FormallySmooth.of_equiv (e.restrictScalars A₀)

  obtain ⟨U, ⟨f, rfl⟩, hfU, hUsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hsm Algebra.isOpen_smoothLocus
  have hf𝔭 : f ∉ 𝔭 := hfU
  have hFS : Algebra.FormallySmooth A₀ (Localization.Away f) := Algebra.basicOpen_subset_smoothLocus_iff.mp hUsub

  haveI : Algebra.FinitePresentation A₀ (Localization.Away f) :=
    Algebra.FinitePresentation.trans A₀ ↥S₀ (Localization.Away f)
  haveI : Algebra.Smooth A₀ (Localization.Away f) := ⟨hFS, inferInstance⟩

  have hfu : IsUnit (algebraMap ↥S₀ S f) := by
    have : f ∈ 𝔭.primeCompl := hf𝔭
    rw [← hM] at this
    exact this
  let gS : Localization.Away f →+* S := IsLocalization.Away.lift f (g := algebraMap ↥S₀ S) hfu
  letI algS₁S : Algebra (Localization.Away f) S := gS.toAlgebra
  have hgS : ∀ x : ↥S₀, algebraMap (Localization.Away f) S (algebraMap ↥S₀ (Localization.Away f) x) = algebraMap ↥S₀ S x :=
    fun x => IsLocalization.Away.lift_eq f hfu x
  haveI : IsScalarTower ↥S₀ (Localization.Away f) S := IsScalarTower.of_algebraMap_eq fun x => (hgS x).symm
  haveI : IsScalarTower A₀ (Localization.Away f) S := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rw [IsScalarTower.algebraMap_apply A₀ ↥S₀ (Localization.Away f) a, hgS, ← IsScalarTower.algebraMap_apply A₀ ↥S₀ S a]

  let P₁ : Ideal (Localization.Away f) := (maximalIdeal S).comap (algebraMap (Localization.Away f) S)
  haveI hP₁ : P₁.IsPrime := Ideal.comap_isPrime _ _
  haveI : IsLocalization.AtPrime S P₁ := by
    have h1 : IsLocalization ((𝔭.primeCompl).map (algebraMap ↥S₀ (Localization.Away f))) S :=
      IsLocalization.isLocalization_of_submonoid_le (Localization.Away f) S (Submonoid.powers f) 𝔭.primeCompl
        (Submonoid.powers_le.mpr hf𝔭)
    refine @IsLocalization.of_le _ _ _ _ _ _ h1 P₁.primeCompl ?_ ?_
    · rintro y ⟨x, hx, rfl⟩
      show algebraMap (Localization.Away f) S (algebraMap ↥S₀ (Localization.Away f) x) ∉ maximalIdeal S
      rw [← IsScalarTower.algebraMap_apply]
      exact hx
    · intro r hr
      have : algebraMap (Localization.Away f) S r ∉ maximalIdeal S := hr
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at this

  obtain ⟨hdom, hic⟩ := Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime A₀ (Localization.Away f) P₁ S
  haveI := hdom
  haveI := hic

  have hqunit : IsUnit (algebraMap S (AdicCompletion (maximalIdeal S) S) (algebraMap A₀ S q)) := hq.map _
  by_cases h𝔪 : maximalIdeal S = ⊥
  ·
    haveI : IsAdicComplete (maximalIdeal S) S := by rw [h𝔪]; infer_instance
    let e := AdicCompletion.ofAlgEquiv (maximalIdeal S)
    have hF : IsField S := IsLocalRing.isField_iff_maximalIdeal_eq.mpr h𝔪
    haveI hD : IsDomain (AdicCompletion (maximalIdeal S) S) := MulEquiv.isDomain S e.symm.toMulEquiv
    have hF' : IsField (AdicCompletion (maximalIdeal S) S) := MulEquiv.isField hF e.symm.toMulEquiv
    letI : Field (AdicCompletion (maximalIdeal S) S) := hF'.toField
    exact ⟨hD, inferInstance, hqunit.ne_zero⟩
  ·
    have hnf : ¬ IsField S := fun hF => h𝔪 (IsLocalRing.isField_iff_maximalIdeal_eq.mp hF)
    haveI hDVR : IsDiscreteValuationRing S := by
      apply ((IsDiscreteValuationRing.TFAE S hnf).out 0 3).mpr
      refine ⟨hic, ⟨maximalIdeal S, ⟨h𝔪, inferInstance⟩, ?_⟩⟩
      rintro Q ⟨hQ0, hQp⟩
      haveI := hQp
      by_contra hQ
      have hlt : Q < maximalIdeal S := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQp.ne_top) hQ
      have hbot : (⊥ : Ideal S) < Q := bot_lt_iff_ne_bot.mpr hQ0
      haveI : (⊥ : Ideal S).IsPrime := Ideal.isPrime_bot
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [Ideal.height_bot, zero_add] at h1
      have h2' : (2 : ℕ∞) ≤ (maximalIdeal S).height := by
        calc (2 : ℕ∞) = 1 + 1 := by norm_num
          _ ≤ Q.height + 1 := by gcongr
          _ ≤ (maximalIdeal S).height := h2
      have : ((2 : ℕ∞) : WithBot ℕ∞) ≤ 1 := by
        refine le_trans ?_ hdim
        rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]; exact WithBot.coe_le_coe.mpr h2'
      exact absurd (WithBot.coe_le_coe.mp this) (by decide)
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
    obtain ⟨hD, hDVR', -, -⟩ :=
      IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete S ϖ hϖ
    haveI := hD; haveI := hDVR'
    exact ⟨hD, inferInstance, hqunit.ne_zero⟩

end S_IsLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_formallySmooth_of_ringKrullDim_le_one
end P2MW
export P2MW.S_IsLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_formallySmooth_of_ringKrullDim_le_one (solution)
