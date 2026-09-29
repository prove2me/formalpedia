-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_ord_placeOfPoint_sum_smul_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_one_of_mem_preimage_iotaInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/21d1df0a-3187-5bb7-912b-f7a1afd9aad9

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_tensor_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_ord_placeOfPoint_sum_smul_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_one_of_mem_preimage_iotaInf

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

namespace UnifCore

theorem exists_irreducible_of_span_eq_maximalIdeal {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (S : Set R) (hS : Ideal.span S = maximalIdeal R) : ∃ s ∈ S, Irreducible s := by
  by_contra hno
  push_neg at hno
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hsub : Ideal.span S ≤ maximalIdeal R ^ 2 := by
    rw [Ideal.span_le]
    intro s hs
    have hs𝔪 : s ∈ maximalIdeal R := hS ▸ Ideal.subset_span hs
    rcases eq_or_ne s 0 with rfl | hs0
    · exact (maximalIdeal R ^ 2).zero_mem
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one] at hs𝔪
      exact (mem_nonunits_iff.mp ((mem_maximalIdeal _).mp hs𝔪)) u.isUnit
    have hn1 : n ≠ 1 := by
      rintro rfl
      apply hno _ hs
      rw [pow_one]
      exact (irreducible_units_mul u).mpr hϖ
    have hn2 : 2 ≤ n := by omega
    show (u : R) * ϖ ^ n ∈ maximalIdeal R ^ 2
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact dvd_mul_of_dvd_right (pow_dvd_pow ϖ hn2) _
  rw [hS] at hsub
  have hϖmem : ϖ ∈ maximalIdeal R ^ 2 := hsub (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ)
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hϖmem
  obtain ⟨c, hc⟩ := hϖmem
  apply hϖ.not_isUnit
  have h1 : ϖ * (1 - ϖ * c) = 0 := by rw [mul_sub, mul_one, ← mul_assoc, ← pow_two, ← hc, sub_self]
  rcases mul_eq_zero.mp h1 with h0 | h0
  · exact absurd h0 hϖ.ne_zero
  · exact IsUnit.of_mul_eq_one c (by rw [sub_eq_zero] at h0; exact h0.symm)

theorem exists_ord_eq_one_of_span_eq_maximalIdeal
    {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L)
    {S : Type*} [CommRing S] [IsLocalRing S] (φ : S →+* L) (hinj : Function.Injective φ)
    (hrange : Set.range φ = (v.toValuationSubring : Set L))
    (T : Set S) (hT : Ideal.span T = maximalIdeal S) :
    ∃ t ∈ T, v.ord (φ t) = 1 := by
  have hmem : ∀ s, φ s ∈ v.toValuationSubring := fun s => by
    have : φ s ∈ Set.range φ := ⟨s, rfl⟩
    rw [hrange] at this
    exact this
  let f : S →+* ↥(v.toValuationSubring) := φ.codRestrict v.toValuationSubring hmem
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h : _), fun y => ?_⟩
    have hy : (y : L) ∈ Set.range φ := by rw [hrange]; exact y.2
    obtain ⟨s, hs⟩ := hy
    exact ⟨s, Subtype.ext hs⟩
  let ψ : S ≃+* ↥(v.toValuationSubring) := RingEquiv.ofBijective f hf
  haveI : IsDomain S := hinj.isDomain φ
  haveI : IsDiscreteValuationRing S := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing ψ.symm
  obtain ⟨t, ht, hirr⟩ := exists_irreducible_of_span_eq_maximalIdeal T hT
  refine ⟨t, ht, ?_⟩
  have hirr' : Irreducible (ψ t) := (MulEquiv.irreducible_iff (ψ : S ≃* ↥(v.toValuationSubring))).mpr hirr
  have := v.ord_coe_irreducible hirr'
  exact this

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem key1
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ).base P.1 ∈ (pullback.fst (toBase p (ΓN p M H hpM) hj)
        (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))
    [Nonempty (Scheme.Opens.toScheme (((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)))] :
    letI : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∀ (𝔮 : PrimeSpectrum (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A))),
      letI : CommRing (Localization.AtPrime 𝔮.asIdeal) := @OreLocalization.instCommRing (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) _ 𝔮.asIdeal.primeCompl _
      ∀ (e : (pullback (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).presheaf.stalk ((𝔛.efib A hA ρ hρ).base P.1) ≅ CommRingCat.of (Localization.AtPrime 𝔮.asIdeal)) (b : ↥(chartAlgInf p (ΓN p M H hpM) hj)),
      e.hom ((pullback (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).presheaf.germ ((pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)) ((𝔛.efib A hA ρ hρ).base P.1) hP
          (((pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv b)))) =
        algebraMap (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) (Localization.AtPrime 𝔮.asIdeal) (b ⊗ₜ[R p] (1 : (IsLocalRing.ResidueField ↥A))) →
      ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm (algebraMap ((𝔛.Mfib A hA ρ hρ).C.presheaf.stalk P.1) (𝔛.Mfib A hA ρ hρ).C.functionField (((𝔛.efib A hA ρ hρ).stalkMap P.1).hom (e.inv.hom (algebraMap (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) (Localization.AtPrime 𝔮.asIdeal) (b ⊗ₜ[R p] (1 : (IsLocalRing.ResidueField ↥A)))))))) = ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm ((𝔛.Mfib A hA ρ hρ).C.germToFunctionField (((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)) (((((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
                (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv b)))))) := by
  letI : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  intro 𝔮 e b hb
  rw [← hb]
  erw [Iso.hom_inv_id_apply]
  have h1 : ((𝔛.efib A hA ρ hρ).stalkMap P.1).hom (((pullback (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).presheaf.germ ((pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)) ((𝔛.efib A hA ρ hρ).base P.1) hP).hom (((pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv b)))) =
      ((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ) ⁻¹ᵁ ((pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))) P.1 hP).hom (((𝔛.efib A hA ρ hρ).app ((pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))).hom (((pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv b)))) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.germ_stalkMap]
    rfl
  erw [h1]
  have h2 : ∀ w, algebraMap ((𝔛.Mfib A hA ρ hρ).C.presheaf.stalk P.1) (𝔛.Mfib A hA ρ hρ).C.functionField (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ) ⁻¹ᵁ ((pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))) P.1 hP).hom w) =
      ((𝔛.Mfib A hA ρ hρ).C.germToFunctionField (((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))).hom w := by
    intro w
    show ((𝔛.Mfib A hA ρ hρ).C.presheaf.stalkSpecializes _).hom (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ _ P.1 hP).hom w) = _
    erw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rfl
  rw [h2]
  rfl

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem key2
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ).base P.1 ∈ (pullback.fst (toBase p (ΓN p M H hpM) hj)
        (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)) :
    letI : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∀ (𝔮 : PrimeSpectrum (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A))),
      letI : CommRing (Localization.AtPrime 𝔮.asIdeal) := @OreLocalization.instCommRing (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) _ 𝔮.asIdeal.primeCompl _
      ∀ (e : (pullback (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).presheaf.stalk ((𝔛.efib A hA ρ hρ).base P.1) ≅ CommRingCat.of (Localization.AtPrime 𝔮.asIdeal)) (o : (IsLocalRing.ResidueField ↥A)),
      e.hom ((pullback (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).presheaf.germ ⊤ ((𝔛.efib A hA ρ hρ).base P.1) trivial
          ((pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).appTop ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField ↥A))).inv o))) =
        algebraMap (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) (Localization.AtPrime 𝔮.asIdeal) ((1 : ↥(chartAlgInf p (ΓN p M H hpM) hj)) ⊗ₜ[R p] o) →
      ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm (algebraMap ((𝔛.Mfib A hA ρ hρ).C.presheaf.stalk P.1) (𝔛.Mfib A hA ρ hρ).C.functionField (((𝔛.efib A hA ρ hρ).stalkMap P.1).hom (e.inv.hom (algebraMap (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) (Localization.AtPrime 𝔮.asIdeal) ((1 : ↥(chartAlgInf p (ΓN p M H hpM) hj)) ⊗ₜ[R p] o)))))) = algebraMap (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) o := by
  letI : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  intro 𝔮 e o ho
  rw [← ho]
  erw [Iso.hom_inv_id_apply]
  have h1 : ((𝔛.efib A hA ρ hρ).stalkMap P.1).hom (((pullback (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).presheaf.germ ⊤ ((𝔛.efib A hA ρ hρ).base P.1) trivial).hom ((pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField ↥A))).inv.hom o))) =
      ((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ) ⁻¹ᵁ ⊤) P.1 trivial).hom (((𝔛.efib A hA ρ hρ).app ⊤).hom ((pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField ↥A))).inv.hom o))) := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.germ_stalkMap]
    rfl
  erw [h1]
  have happ : ((𝔛.efib A hA ρ hρ).app ⊤).hom ((pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField ↥A))).inv.hom o)) = ((𝔛.Mfib A hA ρ hρ).toBase.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of (IsLocalRing.ResidueField ↥A))).inv.hom o) := by
    rw [← 𝔛.hefib A hA ρ hρ, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    rfl
  rw [happ]
  have h3 : ∀ w, algebraMap ((𝔛.Mfib A hA ρ hρ).C.presheaf.stalk P.1) (𝔛.Mfib A hA ρ hρ).C.functionField (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ) ⁻¹ᵁ ⊤) P.1 trivial).hom w) =
      ((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ⊤ (genericPoint (𝔛.Mfib A hA ρ hρ).C) trivial).hom w := by
    intro w
    show ((𝔛.Mfib A hA ρ hρ).C.presheaf.stalkSpecializes _).hom (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ) ⁻¹ᵁ ⊤) P.1 trivial).hom w) = _
    erw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    rfl
  rw [h3, RingEquiv.symm_apply_eq]
  exact ((𝔛.Mfib A hA ρ hρ).ffEquiv_algebraMap o).symm

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem key3
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ).base P.1 ∈ (pullback.fst (toBase p (ΓN p M H hpM) hj)
        (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))
    [Nonempty (Scheme.Opens.toScheme (((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)))] :
    letI : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∀ (S : Type) [CommRing S] [Algebra (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) S] (ψ : S →+* ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))),
      (∀ b : ↥(chartAlgInf p (ΓN p M H hpM) hj), ψ (algebraMap (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) S (b ⊗ₜ[R p] (1 : (IsLocalRing.ResidueField ↥A)))) = ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm ((𝔛.Mfib A hA ρ hρ).C.germToFunctionField (((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)) (((((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
                (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv b))))))) →
      (∀ o : (IsLocalRing.ResidueField ↥A), ψ (algebraMap (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) S ((1 : ↥(chartAlgInf p (ΓN p M H hpM) hj)) ⊗ₜ[R p] o)) = algebraMap (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) o) →
      ∀ r : (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)), ∃ (n : ℕ) (c : Fin n → ↥(chartAlgInf p (ΓN p M H hpM) hj)) (a : Fin n → (IsLocalRing.ResidueField ↥A)),
        ψ (algebraMap (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) S r) = ∑ i, algebraMap (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) (a i) * ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm ((𝔛.Mfib A hA ρ hρ).C.germToFunctionField (((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)) (((((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
                (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv (c i))))))) := by
  letI : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  intro S _ _ ψ k1 k2 r
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset r
  refine ⟨s.card, fun k => (s.equivFin.symm k).1.1, fun k => (s.equivFin.symm k).1.2, ?_⟩
  have hread : ψ (algebraMap (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) S r) = ∑ i ∈ s, algebraMap (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) i.2 * ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm ((𝔛.Mfib A hA ρ hρ).C.germToFunctionField (((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)) (((((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
                (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv i.1)))))) := by
    rw [hs, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have htm : i.1 ⊗ₜ[R p] i.2 = (i.1 ⊗ₜ[R p] (1 : (IsLocalRing.ResidueField ↥A))) * ((1 : ↥(chartAlgInf p (ΓN p M H hpM) hj)) ⊗ₜ[R p] i.2) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [htm, map_mul, map_mul, k1, k2, mul_comm]
  rw [hread, ← Finset.sum_coe_sort s]
  exact (Fintype.sum_equiv s.equivFin.symm _ (fun i : ↥s => algebraMap (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) i.1.2 * ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm ((𝔛.Mfib A hA ρ hρ).C.germToFunctionField (((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)) (((((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
                (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv i.1.1))))))) (fun k => rfl)).symm

end UnifCore

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ).base P.1 ∈ (pullback.fst (toBase p (ΓN p M H hpM) hj)
        (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)) :
    ∃ (_ : Nonempty (Scheme.Opens.toScheme ((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))))
      (n : ℕ) (c : Fin n → ↥(chartAlgInf p (ΓN p M H hpM) hj)) (a : Fin n → IsLocalRing.ResidueField ↥A),
      ((𝔛.Mfib A hA ρ hρ).placeOfPoint P).ord
        (∑ i, algebraMap (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) (a i) *
          ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm
            ((𝔛.Mfib A hA ρ hρ).C.germToFunctionField
              ((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
                  (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))
              (((𝔛.efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
                  (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
                (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv (c i))))))) = 1 := by
  letI : Algebra (R p) (IsLocalRing.ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  haveI : IsIso (𝔛.efib A hA ρ hρ) := 𝔛.efib_iso A hA ρ hρ
  have hPU : P.1 ∈ (((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)) := hP
  haveI hne : Nonempty (Scheme.Opens.toScheme (((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤))) := ⟨⟨P.1, hPU⟩⟩

  obtain ⟨𝔮, e, he_o, he_b⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_stalk_iso_localization_tensor_chartAlgInf
    (R p) ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM)) (jAt (ΓN p M H hpM) hj) (IsLocalRing.ResidueField ↥A) ((𝔛.efib A hA ρ hρ).base P.1) hP
  letI instLoc : CommRing (Localization.AtPrime 𝔮.asIdeal) := @OreLocalization.instCommRing (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) _ 𝔮.asIdeal.primeCompl _

  let φ : ↑((𝔛.Mfib A hA ρ hρ).C.presheaf.stalk P.1) →+* ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) :=
    ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm : (𝔛.Mfib A hA ρ hρ).C.functionField ≃+* ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))).toRingHom.comp
      (algebraMap ((𝔛.Mfib A hA ρ hρ).C.presheaf.stalk P.1) (𝔛.Mfib A hA ρ hρ).C.functionField)
  have hφinj : Function.Injective φ := by
    refine ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm.injective).comp ?_
    exact IsFractionRing.injective ((𝔛.Mfib A hA ρ hρ).C.presheaf.stalk P.1) (𝔛.Mfib A hA ρ hρ).C.functionField
  have hφrange : Set.range φ = ((((𝔛.Mfib A hA ρ hρ).placeOfPoint P).toValuationSubring : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) := by
    have h := congrArg (fun S : Subring ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) => (S : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) ((𝔛.Mfib A hA ρ hρ).range_stalk_eq P)
    first
      | simpa only [RingHom.coe_range] using h
      | (simp only [RingHom.coe_range] at h; exact h)
  let E : (Localization.AtPrime 𝔮.asIdeal) ≃+* ↑((𝔛.Mfib A hA ρ hρ).C.presheaf.stalk P.1) :=
    e.symm.commRingCatIsoToRingEquiv.trans (asIso ((𝔛.efib A hA ρ hρ).stalkMap P.1)).commRingCatIsoToRingEquiv
  let ψ : (Localization.AtPrime 𝔮.asIdeal) →+* ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) := φ.comp E.toRingHom
  have hψinj : Function.Injective ψ := hφinj.comp E.injective
  have hψrange : Set.range ψ = (((𝔛.Mfib A hA ρ hρ).placeOfPoint P).toValuationSubring : Set ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) := by
    rw [← hφrange]
    ext y
    constructor
    · rintro ⟨z, rfl⟩; exact ⟨E z, rfl⟩
    · rintro ⟨z, rfl⟩; exact ⟨E.symm z, by simp [ψ]⟩
  have hspan : Ideal.span ((algebraMap (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) (Localization.AtPrime 𝔮.asIdeal)) '' (𝔮.asIdeal : Set (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)))) = maximalIdeal (Localization.AtPrime 𝔮.asIdeal) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map]
  obtain ⟨t, ⟨r, hr, rfl⟩, hord⟩ := UnifCore.exists_ord_eq_one_of_span_eq_maximalIdeal ((𝔛.Mfib A hA ρ hρ).placeOfPoint P)
    (S := (Localization.AtPrime 𝔮.asIdeal)) ψ hψinj hψrange ((algebraMap (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) (Localization.AtPrime 𝔮.asIdeal)) '' (𝔮.asIdeal : Set (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)))) hspan

  have k1 : ∀ b : ↥(chartAlgInf p (ΓN p M H hpM) hj), ψ (algebraMap (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) (Localization.AtPrime 𝔮.asIdeal) (b ⊗ₜ[R p] (1 : (IsLocalRing.ResidueField ↥A)))) = ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm ((𝔛.Mfib A hA ρ hρ).C.germToFunctionField (((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)) (((((𝔛.efib A hA ρ hρ) ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app ((ιInf p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
                (((ιInf p (ΓN p M H hpM) hj).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgInf p (ΓN p M H hpM) hj))).inv b)))))) :=
    fun b => UnifCore.key1 p M H hpM hj 𝔛 A hA ρ hρ P hP 𝔮 e b (he_b b)
  have k2 : ∀ o : (IsLocalRing.ResidueField ↥A), ψ (algebraMap (↥(chartAlgInf p (ΓN p M H hpM) hj) ⊗[R p] (IsLocalRing.ResidueField ↥A)) (Localization.AtPrime 𝔮.asIdeal) ((1 : ↥(chartAlgInf p (ΓN p M H hpM) hj)) ⊗ₜ[R p] o)) = algebraMap (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) o :=
    fun o => UnifCore.key2 p M H hpM hj 𝔛 A hA ρ hρ P hP 𝔮 e o (he_o o)
  obtain ⟨n, c, a, hsum⟩ := UnifCore.key3 p M H hpM hj 𝔛 A hA ρ hρ P hP (Localization.AtPrime 𝔮.asIdeal) ψ k1 k2 r
  exact ⟨hne, n, c, a, by rw [← hsum]; exact hord⟩

#print axioms solution

end S_ModularCurve_XHDRModelAtP_exists_ord_placeOfPoint_sum_smul_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_one_of_mem_preimage_iotaInf
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_ord_placeOfPoint_sum_smul_ffEquiv_symm_germToFunctionField_app_iotaInf_eq_one_of_mem_preimage_iotaInf (solution)
