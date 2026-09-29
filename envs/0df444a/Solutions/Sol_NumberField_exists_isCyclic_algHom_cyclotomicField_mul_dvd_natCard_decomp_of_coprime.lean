-- Prove2me | solution 1 for NumberField.exists_isCyclic_algHom_cyclotomicField_mul_dvd_natCard_decomp_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/de16d202-27a0-591e-b24c-7f576db2bc86

import Mathlib
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_under_under_ringOfIntegers
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_isCyclic_algHom_cyclotomicField_mul_dvd_natCard_decomp_of_coprime
set_option autoImplicit false
set_option maxHeartbeats 800000
p2m_open "NumberField P2MW.S_NumberField_exists_isCyclic_algHom_cyclotomicField_mul_dvd_natCard_decomp_of_coprime.NumberField IsDedekindDomain"

namespace NumberField
p2m_export "NumberField" "InfinitePlace.smul_eq_comap place InfinitePlace InfinitePlace.comap_comp PlaceDecomp.exists_restrict_decomp_surjective_of_tower PlaceDecomp.decomp InfPlaceDecomp.decomp"
namespace CompositumProof
p2m_open "NumberField"

open Polynomial

theorem splits_cyclotomic_of_dvd (E L : Type) [Field E] [Field L] [Algebra E L] (m m₁ : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} E L] (h : m₁ ∣ m) : (map (algebraMap E L) (cyclotomic m₁ E)).Splits := by
  have hX : (map (algebraMap E L) (X ^ m - 1 : E[X])).Splits :=
    IsCyclotomicExtension.splits_X_pow_sub_one E L (Set.mem_singleton m)
  refine Polynomial.Splits.of_dvd hX ?_ (Polynomial.map_dvd _ ?_)
  · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    exact Polynomial.X_pow_sub_C_ne_zero (NeZero.pos m) 1
  · obtain ⟨k, rfl⟩ := h
    calc cyclotomic m₁ E ∣ X ^ m₁ - 1 := cyclotomic.dvd_X_pow_sub_one m₁ E
      _ ∣ (X ^ m₁) ^ k - 1 ^ k := sub_dvd_pow_sub_pow _ _ _
      _ = X ^ (m₁ * k) - 1 := by rw [one_pow, pow_mul]

noncomputable def cycEmbed (E : Type) [Field E] [NumberField E] (m m₁ : ℕ) [NeZero m] (h : m₁ ∣ m) :
    CyclotomicField m₁ E →ₐ[E] CyclotomicField m E :=
  SplittingField.lift (cyclotomic m₁ E) (splits_cyclotomic_of_dvd E (CyclotomicField m E) m m₁ h)

theorem gal_mul_comm (E L : Type) [Field E] [Field L] [Algebra E L] (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} E L]
    (a b : L ≃ₐ[E] L) : a * b = b * a :=
  IsPrimitiveRoot.autToPow_injective E (IsCyclotomicExtension.zeta_spec m E L) (by rw [map_mul, map_mul, mul_comm])

theorem restrictNormal_mem_stabilizer {E K K' : Type} [Field E] [Field K] [Field K'] [Algebra E K] [Algebra E K']
    [Algebra K K'] [IsScalarTower E K K'] [Normal E K] (g : K' ≃ₐ[E] K') (w : InfinitePlace K')
    (hg : g • w = w) : (AlgEquiv.restrictNormal g K) • w.comap (algebraMap K K') = w.comap (algebraMap K K') := by
  have hcomp : (algebraMap K K').comp ((AlgEquiv.restrictNormal g K).symm : K →+* K)
      = (g.symm : K' →+* K').comp (algebraMap K K') := by
    ext x
    change algebraMap K K' ((AlgEquiv.restrictNormal g K).symm x) = g.symm (algebraMap K K' x)
    apply g.injective
    rw [AlgEquiv.apply_symm_apply, ← AlgEquiv.restrictNormal_commutes, AlgEquiv.apply_symm_apply]
  rw [InfinitePlace.smul_eq_comap, ← InfinitePlace.comap_comp, hcomp, InfinitePlace.comap_comp, ← InfinitePlace.smul_eq_comap, hg]

end NumberField.CompositumProof

open NumberField.CompositumProof in

theorem solution
    (E : Type) [Field E] [NumberField E] (T : Finset (HeightOneSpectrum (𝓞 E)))
    (n₁ m₁ : ℕ) [NeZero m₁] (F₁ : Type) [Field F₁] [NumberField F₁] [Algebra E F₁] [IsGalois E F₁]
    [IsCyclic (F₁ ≃ₐ[E] F₁)] (hcyc₁ : Nonempty (F₁ →ₐ[E] CyclotomicField m₁ E))
    (hinf₁ : ∀ (w : InfinitePlace F₁) (g : (F₁ ≃ₐ[E] F₁)), g ∈ NumberField.InfPlaceDecomp.decomp E F₁ w → g = 1)
    (hdeg₁ : n₁ ∣ Nat.card (F₁ ≃ₐ[E] F₁))
    (hloc₁ : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 F₁), w.under (𝓞 E) = v →
      n₁ ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F₁ w))
    (n₂ m₂ : ℕ) [NeZero m₂] (F₂ : Type) [Field F₂] [NumberField F₂] [Algebra E F₂] [IsGalois E F₂]
    [IsCyclic (F₂ ≃ₐ[E] F₂)] (hcyc₂ : Nonempty (F₂ →ₐ[E] CyclotomicField m₂ E))
    (hinf₂ : ∀ (w : InfinitePlace F₂) (g : (F₂ ≃ₐ[E] F₂)), g ∈ NumberField.InfPlaceDecomp.decomp E F₂ w → g = 1)
    (hdeg₂ : n₂ ∣ Nat.card (F₂ ≃ₐ[E] F₂))
    (hloc₂ : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 F₂), w.under (𝓞 E) = v →
      n₂ ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F₂ w))
    (hcop : Nat.Coprime (Nat.card (F₁ ≃ₐ[E] F₁)) (Nat.card (F₂ ≃ₐ[E] F₂))) :
    ∃ (m : ℕ) (_ : NeZero m) (F' : Type) (_ : Field F') (_ : NumberField F') (_ : Algebra E F') (_ : IsGalois E F')
      (_ : IsCyclic (F' ≃ₐ[E] F')),

      Nonempty (F' →ₐ[E] CyclotomicField m E) ∧

      (∀ (w : InfinitePlace F') (g : (F' ≃ₐ[E] F')), g ∈ NumberField.InfPlaceDecomp.decomp E F' w → g = 1) ∧

      n₁ * n₂ ∣ Nat.card (F' ≃ₐ[E] F') ∧

      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 F'), w.under (𝓞 E) = v →
        n₁ * n₂ ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w)) ∧

      Nat.card (F' ≃ₐ[E] F') ∣ Nat.card (F₁ ≃ₐ[E] F₁) * Nat.card (F₂ ≃ₐ[E] F₂)  := by
  classical
  obtain ⟨ψ₁⟩ := hcyc₁
  obtain ⟨ψ₂⟩ := hcyc₂

  haveI hm : NeZero (m₁ * m₂) := ⟨mul_ne_zero (NeZero.ne m₁) (NeZero.ne m₂)⟩
  haveI : IsGalois E (CyclotomicField (m₁ * m₂) E) := IsCyclotomicExtension.isGalois {m₁ * m₂} E _
  let φ₁ : F₁ →ₐ[E] CyclotomicField (m₁ * m₂) E := (cycEmbed E (m₁ * m₂) m₁ (dvd_mul_right m₁ m₂)).comp ψ₁
  let φ₂ : F₂ →ₐ[E] CyclotomicField (m₁ * m₂) E := (cycEmbed E (m₁ * m₂) m₂ (dvd_mul_left m₂ m₁)).comp ψ₂

  let K : IntermediateField E (CyclotomicField (m₁ * m₂) E) := φ₁.fieldRange ⊔ φ₂.fieldRange
  let H : Subgroup (CyclotomicField (m₁ * m₂) E ≃ₐ[E] CyclotomicField (m₁ * m₂) E) := K.fixingSubgroup
  haveI hHn : H.Normal := ⟨fun n hn g => by rwa [gal_mul_comm E _ (m₁ * m₂) g n, mul_inv_cancel_right]⟩

  haveI hF'gal : IsGalois E ↥(IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H
  have hF'K : IntermediateField.fixedField H = K := IsGalois.fixedField_fixingSubgroup K

  have hle₁ : ∀ x : F₁, φ₁ x ∈ IntermediateField.fixedField H := fun x => by
    rw [hF'K]; exact (le_sup_left : φ₁.fieldRange ≤ K) ⟨x, rfl⟩
  have hle₂ : ∀ x : F₂, φ₂ x ∈ IntermediateField.fixedField H := fun x => by
    rw [hF'K]; exact (le_sup_right : φ₂.fieldRange ≤ K) ⟨x, rfl⟩
  let φ₁' : F₁ →ₐ[E] ↥(IntermediateField.fixedField H) := AlgHom.codRestrict φ₁ (IntermediateField.fixedField H).toSubalgebra hle₁
  let φ₂' : F₂ →ₐ[E] ↥(IntermediateField.fixedField H) := AlgHom.codRestrict φ₂ (IntermediateField.fixedField H).toSubalgebra hle₂
  letI alg₁ : Algebra F₁ ↥(IntermediateField.fixedField H) := φ₁'.toRingHom.toAlgebra
  letI alg₂ : Algebra F₂ ↥(IntermediateField.fixedField H) := φ₂'.toRingHom.toAlgebra
  haveI hst₁ : IsScalarTower E F₁ ↥(IntermediateField.fixedField H) := IsScalarTower.of_algebraMap_eq fun x => (φ₁'.commutes x).symm
  haveI hst₂ : IsScalarTower E F₂ ↥(IntermediateField.fixedField H) := IsScalarTower.of_algebraMap_eq fun x => (φ₂'.commutes x).symm

  let r₁ := AlgEquiv.restrictNormalHom (F := E) (K₁ := ↥(IntermediateField.fixedField H)) F₁
  let r₂ := AlgEquiv.restrictNormalHom (F := E) (K₁ := ↥(IntermediateField.fixedField H)) F₂
  have hsurj₁ : Function.Surjective r₁ := AlgEquiv.restrictNormalHom_surjective _
  have hsurj₂ : Function.Surjective r₂ := AlgEquiv.restrictNormalHom_surjective _
  have hval₁ : (IntermediateField.fixedField H).val.comp φ₁' = φ₁ := AlgHom.ext fun x => rfl
  have hval₂ : (IntermediateField.fixedField H).val.comp φ₂' = φ₂ := AlgHom.ext fun x => rfl
  have htop : (⊤ : IntermediateField E ↥(IntermediateField.fixedField H)) = φ₁'.fieldRange ⊔ φ₂'.fieldRange := by
    apply IntermediateField.map_injective (IntermediateField.fixedField H).val
    rw [IntermediateField.map_sup, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
      AlgHom.fieldRange_eq_map φ₁', AlgHom.fieldRange_eq_map φ₂', IntermediateField.map_map, IntermediateField.map_map,
      hval₁, hval₂, ← AlgHom.fieldRange_eq_map, ← AlgHom.fieldRange_eq_map, hF'K]
  have hinj : Function.Injective (r₁.prod r₂) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    rw [MonoidHom.prod_apply, Prod.mk_eq_one] at hg

    have hfix : ∀ y : ↥(IntermediateField.fixedField H), y ∈ φ₁'.fieldRange ⊔ φ₂'.fieldRange → g y = y := by
      intro y hy
      have hle : φ₁'.fieldRange ⊔ φ₂'.fieldRange ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
        refine sup_le ?_ ?_
        · rintro _ ⟨x, rfl⟩
          rw [IntermediateField.mem_fixedField_iff]
          intro h hh
          have hgx : g (φ₁' x) = φ₁' x := by
            have := AlgEquiv.restrictNormal_commutes g F₁ x
            change φ₁' (r₁ g x) = g (φ₁' x) at this
            rw [← this, hg.1]; rfl
          exact Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hgx) hh
        · rintro _ ⟨x, rfl⟩
          rw [IntermediateField.mem_fixedField_iff]
          intro h hh
          have hgx : g (φ₂' x) = φ₂' x := by
            have := AlgEquiv.restrictNormal_commutes g F₂ x
            change φ₂' (r₂ g x) = g (φ₂' x) at this
            rw [← this, hg.2]; rfl
          exact Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hgx) hh
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle hy) g (Subgroup.mem_zpowers g)
    exact AlgEquiv.ext fun y => hfix y (htop ▸ IntermediateField.mem_top)

  refine ⟨m₁ * m₂, hm, ↥(IntermediateField.fixedField H), inferInstance, inferInstance, inferInstance, hF'gal, ?_, ⟨(IntermediateField.fixedField H).val⟩, ?_, ?_, ?_, ?_⟩
  ·
    haveI : IsCyclic ((F₁ ≃ₐ[E] F₁) × (F₂ ≃ₐ[E] F₂)) := Group.isCyclic_prod_iff.2 ⟨inferInstance, inferInstance, hcop⟩
    exact isCyclic_of_injective (r₁.prod r₂) hinj
  ·
    intro w g hg
    apply hinj
    rw [map_one, MonoidHom.prod_apply, Prod.mk_eq_one]
    have hg' : g • w = w := MulAction.mem_stabilizer_iff.1 hg
    exact ⟨hinf₁ _ _ (MulAction.mem_stabilizer_iff.2 (restrictNormal_mem_stabilizer g w hg')),
      hinf₂ _ _ (MulAction.mem_stabilizer_iff.2 (restrictNormal_mem_stabilizer g w hg'))⟩
  ·
    have hcop' : Nat.Coprime n₁ n₂ := (hcop.coprime_dvd_left hdeg₁).coprime_dvd_right hdeg₂
    exact hcop'.mul_dvd_of_dvd_of_dvd (hdeg₁.trans (Subgroup.card_dvd_of_surjective r₁ hsurj₁))
      (hdeg₂.trans (Subgroup.card_dvd_of_surjective r₂ hsurj₂))
  ·
    intro v hv w hw
    have hcop' : Nat.Coprime n₁ n₂ := (hcop.coprime_dvd_left hdeg₁).coprime_dvd_right hdeg₂
    obtain ⟨rD₁, hD₁, -, -, -, -⟩ := NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower E F₁ _ w
    obtain ⟨rD₂, hD₂, -, -, -, -⟩ := NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower E F₂ _ w
    refine hcop'.mul_dvd_of_dvd_of_dvd ?_ ?_
    · refine (hloc₁ v hv (w.under (𝓞 F₁)) ?_).trans (Subgroup.card_dvd_of_surjective rD₁ hD₁)
      rw [IsDedekindDomain.HeightOneSpectrum.under_under_ringOfIntegers E F₁]; exact hw
    · refine (hloc₂ v hv (w.under (𝓞 F₂)) ?_).trans (Subgroup.card_dvd_of_surjective rD₂ hD₂)
      rw [IsDedekindDomain.HeightOneSpectrum.under_under_ringOfIntegers E F₂]; exact hw
  ·
    rw [← Nat.card_prod]
    exact Subgroup.card_dvd_of_injective (r₁.prod r₂) hinj

end S_NumberField_exists_isCyclic_algHom_cyclotomicField_mul_dvd_natCard_decomp_of_coprime
end P2MW
export P2MW.S_NumberField_exists_isCyclic_algHom_cyclotomicField_mul_dvd_natCard_decomp_of_coprime (solution)
