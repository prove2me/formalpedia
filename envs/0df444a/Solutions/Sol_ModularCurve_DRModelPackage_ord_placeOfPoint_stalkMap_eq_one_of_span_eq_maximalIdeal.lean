-- Prove2me | solution 1 for ModularCurve.DRModelPackage.ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/09d44ee5-be2c-5178-8258-0b22e03fc697

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve
open IsLocalRing

namespace OrdOne

theorem ord_eq_one_of_closedImmersion
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)
    (i : (𝔛.ratModel k).C ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) [IsClosedImmersion i]
    (y : ↥(𝔛.ratModel k).C) (hy : IsClosed ({y} : Set ↥(𝔛.ratModel k).C))
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) (hx : x = (i ≫ DRModel.baseChangeMap toκ).base y)
    (hsp : (i ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (a b : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (hmax : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x), a, b} = IsLocalRing.maximalIdeal _)
    (ha : a ∈ Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp).hom (IsLocalRing.maximalIdeal _))
    (hunr : Ideal.map ((DRModel.baseChangeMap toκ).stalkMap (i.base y)).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _) :
    ((𝔛.ratModel k).placeOfPoint ⟨y, hy⟩).ord
        ((𝔛.ratModel k).ffEquiv.symm (algebraMap _ (𝔛.ratModel k).C.functionField
          (((i ≫ DRModel.baseChangeMap toκ).stalkMap y).hom
            (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (.of_eq hx)).hom.hom b)))) = 1 := by
  subst hx

  have hcongr : ∀ s : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((i ≫ DRModel.baseChangeMap toκ).base y),
      (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr
        (.of_eq (rfl : (i ≫ DRModel.baseChangeMap toκ).base y = (i ≫ DRModel.baseChangeMap toκ).base y))).hom.hom s) = s := by
    intro s
    change ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes (specializes_refl _)).hom s = s
    rw [TopCat.Presheaf.stalkSpecializes_refl]; rfl
  rw [hcongr]

  have hinj : Function.Injective (algebraMap ((𝔛.ratModel k).C.presheaf.stalk y) (𝔛.ratModel k).C.functionField) :=
    IsFractionRing.injective _ _
  have hpC : ((p : ℕ) : (𝔛.ratModel k).C.presheaf.stalk y) = 0 := by
    apply hinj
    rw [map_natCast, map_zero]
    apply (𝔛.ratModel k).ffEquiv.symm.injective
    rw [map_natCast, map_zero]
    exact CharP.cast_eq_zero (RatFunc k) p
  have hp0 : ((i ≫ DRModel.baseChangeMap toκ).stalkMap y).hom ((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((i ≫ DRModel.baseChangeMap toκ).base y)) = 0 := by
    rw [map_natCast, hpC]

  have ha0 : ((i ≫ DRModel.baseChangeMap toκ).stalkMap y).hom a = 0 := by
    apply hinj
    rw [map_zero]

    show ((𝔛.ratModel k).C.presheaf.stalkSpecializes (genericPoint_specializes y))
      (((i ≫ DRModel.baseChangeMap toκ).stalkMap y) a) = 0
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]

    have hmem : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp).hom a ∈ IsLocalRing.maximalIdeal _ := ha
    have hnu : ¬ IsUnit (((i ≫ DRModel.baseChangeMap toκ).stalkMap (genericPoint ↥(𝔛.ratModel k).C)).hom
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp).hom a)) := fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp hmem (isUnit_of_map_unit _ _ hu)
    by_contra hne
    exact hnu (Ne.isUnit hne)

  have hgen : Ideal.map ((i ≫ DRModel.baseChangeMap toκ).stalkMap y).hom (IsLocalRing.maximalIdeal _) =
      IsLocalRing.maximalIdeal ((𝔛.ratModel k).C.presheaf.stalk y) := by
    rw [Scheme.Hom.stalkMap_comp]
    change Ideal.map ((i.stalkMap y).hom.comp ((DRModel.baseChangeMap toκ).stalkMap (i.base y)).hom) _ = _
    rw [← Ideal.map_map]
    refine (congrArg (Ideal.map (i.stalkMap y).hom) hunr).trans ?_
    have hsurj : Function.Surjective (i.stalkMap y).hom := i.stalkMap_surjective y
    rw [← IsLocalRing.maximalIdeal_comap (i.stalkMap y).hom]
    exact Ideal.map_comap_of_surjective _ hsurj _

  have hmy : IsLocalRing.maximalIdeal ((𝔛.ratModel k).C.presheaf.stalk y) = Ideal.span {((i ≫ DRModel.baseChangeMap toκ).stalkMap y).hom b} := by
    rw [← hgen, ← hmax, Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hp0, ha0]
    simp

  let Rm : (𝔛.ratModel k).C.presheaf.stalk y →+* RatFunc k :=
    ((𝔛.ratModel k).ffEquiv.symm : (𝔛.ratModel k).C.functionField ≃+* RatFunc k).toRingHom.comp
      (algebraMap ((𝔛.ratModel k).C.presheaf.stalk y) (𝔛.ratModel k).C.functionField)
  have hRm : ∀ s, Rm s = (𝔛.ratModel k).ffEquiv.symm (algebraMap _ (𝔛.ratModel k).C.functionField s) := fun s => rfl
  have hRinj : Function.Injective Rm := (𝔛.ratModel k).ffEquiv.symm.injective.comp hinj
  have hrange := (𝔛.ratModel k).range_stalk_eq ⟨y, hy⟩
  have hRmem : ∀ s, Rm s ∈ ((𝔛.ratModel k).placeOfPoint ⟨y, hy⟩).toValuationSubring := by
    intro s
    have : Rm s ∈ Rm.range := ⟨s, rfl⟩
    rw [hrange] at this
    exact this
  let ρ' : (𝔛.ratModel k).C.presheaf.stalk y →+* ↥((𝔛.ratModel k).placeOfPoint ⟨y, hy⟩).toValuationSubring :=
    Rm.codRestrict (((𝔛.ratModel k).placeOfPoint ⟨y, hy⟩).toValuationSubring.toSubring) hRmem
  have hbij : Function.Bijective ρ' := by
    refine ⟨fun s s' h => hRinj (congrArg (fun z : ↥((𝔛.ratModel k).placeOfPoint ⟨y, hy⟩).toValuationSubring => (z : RatFunc k)) h),
      fun z => ?_⟩
    have hz : (z : RatFunc k) ∈ Rm.range := by rw [hrange]; exact z.2
    obtain ⟨s, hs⟩ := hz
    exact ⟨s, Subtype.ext hs⟩
  let ρ : (𝔛.ratModel k).C.presheaf.stalk y ≃+* ↥((𝔛.ratModel k).placeOfPoint ⟨y, hy⟩).toValuationSubring :=
    RingEquiv.ofBijective ρ' hbij
  have hρ : ∀ s, ((ρ s : ↥((𝔛.ratModel k).placeOfPoint ⟨y, hy⟩).toValuationSubring) : RatFunc k) = Rm s := fun s => rfl

  have hmv : IsLocalRing.maximalIdeal ↥((𝔛.ratModel k).placeOfPoint ⟨y, hy⟩).toValuationSubring =
      Ideal.span {ρ (((i ≫ DRModel.baseChangeMap toκ).stalkMap y).hom b)} := by
    have h1 : Ideal.map ρ (IsLocalRing.maximalIdeal ((𝔛.ratModel k).C.presheaf.stalk y)) =
        IsLocalRing.maximalIdeal _ := by
      haveI := (Ideal.map_isMaximal_of_equiv ρ (p := IsLocalRing.maximalIdeal ((𝔛.ratModel k).C.presheaf.stalk y)))
      exact IsLocalRing.eq_maximalIdeal inferInstance
    rw [← h1, hmy, Ideal.map_span, Set.image_singleton]
  have hne : ρ (((i ≫ DRModel.baseChangeMap toκ).stalkMap y).hom b) ≠ 0 := by
    intro h0
    rw [h0] at hmv
    simp only [Ideal.span_singleton_eq_bot.mpr rfl] at hmv
    exact IsDiscreteValuationRing.not_a_field' (R := ↥((𝔛.ratModel k).placeOfPoint ⟨y, hy⟩).toValuationSubring) hmv
  have hirr := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hne hmv
  have := ((𝔛.ratModel k).placeOfPoint ⟨y, hy⟩).ord_coe_irreducible hirr
  rw [hρ, hRm] at this
  exact this

end OrdOne

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))

    (n : ↥(pullback (𝔛.compInf k) (𝔛.compZero k)))
    (hy₁ : IsClosed ({(pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hy₂ : IsClosed ({(pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n} : Set ↥(𝔛.ratModel k).C))
    (hx₁ : x = (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hx₂ : x = (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))
    (hsp₁ : (𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)
    (hsp₂ : (𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C) ⤳ x)

    (u v : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x)
    (hmax : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x), u, v} = IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x))
    (h𝔭₁ : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x), u} =
      Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _))
    (h𝔭₂ : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x), v} =
      Ideal.comap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hsp₂).hom (IsLocalRing.maximalIdeal _))

    (hunr₁ : Ideal.map ((DRModel.baseChangeMap toκ).stalkMap ((𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _)
    (hunr₂ : Ideal.map ((DRModel.baseChangeMap toκ).stalkMap ((𝔛.compZero k).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _) :
    ((𝔛.ratModel k).placeOfPoint ⟨((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n), hy₁⟩).ord
        ((𝔛.ratModel k).ffEquiv.symm (algebraMap _ (𝔛.ratModel k).C.functionField
          (((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).stalkMap ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base n)).hom
            (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (.of_eq hx₁)).hom.hom v)))) = 1 ∧
    ((𝔛.ratModel k).placeOfPoint ⟨((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n), hy₂⟩).ord
        ((𝔛.ratModel k).ffEquiv.symm (algebraMap _ (𝔛.ratModel k).C.functionField
          (((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).stalkMap ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base n)).hom
            (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkCongr (.of_eq hx₂)).hom.hom u)))) = 1 := by
  haveI : IsClosedImmersion (𝔛.compInf k) := 𝔛.compInf_isClosedImmersion k
  haveI : IsClosedImmersion (𝔛.compZero k) := 𝔛.compZero_isClosedImmersion k
  refine ⟨?_, ?_⟩
  · exact OrdOne.ord_eq_one_of_closedImmersion p 𝔛 O k toκ (𝔛.compInf k) _ hy₁ x hx₁ hsp₁ u v hmax
      (by rw [← h𝔭₁]; exact Ideal.subset_span (by simp)) hunr₁
  · have hmax' : Ideal.span {((p : ℕ) : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x), v, u} = IsLocalRing.maximalIdeal _ := by
      rw [← hmax]; congr 1; rw [Set.pair_comm]
    exact OrdOne.ord_eq_one_of_closedImmersion p 𝔛 O k toκ (𝔛.compZero k) _ hy₂ x hx₂ hsp₂ v u hmax'
      (by rw [← h𝔭₂]; exact Ideal.subset_span (by simp)) hunr₂

end S_ModularCurve_DRModelPackage_ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal (solution)
