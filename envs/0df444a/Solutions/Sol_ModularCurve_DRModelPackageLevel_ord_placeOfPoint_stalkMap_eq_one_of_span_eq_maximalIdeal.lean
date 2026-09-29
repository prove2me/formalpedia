-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c50ae959-0999-5cd3-b518-193bee660840

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_DRResolvedModelPackageLevel
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_ModularCurve_DRResolvedModelChartsLevelRam
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal

set_option autoImplicit false

namespace E4OrdOne

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve IsLocalRing

universe u

private theorem e4_ord_eq_one_of_closedImmersion
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] {L : Type u} [Field L] [Algebra k L] [CharP L p]
    (C : CurveModel k L) {X Y : Scheme.{u}} (i : C.C ⟶ Y) [IsClosedImmersion i] (β : Y ⟶ X) (g : C.C ⟶ X) (hg : g = i ≫ β)
    (P : closedPoints C.C) (x : X) (hx : x = g.base P.1)
    (pt : X) (hpt : g.base (genericPoint C.C) = pt) (hsp : pt ⤳ x)
    (a b : X.presheaf.stalk x)
    (hmax : Ideal.span {((p : ℕ) : X.presheaf.stalk x), a, b} = IsLocalRing.maximalIdeal _)
    (ha : a ∈ Ideal.comap (X.presheaf.stalkSpecializes hsp).hom (IsLocalRing.maximalIdeal _))
    (pt' : Y) (hpt' : i.base P.1 = pt')
    (hunr : Ideal.map ((β.stalkMap pt').hom) (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _) :
    (C.placeOfPoint P).ord
        (C.ffEquiv.symm (algebraMap _ C.C.functionField
          ((g.stalkMap P.1).hom ((X.presheaf.stalkCongr (.of_eq hx)).hom.hom b)))) = 1 := by
  subst hx hpt hpt'
  obtain ⟨y, hy⟩ := P

  have hcongr : ∀ s : X.presheaf.stalk (g.base y),
      ((X.presheaf.stalkCongr (.of_eq (rfl : g.base y = g.base y))).hom.hom s) = s := by
    intro s
    change (X.presheaf.stalkSpecializes (specializes_refl _)).hom s = s
    rw [TopCat.Presheaf.stalkSpecializes_refl]; rfl
  rw [hcongr]

  have hinj : Function.Injective (algebraMap (C.C.presheaf.stalk y) C.C.functionField) :=
    IsFractionRing.injective _ _
  have hpC : ((p : ℕ) : C.C.presheaf.stalk y) = 0 := by
    apply hinj
    rw [map_natCast, map_zero]
    apply C.ffEquiv.symm.injective
    rw [map_natCast, map_zero]
    exact CharP.cast_eq_zero L p
  have hp0 : (g.stalkMap y).hom ((p : ℕ) : X.presheaf.stalk (g.base y)) = 0 := by
    rw [map_natCast, hpC]

  have ha0 : (g.stalkMap y).hom a = 0 := by
    apply hinj
    rw [map_zero]
    show (C.C.presheaf.stalkSpecializes (genericPoint_specializes y)) ((g.stalkMap y) a) = 0
    rw [← Scheme.Hom.stalkSpecializes_stalkMap_apply]
    have hmem : (X.presheaf.stalkSpecializes hsp).hom a ∈ IsLocalRing.maximalIdeal _ := ha
    have hnu : ¬ IsUnit ((g.stalkMap (genericPoint C.C)).hom ((X.presheaf.stalkSpecializes hsp).hom a)) := fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp hmem (isUnit_of_map_unit _ _ hu)
    by_contra hne
    exact hnu (Ne.isUnit hne)

  have hgen : Ideal.map (g.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal (C.C.presheaf.stalk y) := by
    subst hg
    rw [Scheme.Hom.stalkMap_comp]
    change Ideal.map ((i.stalkMap y).hom.comp ((β.stalkMap (i.base y)).hom)) _ = _
    rw [← Ideal.map_map]
    refine (congrArg (Ideal.map (i.stalkMap y).hom) hunr).trans ?_
    have hsurj : Function.Surjective (i.stalkMap y).hom := i.stalkMap_surjective y
    rw [← IsLocalRing.maximalIdeal_comap (i.stalkMap y).hom]
    exact Ideal.map_comap_of_surjective _ hsurj _

  have hmy : IsLocalRing.maximalIdeal (C.C.presheaf.stalk y) = Ideal.span {(g.stalkMap y).hom b} := by
    rw [← hgen, ← hmax, Ideal.map_span, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton, hp0, ha0]
    simp

  let Rm : C.C.presheaf.stalk y →+* L :=
    (C.ffEquiv.symm : C.C.functionField ≃+* L).toRingHom.comp (algebraMap (C.C.presheaf.stalk y) C.C.functionField)
  have hRm : ∀ s, Rm s = C.ffEquiv.symm (algebraMap _ C.C.functionField s) := fun s => rfl
  have hRinj : Function.Injective Rm := C.ffEquiv.symm.injective.comp hinj
  have hrange := C.range_stalk_eq ⟨y, hy⟩
  have hRmem : ∀ s, Rm s ∈ (C.placeOfPoint ⟨y, hy⟩).toValuationSubring := by
    intro s
    have : Rm s ∈ Rm.range := ⟨s, rfl⟩
    rw [hrange] at this
    exact this
  let ρ' : C.C.presheaf.stalk y →+* ↥(C.placeOfPoint ⟨y, hy⟩).toValuationSubring :=
    Rm.codRestrict ((C.placeOfPoint ⟨y, hy⟩).toValuationSubring.toSubring) hRmem
  have hbij : Function.Bijective ρ' := by
    refine ⟨fun s s' h => hRinj (congrArg (fun z : ↥(C.placeOfPoint ⟨y, hy⟩).toValuationSubring => (z : L)) h), fun z => ?_⟩
    have hz : (z : L) ∈ Rm.range := by rw [hrange]; exact z.2
    obtain ⟨s, hs⟩ := hz
    exact ⟨s, Subtype.ext hs⟩
  let ρ : C.C.presheaf.stalk y ≃+* ↥(C.placeOfPoint ⟨y, hy⟩).toValuationSubring := RingEquiv.ofBijective ρ' hbij
  have hρ : ∀ s, ((ρ s : ↥(C.placeOfPoint ⟨y, hy⟩).toValuationSubring) : L) = Rm s := fun s => rfl

  have hmv : IsLocalRing.maximalIdeal ↥(C.placeOfPoint ⟨y, hy⟩).toValuationSubring = Ideal.span {ρ ((g.stalkMap y).hom b)} := by
    have h1 : Ideal.map ρ (IsLocalRing.maximalIdeal (C.C.presheaf.stalk y)) = IsLocalRing.maximalIdeal _ := by
      haveI := (Ideal.map_isMaximal_of_equiv ρ (p := IsLocalRing.maximalIdeal (C.C.presheaf.stalk y)))
      exact IsLocalRing.eq_maximalIdeal inferInstance
    rw [← h1, hmy, Ideal.map_span, Set.image_singleton]
  have hne : ρ ((g.stalkMap y).hom b) ≠ 0 := by
    intro h0
    rw [h0] at hmv
    simp only [Ideal.span_singleton_eq_bot.mpr rfl] at hmv
    exact IsDiscreteValuationRing.not_a_field' (R := ↥(C.placeOfPoint ⟨y, hy⟩).toValuationSubring) hmv
  have hirr := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hne hmv
  have := (C.placeOfPoint ⟨y, hy⟩).ord_coe_irreducible hirr
  rw [hρ, hRm] at this
  exact this

end E4OrdOne

section Face

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization MvPolynomial MvPolynomial.CrossingQuotient

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : DRLevel.R q →+* O)
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)] (toκ : O →+* ResidueField ↥A)
    [hfib0 : AlgebraicGeometry.IsIntegral (DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO))]
    (x : ↥(pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))))

    (n : ↥(pullback (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)))
    (P₀ P₁ : closedPoints ((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).C)
    (hP₀ : (𝔓.efib (ResidueField ↥A) (toκ.comp ρO)).base P₀.1 = (pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n)
    (hP₁ : (𝔓.efib (ResidueField ↥A) (toκ.comp ρO)).base P₁.1 = (pullback.snd (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n)
    (hx₀ : x = (𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base P₀.1)
    (hx₁ : x = (𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base P₁.1)
    (hsp₀ : (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ x)
    (hsp₁ : (((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).base (genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)))) ⤳ x)

    (u v : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x)
    (hmax : Ideal.span {((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x), u, v} = IsLocalRing.maximalIdeal ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x))
    (h𝔭₀ : Ideal.span {((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x), u} =
      Ideal.comap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hsp₀).hom (IsLocalRing.maximalIdeal _))
    (h𝔭₁ : Ideal.span {((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x), v} =
      Ideal.comap ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkSpecializes hsp₁).hom (IsLocalRing.maximalIdeal _))

    (hunr₀ : Ideal.map ((DRLevel.bcMap ρO toκ).stalkMap ((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0).base ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _)
    (hunr₁ : Ideal.map ((DRLevel.bcMap ρO toκ).stalkMap ((𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1).base ((pullback.snd (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n))).hom
        (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _) :
    (((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).placeOfPoint P₀).ord
        (((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).ffEquiv.symm (algebraMap _ ((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).C.functionField
          (((𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).stalkMap P₀.1).hom (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkCongr (.of_eq hx₀)).hom.hom v)))) = 1 ∧
    (((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).placeOfPoint P₁).ord
        (((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).ffEquiv.symm (algebraMap _ ((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).C.functionField
          (((𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ).stalkMap P₁.1).hom (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalkCongr (.of_eq hx₁)).hom.hom u)))) = 1 := by

  haveI : IsIso (𝔓.efib (ResidueField ↥A) (toκ.comp ρO)) := 𝔓.efib_iso (ResidueField ↥A) (toκ.comp ρO)
  haveI : ∀ i, IsClosedImmersion (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) i) := 𝔓.comp_isClosedImmersion (ResidueField ↥A) (toκ.comp ρO)
  haveI : CharP ↥(modularFunctionFieldC (ResidueField ↥A) N₀) q :=
    charP_of_injective_algebraMap (algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)).injective q

  have hη : (𝔓.efib (ResidueField ↥A) (toκ.comp ρO)).base (genericPoint ((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO))).C) =
      genericPoint ↥(DRLevel.fibre0 (N₀ := N₀) (toκ.comp ρO)) :=
    genericPoint_eq_of_isOpenImmersion _
  refine ⟨?_, ?_⟩
  · exact E4OrdOne.e4_ord_eq_one_of_closedImmersion q ((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO)))
      (𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (DRLevel.bcMap ρO toκ)
      (𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ)
      (by simp only [Category.assoc]) P₀ x hx₀ _ (by rw [← hη]; rfl) hsp₀ u v hmax
      (by rw [← h𝔭₀]; exact Ideal.subset_span (by simp)) _ (by rw [← hP₀]; rfl) hunr₀
  · have hmax' : Ideal.span {((q : ℕ) : (pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk x), v, u} =
        IsLocalRing.maximalIdeal _ := by
      rw [← hmax]; congr 1; rw [Set.pair_comm]
    exact E4OrdOne.e4_ord_eq_one_of_closedImmersion q ((𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO)))
      (𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) (DRLevel.bcMap ρO toκ)
      (𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ DRLevel.bcMap ρO toκ)
      (by simp only [Category.assoc]) P₁ x hx₁ _ (by rw [← hη]; rfl) hsp₁ v u hmax'
      (by rw [← h𝔭₁]; exact Ideal.subset_span (by simp)) _ (by rw [← hP₁]; rfl) hunr₁

end Face

#print axioms solution

end S_ModularCurve_DRModelPackageLevel_ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_ord_placeOfPoint_stalkMap_eq_one_of_span_eq_maximalIdeal (solution)
