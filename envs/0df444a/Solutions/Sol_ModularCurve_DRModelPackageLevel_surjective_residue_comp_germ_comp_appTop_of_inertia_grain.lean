-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.surjective_residue_comp_germ_comp_appTop_of_inertia_grain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/15f42dd2-484b-562c-90df-bdbf624c3e0f

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
import Theorems.Thm_ModularCurve_inertiaField_comap_isDVR_and_residue_surjective_and_place_fixed
import Theorems.Thm_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_surjective_residue_comp_germ_comp_appTop_of_inertia_grain
p2m_attr_erase "instance" "ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization MvPolynomial MvPolynomial.CrossingQuotient

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

namespace HratBridgeLevel

private theorem surjective_residue_comp_of_section
    {O : Type} [CommRing O] [IsLocalRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O))
    (t : Spec (CommRingCat.of (ResidueField O)) ⟶ X)
    (ht : t ≫ q = Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
    (x : X) (hxt : t.base (closedPoint (ResidueField O)) = x) :
    Function.Surjective ((IsLocalRing.residue (X.presheaf.stalk x)).comp
      ((X.presheaf.germ ⊤ x trivial).hom.comp
        (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom))) := by
  subst hxt
  set x := t.base (closedPoint (ResidueField O)) with hxdef
  let τ := Scheme.stalkClosedPointTo t
  haveI : IsLocalHom τ.hom := inferInstance
  let c : CommRingCat.of O ⟶ X.presheaf.stalk x := (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appTop ≫ X.presheaf.germ ⊤ x trivial
  have hc : ∀ o : O, c.hom o = (X.presheaf.germ ⊤ x trivial).hom (q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) :=
    fun o => rfl
  have hSpec_c : Spec.map c = X.fromSpecStalk x ≫ q := by
    have hq : q = X.toSpecΓ ≫ Spec.map q.appTop ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv := by
      rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    conv_rhs => rw [hq]
    rw [← Category.assoc, Scheme.fromSpecStalk_toSpecΓ]
    simp only [c, Spec.map_comp, Category.assoc]
  have hcτ : c ≫ τ = CommRingCat.ofHom (IsLocalRing.residue O) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hSpec_c, ← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, ht]
  intro ζ
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective ζ
  obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective (τ.hom a)
  refine ⟨o, ?_⟩
  change IsLocalRing.residue _ (c.hom o) = IsLocalRing.residue _ a
  have hτ : τ.hom (c.hom o) = τ.hom a := by
    change (c ≫ τ).hom o = _
    rw [hcτ]; exact ho
  apply (Ideal.Quotient.eq).mpr
  rw [IsLocalRing.mem_maximalIdeal]
  intro hu
  have h0 : τ.hom (c.hom o - a) = 0 := by rw [map_sub, hτ, sub_self]
  exact (hu.map τ.hom).ne_zero h0

end HratBridgeLevel

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q)
    (𝔓 : DRModelPackageLevel N₀ q hqN)
    [CharP (ResidueField ↥A) q] [IsAlgClosed (ResidueField ↥A)] [DecidableEq (ResidueField ↥A)]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((q : ℕ) : O)})
    (ρO : DRLevel.R q →+* O)
    (hρO : ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
        (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom))).comp ρO =
      algebraMap (DRLevel.R q) (AlgebraicClosure ℚ))
    (toκ : O →+* (ResidueField ↥A))
    (htoκ : ∀ o : O, toκ o = (residue ↥A) ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)
    (hred : Function.Surjective (IsLocalRing.residue ↥A))
    (n : ↥(pullback (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1))) :
    Function.Surjective ((IsLocalRing.residue ((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base n))).comp
      (((pullback (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).presheaf.germ ⊤ ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫ (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) ≫ DRLevel.bcMap ρO toκ).base n) trivial).hom.comp
        (((pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO))).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom))) := by
  classical

  obtain ⟨_, _, hres, _⟩ :=
    ModularCurve.inertiaField_comap_isDVR_and_residue_surjective_and_place_fixed q A hA N₀
  have hsurj : Function.Surjective toκ := by
    intro c
    obtain ⟨x, hx⟩ := hres c
    refine ⟨eO.symm x, ?_⟩
    rw [htoκ, RingEquiv.apply_symm_apply]
    exact hx

  have hkerle : IsLocalRing.maximalIdeal O ≤ RingHom.ker toκ := by
    rw [hϖO, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast]
    exact CharP.cast_eq_zero _ q
  haveI : IsLocalHom toκ := ⟨fun a ha => by
    by_contra h
    exact ha.ne_zero (RingHom.mem_ker.mp (hkerle ((IsLocalRing.mem_maximalIdeal a).mpr h)))⟩
  have hιbij : Function.Bijective (IsLocalRing.ResidueField.lift toκ) :=
    ⟨(IsLocalRing.ResidueField.lift toκ).injective, fun c => by
      obtain ⟨o, rfl⟩ := hsurj c
      exact ⟨residue O o, IsLocalRing.ResidueField.lift_residue_apply toκ o⟩⟩
  let eκ : ResidueField O ≃+* ResidueField ↥A := RingEquiv.ofBijective (IsLocalRing.ResidueField.lift toκ) hιbij
  have heκ : (eκ.symm : ResidueField ↥A →+* ResidueField O).comp toκ = residue O := by
    ext o
    apply eκ.injective
    show eκ (eκ.symm (toκ o)) = IsLocalRing.ResidueField.lift toκ (residue O o)
    rw [RingEquiv.apply_symm_apply, IsLocalRing.ResidueField.lift_residue_apply]

  obtain ⟨⟨hcl, -⟩, -⟩ := 𝔓.node_pin (ResidueField ↥A) (toκ.comp ρO) n
  obtain ⟨z, hz⟩ := AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton (ResidueField ↥A)
    (𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO)).toBase _ (mem_closedPoints_iff.mp hcl)

  let t : Spec (CommRingCat.of (ResidueField O)) ⟶ DRLevel.XO (N₀ := N₀) ρO :=
    Spec.map (CommRingCat.ofHom (eκ.symm : ResidueField ↥A →+* ResidueField O)) ≫ z.left ≫
      𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫ 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ
  have h1 : DRLevel.bcMap (N₀ := N₀) ρO toκ ≫ pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
      pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) ≫ Spec.map (CommRingCat.ofHom toκ) := by
    simp only [DRLevel.bcMap, pullback.map, pullback.lift_snd]
  have h2 : 𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0 ≫
      pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) =
      pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) := 𝔓.comp_over _ _ 0
  have h3 : 𝔓.efib (ResidueField ↥A) (toκ.comp ρO) ≫
      pullback.snd (DRLevel.toBase0 N₀ q) (Spec.map (CommRingCat.ofHom (toκ.comp ρO))) =
      (𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO)).toBase := 𝔓.hefib _ _
  have h4 : z.left ≫ (𝔓.Mfib (ResidueField ↥A) (toκ.comp ρO)).toBase = 𝟙 _ := by
    simpa only [Over.mk_left, Over.mk_hom] using Over.w z
  have ht : t ≫ pullback.snd (DRLevel.toBase N₀ q) (Spec.map (CommRingCat.ofHom ρO)) =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) := by
    simp only [t, Category.assoc, h1]
    erw [reassoc_of% h2, reassoc_of% h3, reassoc_of% h4]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, heκ]
  have hinv : (𝔓.efib (ResidueField ↥A) (toκ.comp ρO)).base ((inv (𝔓.efib (ResidueField ↥A) (toκ.comp ρO))).base
      ((pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n)) =
      (pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1)).base n := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hxt : t.base (closedPoint (ResidueField O)) =
      (pullback.fst (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0) (𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 1) ≫
        𝔓.comp (ResidueField ↥A) (toκ.comp ρO) 0 ≫ DRLevel.bcMap ρO toκ).base n := by
    simp only [t, Scheme.Hom.comp_apply]
    rw [← hinv, ← hz]
    exact congrArg _ (congrArg _ (congrArg _ (congrArg _ (Subsingleton.elim _ _))))

  exact HratBridgeLevel.surjective_residue_comp_of_section _ t ht _ hxt

end S_ModularCurve_DRModelPackageLevel_surjective_residue_comp_germ_comp_appTop_of_inertia_grain
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_surjective_residue_comp_germ_comp_appTop_of_inertia_grain (solution)
