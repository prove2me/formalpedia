-- Prove2me | solution 1 for NeronModelInfra.exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3e38a533-5ee1-5265-a632-f11830339bf2

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_NeronModelInfra_WeakNeronModel
import Theorems.Thm_NeronModelInfra_exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative
import Theorems.Thm_NeronModelInfra_exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension
import Theorems.Thm_NeronModelInfra_exists_opens_relativeGroupLaw_isOpenImmersion_genericFibre_iso_of_isOpenImmersion_lift_mul_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory NeronModelInfra.ComponentReading.isDomain NeronModelInfra.MinimalComponentData.finite NeronModelInfra.ComponentReading.isDiscreteValuationRing NeronModelInfra.ComponentReading.locallyOfFiniteType NeronModelInfra.ComponentReading.smooth NeronModelInfra.MinimalComponentData.nonempty NeronModelInfra.ComponentReading.isOpenImmersion PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited NeronModelInfra.isOpenImmersion_specGenericFibreInclusion NeronModelInfra.isLocalizationAway_uniformizer_zp instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj NeronModelInfra.MinimalComponentData.mk.injEq NeronModelInfra.ComponentReading.mk.injEq NeronModelInfra.ComponentReading.mk.sizeOf_spec NeronModelInfra.MinimalComponentData.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.DescentAction.toTriple_fst_assoc AlgebraicGeometry.DescentAction.invol_snd_assoc AlgebraicGeometry.DescentAction.unitMap_fst AlgebraicGeometry.DescentAction.flipMap_snd_assoc AlgebraicGeometry.DescentAction.actMap_snd_assoc AlgebraicGeometry.DescentAction.unitMap_fst_assoc AlgebraicGeometry.DescentAction.unitMap_snd AlgebraicGeometry.DescentAction.eRel_snd AlgebraicGeometry.DescentAction.toTriple_fst AlgebraicGeometry.DescentAction.invol_invol AlgebraicGeometry.DescentAction.proj₁₃_snd AlgebraicGeometry.DescentAction.eRel_snd_assoc AlgebraicGeometry.DescentAction.invol_invol_assoc AlgebraicGeometry.DescentAction.invol_act AlgebraicGeometry.DescentAction.actMap_fst_assoc AlgebraicGeometry.DescentAction.flipMap_fst_assoc AlgebraicGeometry.DescentAction.eRel_fst_assoc AlgebraicGeometry.DescentAction.eRel_fst AlgebraicGeometry.DescentAction.invol_act_assoc AlgebraicGeometry.DescentAction.invol_fst_assoc AlgebraicGeometry.DescentAction.proj₁₃_snd_assoc AlgebraicGeometry.DescentAction.mk.injEq AlgebraicGeometry.DescentAction.flipMap_fst AlgebraicGeometry.DescentAction.proj₁₃_fst AlgebraicGeometry.DescentAction.invol_fst AlgebraicGeometry.DescentAction.unitMap_snd_assoc AlgebraicGeometry.DescentAction.actMap_fst AlgebraicGeometry.DescentAction.toTriple_snd_assoc AlgebraicGeometry.DescentAction.invol_snd AlgebraicGeometry.DescentAction.actMap_snd AlgebraicGeometry.DescentAction.flipMap_snd AlgebraicGeometry.DescentAction.proj₁₃_fst_assoc AlgebraicGeometry.DescentAction.mk.sizeOf_spec AlgebraicGeometry.DescentAction.toTriple_snd"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mNeronN34H

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable def prodMap {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g) :
    pullback z f ⟶ pullback z g :=
  pullback.map z f z g (𝟙 Z) j.1 (𝟙 _) ((Category.comp_id _).trans (Category.id_comp z).symm)
    ((Category.comp_id _).trans j.2.symm)

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[reassoc (attr := simp)]
theorem prodMap_fst {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g) :
    prodMap z f g j ≫ pullback.fst z g = pullback.fst z f := by
  rw [prodMap, pullback.map, pullback.lift_fst, Category.comp_id]

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[reassoc (attr := simp)]
theorem prodMap_snd {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g) :
    prodMap z f g j ≫ pullback.snd z g = pullback.snd z f ≫ j.1 := by
  rw [prodMap, pullback.map, pullback.lift_snd]

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem isOpenImmersion_prodMap {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g)
    [IsOpenImmersion j.1] : IsOpenImmersion (prodMap z f g j) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) (IsOpenImmersion.of_isIso (𝟙 Z)) ‹_›
    (Category.id_comp z).symm j.2.symm

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem range_prodMap {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g) :
    Set.range (prodMap z f g j).base = (pullback.snd z g).base ⁻¹' Set.range j.1.base := by
  have h := Scheme.Pullback.range_map z f z g (𝟙 Z) j.1 (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp z).symm) ((Category.comp_id _).trans j.2.symm)
  change Set.range (prodMap z f g j).base = _ at h
  rw [h]
  ext p
  simp

theorem exists_preimage_maximal {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g)
    [IsOpenImmersion j.1]
    (hj₂ : ∀ b : B, g.base b = IsLocalRing.closedPoint R →
      (∀ y : B, y ⤳ b → g.base y = IsLocalRing.closedPoint R → y = b) → b ∈ Set.range j.1.base)
    (η' : ↑(pullback z g)) (hη' : (pullback.fst z g ≫ z).base η' = IsLocalRing.closedPoint R)
    (hmax' : ∀ y : ↑(pullback z g), y ⤳ η' → (pullback.fst z g ≫ z).base y = IsLocalRing.closedPoint R →
      y = η') :
    ∃ η : ↑(pullback z f), (prodMap z f g j).base η = η' ∧
      (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R ∧
      (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η) := by
  haveI := isOpenImmersion_prodMap z f g j

  have hb : g.base ((pullback.snd z g).base η') = IsLocalRing.closedPoint R := by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition]; exact hη'
  have hbmax : ∀ y : B, y ⤳ (pullback.snd z g).base η' → g.base y = IsLocalRing.closedPoint R →
      y = (pullback.snd z g).base η' := by
    intro y hy hys
    obtain ⟨x, hx, hxy⟩ := Flat.generalizingMap (pullback.snd z g) hy
    have hxs : (pullback.fst z g ≫ z).base x = IsLocalRing.closedPoint R := by
      rw [pullback.condition, Scheme.Hom.comp_apply, hxy]; exact hys
    rw [← hxy, hmax' x hx hxs]
  have hmem : η' ∈ Set.range (prodMap z f g j).base := by
    rw [range_prodMap]
    exact hj₂ _ hb hbmax
  obtain ⟨η, hη⟩ := hmem
  refine ⟨η, hη, ?_, ?_⟩
  · rw [← prodMap_fst z f g j, Category.assoc, Scheme.Hom.comp_apply, hη]; exact hη'
  · intro y hy hys
    apply (prodMap z f g j).isOpenEmbedding.injective
    rw [hη]
    apply hmax' _ ((hy.map (prodMap z f g j).base.hom.continuous).trans (hη ▸ specializes_rfl))
    rw [← prodMap_fst z f g j, Category.assoc, Scheme.Hom.comp_apply] at hys
    exact hys

noncomputable def prodMapOver {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g) :
    SchemeHomOver (pullback.fst z f ≫ z) (pullback.fst z g ≫ z) :=
  ⟨prodMap z f g j, by rw [prodMap_fst_assoc]⟩

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[scoped simp]
theorem prodMapOver_coe {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R)) (j : SchemeHomOver f g) :
    (prodMapOver z f g j).1 = prodMap z f g j :=
  rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem transport_twistK
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R))
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (LB : RelativeGroupLaw R g) (j : SchemeHomOver f g)
    (e' : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
      NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e' =
        LXK.mul t (NeronModelInfra.schemeHomOverComp x e') (NeronModelInfra.schemeHomOverComp y e'))
    (hcompat : NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K g f j) e' = e)
    (uK' : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K))
      (pullback.snd g (specGenericFibreInclusion R K))) :
    NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K (pullback.fst z g ≫ z) (pullback.fst z f ≫ z) (prodMapOver z f g j))
        (NeronModelInfra.schemeHomOverComp
          ((LB.genericFibre K).mul (pullback.snd (pullback.fst z g ≫ z) (specGenericFibreInclusion R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K z (pullback.fst z g ≫ z) ⟨pullback.fst z g, rfl⟩) uK')
            (genericFibreRestrict R K g (pullback.fst z g ≫ z)
              ⟨pullback.snd z g, pullback.condition.symm⟩)) e') =
      LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩)
          (NeronModelInfra.schemeHomOverComp uK' e'))
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K f (pullback.fst z f ≫ z) ⟨pullback.snd z f, pullback.condition.symm⟩)
          e) := by

  have h1 : NeronModelInfra.schemeHomOverComp (prodMapOver z f g j)
      (⟨pullback.fst z g, rfl⟩ : SchemeHomOver (pullback.fst z g ≫ z) z) =
        (⟨pullback.fst z f, rfl⟩ : SchemeHomOver (pullback.fst z f ≫ z) z) :=
    Subtype.ext (prodMap_fst z f g j)
  have h2 : NeronModelInfra.schemeHomOverComp (prodMapOver z f g j)
      (⟨pullback.snd z g, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst z g ≫ z) g) =
        NeronModelInfra.schemeHomOverComp
          (⟨pullback.snd z f, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst z f ≫ z) f) j :=
    Subtype.ext (prodMap_snd z f g j)
  rw [hhom]

  have hnat : ∀ (a b : SchemeHomOver (pullback.snd (pullback.fst z g ≫ z) (specGenericFibreInclusion R K)) gK),
      NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K (pullback.fst z g ≫ z) (pullback.fst z f ≫ z) (prodMapOver z f g j))
        (LXK.mul _ a b) =
      LXK.mul _
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K (pullback.fst z g ≫ z) (pullback.fst z f ≫ z) (prodMapOver z f g j)) a)
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K (pullback.fst z g ≫ z) (pullback.fst z f ≫ z) (prodMapOver z f g j)) b) := by
    intro a b
    exact LXK.mul_natural _ _ _
      (genericFibreRestrict R K (pullback.fst z g ≫ z) (pullback.fst z f ≫ z) (prodMapOver z f g j)).2 a b
  rw [hnat]
  congr 1
  · rw [← schemeHomOverComp_assoc, ← schemeHomOverComp_assoc, ← genericFibreRestrict_schemeHomOverComp, h1,
      schemeHomOverComp_assoc]
  · rw [← schemeHomOverComp_assoc, ← genericFibreRestrict_schemeHomOverComp, h2,
      genericFibreRestrict_schemeHomOverComp, schemeHomOverComp_assoc, hcompat]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem genericFibreRestrict_fst_assoc {P Q W : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R))
    (q : Q ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver q p) (h : P ⟶ W) :
    (genericFibreRestrict R K p q φ).1 ≫ pullback.fst p (specGenericFibreInclusion R K) ≫ h =
      pullback.fst q (specGenericFibreInclusion R K) ≫ φ.1 ≫ h := by
  rw [← Category.assoc, genericFibreRestrict_coe_comp_fst, Category.assoc]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem restrict_comp_genericFibre {P P' : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R))
    (p' : P' ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver p p') (U : P.Opens) (U' : P'.Opens)
    (ψ : SchemeHomOver (U'.ι ≫ p') (U.ι ≫ p)) (hψ : ψ.1 ≫ U.ι ≫ φ.1 = U'.ι) :
    (genericFibreRestrict R K (U.ι ≫ p) (U'.ι ≫ p') ψ).1 ≫
      pullback.map (U.ι ≫ p) (specGenericFibreInclusion R K) p (specGenericFibreInclusion R K) U.ι (𝟙 _)
        (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
      (genericFibreRestrict R K p' p φ).1 =
    pullback.map (U'.ι ≫ p') (specGenericFibreInclusion R K) p' (specGenericFibreInclusion R K) U'.ι (𝟙 _)
        (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, genericFibreRestrict_coe_comp_fst,
      genericFibreRestrict_fst_assoc, hψ]
  · simp only [Category.assoc, pullback.lift_snd, genericFibreRestrict_coe_comp_snd, Category.comp_id]

omit [IsFractionRing R K] in

theorem twist
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {Z X B : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (f : X ⟶ Spec (CommRingCat.of R)) (g : B ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (LB : RelativeGroupLaw R g) (j : SchemeHomOver f g) [IsOpenImmersion j.1]
    (hj₂ : ∀ b : B, g.base b = IsLocalRing.closedPoint R →
      (∀ y : B, y ⤳ b → g.base y = IsLocalRing.closedPoint R → y = b) → b ∈ Set.range j.1.base)
    (e' : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK) [IsIso e'.1]
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
        (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
      NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e' =
        LXK.mul t (NeronModelInfra.schemeHomOverComp x e') (NeronModelInfra.schemeHomOverComp y e'))
    (hcompat : NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K g f j) e' = e)
    (hL : ∀ (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
      (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
              (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                  ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1)
    (uK' : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K))
      (pullback.snd g (specGenericFibreInclusion R K)))
    (η' : ↑(pullback z g)) (hη' : (pullback.fst z g ≫ z).base η' = IsLocalRing.closedPoint R)
    (hmax' : ∀ y : ↑(pullback z g), y ⤳ η' → (pullback.fst z g ≫ z).base y = IsLocalRing.closedPoint R →
      y = η') :
    ∃ (U' : (pullback z g).Opens) (_ : η' ∈ U') (τ' : SchemeHomOver (U'.ι ≫ pullback.fst z g ≫ z) g),
      (genericFibreRestrict R K g (U'.ι ≫ pullback.fst z g ≫ z) τ').1 =
        pullback.map (U'.ι ≫ pullback.fst z g ≫ z) (specGenericFibreInclusion R K)
            (pullback.fst z g ≫ z) (specGenericFibreInclusion R K) U'.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
          ((LB.genericFibre K).mul (pullback.snd (pullback.fst z g ≫ z) (specGenericFibreInclusion R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K z (pullback.fst z g ≫ z) ⟨pullback.fst z g, rfl⟩) uK')
            (genericFibreRestrict R K g (pullback.fst z g ≫ z)
              ⟨pullback.snd z g, pullback.condition.symm⟩)).1 := by
  haveI := isOpenImmersion_prodMap z f g j

  obtain ⟨η, hη, hηs, hηmax⟩ := exists_preimage_maximal z f g j hj₂ η' hη' hmax'

  obtain ⟨U, hηU, τ, hτK⟩ := hL (NeronModelInfra.schemeHomOverComp uK' e') η hηs hηmax

  have hinv : ((prodMap z f g j).isoImage U).inv ≫ U.ι ≫ prodMap z f g j = ((prodMap z f g j) ''ᵁ U).ι :=
    (prodMap z f g j).isoImage_inv_ι U
  let ψ : SchemeHomOver (((prodMap z f g j) ''ᵁ U).ι ≫ pullback.fst z g ≫ z) (U.ι ≫ pullback.fst z f ≫ z) :=
    ⟨((prodMap z f g j).isoImage U).inv, by rw [← hinv, Category.assoc, Category.assoc, prodMap_fst_assoc]⟩
  refine ⟨(prodMap z f g j) ''ᵁ U, ?_,
    NeronModelInfra.schemeHomOverComp ψ (NeronModelInfra.schemeHomOverComp τ j), ?_⟩
  · rw [← hη]; exact ⟨η, hηU, rfl⟩

  rw [← cancel_mono e'.1]
  have hgen : genericFibreRestrict R K g _
      (NeronModelInfra.schemeHomOverComp ψ (NeronModelInfra.schemeHomOverComp τ j)) =
      NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K _ _ ψ)
        (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f _ τ)
          (genericFibreRestrict R K g f j)) := by
    rw [genericFibreRestrict_schemeHomOverComp, genericFibreRestrict_schemeHomOverComp]
  have hτK' := hτK
  rw [NeronModelInfra.schemeHomOverComp_coe,
    show e.1 = (genericFibreRestrict R K g f j).1 ≫ e'.1 by
      rw [← hcompat, NeronModelInfra.schemeHomOverComp_coe]] at hτK'
  have htr := congrArg Subtype.val (transport_twistK K LXK z f g e LB j e' hhom hcompat uK')
  simp only [NeronModelInfra.schemeHomOverComp_coe] at htr
  rw [hgen]
  simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
  rw [hτK', ← htr,
    ← restrict_comp_genericFibre K (pullback.fst z f ≫ z) (pullback.fst z g ≫ z) (prodMapOver z f g j) U _ ψ
      hinv]
  simp only [Category.assoc]

end P2mNeronN34H
p2m_reactivate "P2MW.S_NeronModelInfra_exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative.P2mNeronN34H"

namespace P2mNeronN34H

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

theorem map_maximal {P Q : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R)) (q : Q ⟶ Spec (CommRingCat.of R))
    (φ : SchemeHomOver p q) [IsOpenImmersion φ.1] (η : P) (hη : p.base η = IsLocalRing.closedPoint R)
    (hmax : ∀ y : P, y ⤳ η → p.base y = IsLocalRing.closedPoint R → y = η) :
    q.base (φ.1.base η) = IsLocalRing.closedPoint R ∧
      ∀ y : Q, y ⤳ φ.1.base η → q.base y = IsLocalRing.closedPoint R → y = φ.1.base η := by
  refine ⟨by rw [← Scheme.Hom.comp_apply, φ.2]; exact hη, fun y hy hys => ?_⟩
  obtain ⟨y₁, rfl⟩ : y ∈ Set.range φ.1.base := hy.mem_open (IsOpenImmersion.isOpen_range φ.1) ⟨η, rfl⟩
  rw [hmax y₁ ((φ.1.isOpenEmbedding.isInducing.specializes_iff).1 hy)
    (by rw [← φ.2, Scheme.Hom.comp_apply]; exact hys)]

theorem maximal_of_opens {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R)) (U : P.Opens) (η : P) (hηU : η ∈ U)
    (hmax : ∀ y : P, y ⤳ η → p.base y = IsLocalRing.closedPoint R → y = η) :
    ∀ y : ↑U, y ⤳ (⟨η, hηU⟩ : ↑U) → (U.ι ≫ p).base y = IsLocalRing.closedPoint R → y = ⟨η, hηU⟩ := by
  intro y hy hys
  apply U.ι.isOpenEmbedding.injective
  have h := hmax (U.ι.base y) (by simpa using hy.map U.ι.base.hom.continuous)
    (by rw [← Scheme.Hom.comp_apply]; exact hys)
  simpa using h

theorem snd_maximal {Z X : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (f : X ⟶ Spec (CommRingCat.of R)) (θ : ↑(pullback z f))
    (hθ : (pullback.fst z f ≫ z).base θ = IsLocalRing.closedPoint R)
    (hmax : ∀ y : ↑(pullback z f), y ⤳ θ → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = θ) :
    f.base ((pullback.snd z f).base θ) = IsLocalRing.closedPoint R ∧
      ∀ y : X, y ⤳ (pullback.snd z f).base θ → f.base y = IsLocalRing.closedPoint R →
        y = (pullback.snd z f).base θ := by
  refine ⟨by rw [← Scheme.Hom.comp_apply, ← pullback.condition]; exact hθ, fun y hy hys => ?_⟩
  obtain ⟨x, hx, hxy⟩ := Flat.generalizingMap (pullback.snd z f) hy
  have hxs : (pullback.fst z f ≫ z).base x = IsLocalRing.closedPoint R := by
    rw [pullback.condition, Scheme.Hom.comp_apply, hxy]; exact hys
  rw [← hxy, hmax x hx hxs]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem genericFibre_comp_restrict {P P' : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of R))
    (p' : P' ⟶ Spec (CommRingCat.of R)) (φ : SchemeHomOver p' p) (U : P.Opens) (U' : P'.Opens)
    (ψ : SchemeHomOver (U'.ι ≫ p') (U.ι ≫ p)) (hψ : ψ.1 ≫ U.ι = U'.ι ≫ φ.1) :
    (genericFibreRestrict R K (U.ι ≫ p) (U'.ι ≫ p') ψ).1 ≫
      pullback.map (U.ι ≫ p) (specGenericFibreInclusion R K) p (specGenericFibreInclusion R K) U.ι (𝟙 _)
        (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) =
    pullback.map (U'.ι ≫ p') (specGenericFibreInclusion R K) p' (specGenericFibreInclusion R K) U'.ι (𝟙 _)
        (𝟙 _) (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
      (genericFibreRestrict R K p p' φ).1 := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, genericFibreRestrict_coe_comp_fst,
      genericFibreRestrict_fst_assoc, pullback.lift_fst_assoc, hψ]
  · simp only [Category.assoc, pullback.lift_snd, genericFibreRestrict_coe_comp_snd, Category.comp_id]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem transport_mulK
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {Z X : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R))
    (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK) (X' : X.Opens)
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK) :
    NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K (pullback.fst z f ≫ z) (pullback.fst z (X'.ι ≫ f) ≫ z)
          (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩))
        (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
          (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (pullback.fst z f ≫ z) ⟨pullback.snd z f, pullback.condition.symm⟩)
            e)) =
      LXK.mul (pullback.snd (pullback.fst z (X'.ι ≫ f) ≫ z) (specGenericFibreInclusion R K))
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K z (pullback.fst z (X'.ι ≫ f) ≫ z) ⟨pullback.fst z (X'.ι ≫ f), rfl⟩) uK)
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K (X'.ι ≫ f) (pullback.fst z (X'.ι ≫ f) ≫ z)
            ⟨pullback.snd z (X'.ι ≫ f), pullback.condition.symm⟩)
          (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩) e)) := by
  have h1 : NeronModelInfra.schemeHomOverComp (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩)
      (⟨pullback.fst z f, rfl⟩ : SchemeHomOver (pullback.fst z f ≫ z) z) =
        (⟨pullback.fst z (X'.ι ≫ f), rfl⟩ : SchemeHomOver (pullback.fst z (X'.ι ≫ f) ≫ z) z) :=
    Subtype.ext (prodMap_fst z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩)
  have h2 : NeronModelInfra.schemeHomOverComp (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩)
      (⟨pullback.snd z f, pullback.condition.symm⟩ : SchemeHomOver (pullback.fst z f ≫ z) f) =
        NeronModelInfra.schemeHomOverComp
          (⟨pullback.snd z (X'.ι ≫ f), pullback.condition.symm⟩ :
            SchemeHomOver (pullback.fst z (X'.ι ≫ f) ≫ z) (X'.ι ≫ f))
          (⟨X'.ι, rfl⟩ : SchemeHomOver (X'.ι ≫ f) f) :=
    Subtype.ext (prodMap_snd z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩)

  have hnat : ∀ (a b : SchemeHomOver (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K)) gK),
      NeronModelInfra.schemeHomOverComp
        (genericFibreRestrict R K (pullback.fst z f ≫ z) (pullback.fst z (X'.ι ≫ f) ≫ z)
          (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩))
        (LXK.mul _ a b) =
      LXK.mul _
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K (pullback.fst z f ≫ z) (pullback.fst z (X'.ι ≫ f) ≫ z)
            (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩)) a)
        (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K (pullback.fst z f ≫ z) (pullback.fst z (X'.ι ≫ f) ≫ z)
            (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩)) b) := by
    intro a b
    exact LXK.mul_natural _ _ _
      (genericFibreRestrict R K (pullback.fst z f ≫ z) (pullback.fst z (X'.ι ≫ f) ≫ z)
        (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩)).2 a b
  rw [hnat]
  congr 1
  · rw [← schemeHomOverComp_assoc, ← genericFibreRestrict_schemeHomOverComp, h1]
  · rw [← schemeHomOverComp_assoc, ← genericFibreRestrict_schemeHomOverComp, h2,
      genericFibreRestrict_schemeHomOverComp, schemeHomOverComp_assoc]

omit [IsFractionRing R K] in

theorem restrict_translation
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} (LXK : RelativeGroupLaw K gK)
    {Z X : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z]
    (f : X ⟶ Spec (CommRingCat.of R)) (e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK)
    (X' : X.Opens)
    (hX'₂ : ∀ x : X, f.base x = IsLocalRing.closedPoint R →
      (∀ y : X, y ⤳ x → f.base y = IsLocalRing.closedPoint R → y = x) → x ∈ X')
    (hL : ∀ (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
      (η : ↑(pullback z f)), (pullback.fst z f ≫ z).base η = IsLocalRing.closedPoint R →
      (∀ y : ↑(pullback z f), y ⤳ η → (pullback.fst z f ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
      ∃ (U : (pullback z f).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) f),
        IsOpenImmersion
          (pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
            ((Category.assoc _ _ _).trans τ.2.symm)) ∧
        (NeronModelInfra.schemeHomOverComp
            (genericFibreRestrict R K f (U.ι ≫ pullback.fst z f ≫ z) τ) e).1 =
          pullback.map (U.ι ≫ pullback.fst z f ≫ z) (specGenericFibreInclusion R K)
              (pullback.fst z f ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
              (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
            (LXK.mul (pullback.snd (pullback.fst z f ≫ z) (specGenericFibreInclusion R K))
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K z (pullback.fst z f ≫ z) ⟨pullback.fst z f, rfl⟩) uK)
              (NeronModelInfra.schemeHomOverComp
                (genericFibreRestrict R K f (pullback.fst z f ≫ z)
                  ⟨pullback.snd z f, pullback.condition.symm⟩) e)).1)
    (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K)) gK)
    (η₁ : ↑(pullback z (X'.ι ≫ f)))
    (hη₁ : (pullback.fst z (X'.ι ≫ f) ≫ z).base η₁ = IsLocalRing.closedPoint R)
    (hmax₁ : ∀ y : ↑(pullback z (X'.ι ≫ f)), y ⤳ η₁ →
      (pullback.fst z (X'.ι ≫ f) ≫ z).base y = IsLocalRing.closedPoint R → y = η₁) :
    ∃ (U₁ : (pullback z (X'.ι ≫ f)).Opens) (_ : η₁ ∈ U₁)
      (τ₁ : SchemeHomOver (U₁.ι ≫ pullback.fst z (X'.ι ≫ f) ≫ z) (X'.ι ≫ f)),
      (NeronModelInfra.schemeHomOverComp
          (genericFibreRestrict R K (X'.ι ≫ f) (U₁.ι ≫ pullback.fst z (X'.ι ≫ f) ≫ z) τ₁)
          (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩) e)).1 =
        pullback.map (U₁.ι ≫ pullback.fst z (X'.ι ≫ f) ≫ z) (specGenericFibreInclusion R K)
            (pullback.fst z (X'.ι ≫ f) ≫ z) (specGenericFibreInclusion R K) U₁.ι (𝟙 _) (𝟙 _)
            (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
          (LXK.mul (pullback.snd (pullback.fst z (X'.ι ≫ f) ≫ z) (specGenericFibreInclusion R K))
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K z (pullback.fst z (X'.ι ≫ f) ≫ z) ⟨pullback.fst z (X'.ι ≫ f), rfl⟩) uK)
            (NeronModelInfra.schemeHomOverComp
              (genericFibreRestrict R K (X'.ι ≫ f) (pullback.fst z (X'.ι ≫ f) ≫ z)
                ⟨pullback.snd z (X'.ι ≫ f), pullback.condition.symm⟩)
              (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩) e))).1 := by

  haveI hQ : IsOpenImmersion (prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩) := isOpenImmersion_prodMap z (X'.ι ≫ f) f _
  haveI hQ' : IsOpenImmersion (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩).1 := hQ

  obtain ⟨hη, hmax⟩ := map_maximal (pullback.fst z (X'.ι ≫ f) ≫ z) (pullback.fst z f ≫ z)
    (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩) η₁ hη₁ hmax₁
  simp only [prodMapOver_coe] at hη hmax

  obtain ⟨U, hηU, τ, hoi, hτK⟩ := hL uK _ hη hmax

  have hτη : τ.1.base ⟨(prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩).base η₁, hηU⟩ ∈ X' := by
    let Φ : SchemeHomOver (U.ι ≫ pullback.fst z f ≫ z) (pullback.fst z f ≫ z) :=
      ⟨pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1 ((Category.assoc _ _ _).trans τ.2.symm),
        by rw [pullback.lift_fst_assoc, Category.assoc]⟩
    haveI : IsOpenImmersion Φ.1 := hoi
    obtain ⟨hθ, hθmax⟩ := map_maximal (U.ι ≫ pullback.fst z f ≫ z) (pullback.fst z f ≫ z) Φ ⟨_, hηU⟩
      (by rw [Scheme.Hom.comp_apply]; exact hη) (maximal_of_opens (pullback.fst z f ≫ z) U _ hηU hmax)
    obtain ⟨hs, hsmax⟩ := snd_maximal z f _ hθ hθmax
    have hsnd : (pullback.snd z f).base (Φ.1.base ⟨_, hηU⟩) = τ.1.base ⟨_, hηU⟩ := by
      show (pullback.snd z f).base ((pullback.lift (f := z) (g := f) (U.ι ≫ pullback.fst z f) τ.1
        ((Category.assoc _ _ _).trans τ.2.symm)).base _) = _
      rw [← Scheme.Hom.comp_apply, pullback.lift_snd]
    rw [hsnd] at hs hsmax
    exact hX'₂ _ hs hsmax

  let V : (↑U : Scheme.{u}).Opens := τ.1 ⁻¹ᵁ X'
  let U₀ : (pullback z f).Opens := U.ι ''ᵁ V
  let U₁ : (pullback z (X'.ι ≫ f)).Opens := (prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩) ⁻¹ᵁ U₀
  have hη₁U₁ : η₁ ∈ U₁ := by
    change (prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩).base η₁ ∈ U.ι ''ᵁ V
    exact ⟨⟨_, hηU⟩, hτη, rfl⟩

  have hr₁ : Set.range (U₁.ι ≫ prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩).base ⊆ Set.range U.ι.base := by
    rintro _ ⟨u₁, rfl⟩
    obtain ⟨v, -, hv⟩ : (prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩).base (U₁.ι.base u₁) ∈ (U₀ : Set _) := u₁.2
    exact ⟨v, by rw [Scheme.Hom.comp_apply]; exact hv⟩
  let l₁ : (↑U₁ : Scheme.{u}) ⟶ ↑U := IsOpenImmersion.lift U.ι (U₁.ι ≫ prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩) hr₁
  have hl₁ : l₁ ≫ U.ι = U₁.ι ≫ prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩ := IsOpenImmersion.lift_fac _ _ _
  have hl₁V : ∀ u₁ : ↑U₁, l₁.base u₁ ∈ V := by
    intro u₁
    obtain ⟨v, hvV, hv⟩ : (prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩).base (U₁.ι.base u₁) ∈ (U₀ : Set _) := u₁.2
    have : v = l₁.base u₁ := by
      apply U.ι.isOpenEmbedding.injective
      have h' : U.ι.base (l₁.base u₁) = (prodMap z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩).base (U₁.ι.base u₁) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hl₁]
      exact hv.trans h'.symm
    exact this ▸ hvV
  have hr₂ : Set.range (l₁ ≫ τ.1).base ⊆ Set.range X'.ι.base := by
    rintro _ ⟨u₁, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hl₁V u₁
  let τv : (↑U₁ : Scheme.{u}) ⟶ ↑X' := IsOpenImmersion.lift X'.ι (l₁ ≫ τ.1) hr₂
  have hτv : τv ≫ X'.ι = l₁ ≫ τ.1 := IsOpenImmersion.lift_fac _ _ _
  let lam : SchemeHomOver (U₁.ι ≫ pullback.fst z (X'.ι ≫ f) ≫ z) (U.ι ≫ pullback.fst z f ≫ z) :=
    ⟨l₁, by rw [reassoc_of% hl₁, prodMap_fst_assoc]⟩
  let τ₁ : SchemeHomOver (U₁.ι ≫ pullback.fst z (X'.ι ≫ f) ≫ z) (X'.ι ≫ f) :=
    ⟨τv, by rw [reassoc_of% hτv, τ.2, reassoc_of% hl₁, prodMap_fst_assoc]⟩
  have hτ₁ : NeronModelInfra.schemeHomOverComp τ₁ (⟨X'.ι, rfl⟩ : SchemeHomOver (X'.ι ≫ f) f) =
      NeronModelInfra.schemeHomOverComp lam τ :=
    Subtype.ext hτv
  refine ⟨U₁, hη₁U₁, τ₁, ?_⟩

  have htr := congrArg Subtype.val (transport_mulK K LXK z f e X' uK)
  simp only [NeronModelInfra.schemeHomOverComp_coe] at htr
  rw [← schemeHomOverComp_assoc, ← genericFibreRestrict_schemeHomOverComp, hτ₁,
    genericFibreRestrict_schemeHomOverComp, schemeHomOverComp_assoc, NeronModelInfra.schemeHomOverComp_coe, hτK,
    reassoc_of% (genericFibre_comp_restrict K (pullback.fst z f ≫ z) (pullback.fst z (X'.ι ≫ f) ≫ z)
      (prodMapOver z (X'.ι ≫ f) f ⟨X'.ι, rfl⟩) U U₁ lam hl₁), htr]

theorem main [HenselianLocalRing R]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK) (hcomm : LXK.IsCommutative)
    (M : ModelFamily R K gK) (hfin : Finite M.ι)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i))
    (hpts : M.CatchesIndexOnePoints) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (e : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧
      IsIso e.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e =
          LXK.mul t (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y e)) ∧
      (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K))
          (pullback.snd g (specGenericFibreInclusion R K)))
        (η : ↑(pullback z g)), (pullback.fst z g ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z g), y ⤳ η → (pullback.fst z g ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
        ∃ (U : (pullback z g).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z g ≫ z) g),
          (genericFibreRestrict R K g (U.ι ≫ pullback.fst z g ≫ z) τ).1 =
            pullback.map (U.ι ≫ pullback.fst z g ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z g ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              ((LB.genericFibre K).mul (pullback.snd (pullback.fst z g ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z g ≫ z) ⟨pullback.fst z g, rfl⟩) uK)
                (genericFibreRestrict R K g (pullback.fst z g ≫ z)
                  ⟨pullback.snd z g, pullback.condition.symm⟩)).1) := by

  obtain ⟨X, f, e, hsm, hsep, hloft, hqc, hXk, he, hL, hR⟩ :=
    NeronModelInfra.exists_model_forall_nhds_translation_extension_isOpenImmersion_of_catchesIndexOnePoints_of_isCommutative
      K LXK hcomm M hfin hM hpts
  haveI := hsm; haveI := hsep; haveI := hloft; haveI := hqc; haveI := he

  obtain ⟨W, m, hW₁, hW₂, hmK, hΦ, hΦ₂, hΨ, hΨ₂⟩ :=
    NeronModelInfra.exists_opens_mul_extension_isOpenImmersion_lift_of_forall_nhds_translation_extension
      K LXK f e (hL X f e) (hR X f e)

  obtain ⟨X', B, g, LB, jY, e', -, hX'₂, hg₁, hg₂, hg₃, hg₄, hjY, -, hjY₂, he', hhom, hcompat⟩ :=
    NeronModelInfra.exists_opens_relativeGroupLaw_isOpenImmersion_genericFibre_iso_of_isOpenImmersion_lift_mul_of_henselianLocalRing
      K LXK f hXk e W m hW₁ hW₂ hmK hΦ hΦ₂ hΨ hΨ₂
  haveI := hjY; haveI := he'
  refine ⟨B, g, LB, e', hg₁, hg₂, hg₃, hg₄, he', hhom, ?_⟩

  intro Z z _ _ uK' η' hη' hmax'
  exact twist K LXK z (X'.ι ≫ f) g
    (NeronModelInfra.schemeHomOverComp (genericFibreRestrict R K f (X'.ι ≫ f) ⟨X'.ι, rfl⟩) e) LB jY hjY₂ e'
    hhom hcompat (restrict_translation K LXK z f e X' hX'₂ (fun uK η hηs hηmax => hL Z z uK η hηs hηmax))
    uK' η' hη' hmax'

end P2mNeronN34H
p2m_reactivate "P2MW.S_NeronModelInfra_exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative.P2mNeronN34H"

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    [Smooth gK] [IsSeparated gK] [LocallyOfFiniteType gK] [QuasiCompact gK]
    (LXK : RelativeGroupLaw K gK) (hcomm : LXK.IsCommutative)
    (M : ModelFamily R K gK) (hfin : Finite M.ι)
    (hM : ∀ i, Smooth (M.str i) ∧ IsSeparated (M.str i) ∧ LocallyOfFiniteType (M.str i) ∧
      QuasiCompact (M.str i))
    (hpts : M.CatchesIndexOnePoints) :
    ∃ (B : Scheme.{u}) (g : B ⟶ Spec (CommRingCat.of R)) (LB : RelativeGroupLaw R g)
      (e : SchemeHomOver (pullback.snd g (specGenericFibreInclusion R K)) gK),
      Smooth g ∧ IsSeparated g ∧ LocallyOfFiniteType g ∧ QuasiCompact g ∧
      IsIso e.1 ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
          (x y : SchemeHomOver t (pullback.snd g (specGenericFibreInclusion R K))),
        NeronModelInfra.schemeHomOverComp ((LB.genericFibre K).mul t x y) e =
          LXK.mul t (NeronModelInfra.schemeHomOverComp x e) (NeronModelInfra.schemeHomOverComp y e)) ∧
      (∀ (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R)) [Smooth z] [QuasiCompact z]
        (uK : SchemeHomOver (pullback.snd z (specGenericFibreInclusion R K))
          (pullback.snd g (specGenericFibreInclusion R K)))
        (η : ↑(pullback z g)), (pullback.fst z g ≫ z).base η = IsLocalRing.closedPoint R →
        (∀ y : ↑(pullback z g), y ⤳ η → (pullback.fst z g ≫ z).base y = IsLocalRing.closedPoint R → y = η) →
        ∃ (U : (pullback z g).Opens) (_ : η ∈ U) (τ : SchemeHomOver (U.ι ≫ pullback.fst z g ≫ z) g),
          (genericFibreRestrict R K g (U.ι ≫ pullback.fst z g ≫ z) τ).1 =
            pullback.map (U.ι ≫ pullback.fst z g ≫ z) (specGenericFibreInclusion R K)
                (pullback.fst z g ≫ z) (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
                (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              ((LB.genericFibre K).mul (pullback.snd (pullback.fst z g ≫ z) (specGenericFibreInclusion R K))
                (NeronModelInfra.schemeHomOverComp
                  (genericFibreRestrict R K z (pullback.fst z g ≫ z) ⟨pullback.fst z g, rfl⟩) uK)
                (genericFibreRestrict R K g (pullback.fst z g ≫ z)
                  ⟨pullback.snd z g, pullback.condition.symm⟩)).1) :=
  P2mNeronN34H.main K LXK hcomm M hfin hM hpts

end S_NeronModelInfra_exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative
end P2MW
export P2MW.S_NeronModelInfra_exists_relativeGroupLaw_genericFibre_iso_nhds_twist_extension_of_catchesIndexOnePoints_of_henselianLocalRing_of_isCommutative (solution)
