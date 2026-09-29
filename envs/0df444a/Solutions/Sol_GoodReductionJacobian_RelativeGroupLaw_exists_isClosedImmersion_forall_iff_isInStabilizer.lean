-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isClosedImmersion_forall_iff_isInStabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4a091d76-0934-5f45-9bf2-b6dfa9fde659

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_forall_iff_isInStabilizer
p2m_attr_erase "instance" "PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing"
p2m_attr_erase "instance" "TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mKSpread

p2m_open "AlgebraicGeometry.Scheme.Modules"

variable {X X' T : Scheme.{u}}

theorem locallyIsoOver_congr (q : X ⟶ T) {M M₁ M' M₁' : X.Modules} (e : M ≅ M₁) (e' : M' ≅ M₁') :
    LocallyIsoOver q M M' ↔ LocallyIsoOver q M₁ M₁' :=
  ⟨fun h => ((LocallyIsoOver.of_iso q e).symm.trans h).trans (LocallyIsoOver.of_iso q e'),
    fun h => ((LocallyIsoOver.of_iso q e).trans h).trans (LocallyIsoOver.of_iso q e').symm⟩

theorem locallyIsoOver_pullback_iso (q : X ⟶ T) (e : X' ≅ X) (M M' : X.Modules)
    (h : LocallyIsoOver q M M') :
    LocallyIsoOver (e.hom ≫ q) ((Scheme.Modules.pullback e.hom).obj M) ((Scheme.Modules.pullback e.hom).obj M') := by
  intro τ
  obtain ⟨U, hτ, ⟨φ⟩⟩ := h τ
  refine ⟨U, hτ, ⟨?_⟩⟩

  have hle : (e.hom ≫ q) ⁻¹ᵁ U = e.hom ⁻¹ᵁ (q ⁻¹ᵁ U) := rfl
  let r : ((e.hom ≫ q) ⁻¹ᵁ U).toScheme ⟶ (q ⁻¹ᵁ U).toScheme := e.hom ∣_ (q ⁻¹ᵁ U)
  have hr : r ≫ (q ⁻¹ᵁ U).ι = ((e.hom ≫ q) ⁻¹ᵁ U).ι ≫ e.hom := morphismRestrict_ι _ _

  let c1 : (Scheme.Modules.pullback ((e.hom ≫ q) ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback e.hom).obj M) ≅
      (Scheme.Modules.pullback r).obj ((Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M) :=
    (Scheme.Modules.pullbackComp ((e.hom ≫ q) ⁻¹ᵁ U).ι e.hom).app M ≪≫
      (Scheme.Modules.pullbackCongr hr.symm).app M ≪≫
      ((Scheme.Modules.pullbackComp r (q ⁻¹ᵁ U).ι).app M).symm
  let c2 : (Scheme.Modules.pullback ((e.hom ≫ q) ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback e.hom).obj M') ≅
      (Scheme.Modules.pullback r).obj ((Scheme.Modules.pullback (q ⁻¹ᵁ U).ι).obj M') :=
    (Scheme.Modules.pullbackComp ((e.hom ≫ q) ⁻¹ᵁ U).ι e.hom).app M' ≪≫
      (Scheme.Modules.pullbackCongr hr.symm).app M' ≪≫
      ((Scheme.Modules.pullbackComp r (q ⁻¹ᵁ U).ι).app M').symm
  exact c1 ≪≫ (Scheme.Modules.pullback r).mapIso φ ≪≫ c2.symm

noncomputable def pullbackInvHomIso (e : X' ≅ X) (N : X.Modules) :
    (Scheme.Modules.pullback e.inv).obj ((Scheme.Modules.pullback e.hom).obj N) ≅ N :=
  (Scheme.Modules.pullbackComp e.inv e.hom).app N ≪≫
    (Scheme.Modules.pullbackCongr e.inv_hom_id).app N ≪≫ (Scheme.Modules.pullbackId X).app N

theorem locallyIsoOver_iff_of_iso (q : X ⟶ T) (e : X' ≅ X) (M M' : X.Modules) :
    LocallyIsoOver (e.hom ≫ q) ((Scheme.Modules.pullback e.hom).obj M) ((Scheme.Modules.pullback e.hom).obj M') ↔
      LocallyIsoOver q M M' := by
  refine ⟨fun h => ?_, locallyIsoOver_pullback_iso q e M M'⟩
  have h' := locallyIsoOver_pullback_iso (e.hom ≫ q) e.symm _ _ h
  simp only [Iso.symm_hom, Iso.inv_hom_id_assoc] at h'
  exact (locallyIsoOver_congr q (pullbackInvHomIso e M) (pullbackInvHomIso e M')).mp h'

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

def idPoint (f : A ⟶ Spec (CommRingCat.of R)) : SchemeHomOver f f := ⟨𝟙 A, Category.id_comp f⟩

theorem isPullback_slice {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    IsPullback (pullback.fst (pullback.snd f f) x.1 ≫ pullback.fst f f) (pullback.snd (pullback.snd f f) x.1) f t := by
  have sq := (IsPullback.of_hasPullback (pullback.snd f f) x.1).paste_horiz (IsPullback.of_hasPullback f f)
  rwa [x.2] at sq

noncomputable def sliceIso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    Limits.pullback (pullback.snd f f) x.1 ≅ Limits.pullback f t :=
  (isPullback_slice t x).isoPullback

@[reassoc (attr := simp)]
theorem sliceIso_hom_fst {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (sliceIso t x).hom ≫ pullback.fst f t = pullback.fst (pullback.snd f f) x.1 ≫ pullback.fst f f :=
  (isPullback_slice t x).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem sliceIso_hom_snd {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (sliceIso t x).hom ≫ pullback.snd f t = pullback.snd (pullback.snd f f) x.1 :=
  (isPullback_slice t x).isoPullback_hom_snd

theorem mul_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f) (hx : x₁.1 = x₂.1)
    (hy : y₁.1 = y₂.1) : (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst h
  obtain rfl : x₁ = x₂ := Subtype.ext hx
  obtain rfl : y₁ = y₂ := Subtype.ext hy
  rfl

theorem sliceIso_hom_mulRight (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) :
    (sliceIso t x).hom ≫ L.mulRight t x = pullback.fst (pullback.snd f f) x.1 ≫ L.mulRight f (idPoint f) := by

  have hbase : (sliceIso t x).hom ≫ pullback.snd f t ≫ t =
      pullback.fst (pullback.snd f f) x.1 ≫ pullback.snd f f ≫ f := by
    rw [sliceIso_hom_snd_assoc, pullback.condition_assoc, x.2]
  have h1 := L.mul_natural (pullback.snd f t ≫ t) ((sliceIso t x).hom ≫ pullback.snd f t ≫ t) (sliceIso t x).hom rfl
    (L.fstPoint t) (L.sndPoint t x)
  have h2 := L.mul_natural (pullback.snd f f ≫ f) (pullback.fst (pullback.snd f f) x.1 ≫ pullback.snd f f ≫ f)
    (pullback.fst (pullback.snd f f) x.1) rfl (L.fstPoint f) (L.sndPoint f (idPoint f))
  have e1 : (sliceIso t x).hom ≫ L.mulRight t x =
      (L.mul ((sliceIso t x).hom ≫ pullback.snd f t ≫ t)
        (schemeHomOverComp (sliceIso t x).hom rfl (L.fstPoint t))
        (schemeHomOverComp (sliceIso t x).hom rfl (L.sndPoint t x))).1 := by
    rw [← h1]; rfl
  have e2 : pullback.fst (pullback.snd f f) x.1 ≫ L.mulRight f (idPoint f) =
      (L.mul (pullback.fst (pullback.snd f f) x.1 ≫ pullback.snd f f ≫ f)
        (schemeHomOverComp (pullback.fst (pullback.snd f f) x.1) rfl (L.fstPoint f))
        (schemeHomOverComp (pullback.fst (pullback.snd f f) x.1) rfl (L.sndPoint f (idPoint f)))).1 := by
    rw [← h2]; rfl
  rw [e1, e2]

  refine mul_val_congr L hbase _ _ _ _ ?_ ?_
  · simp only [schemeHomOverComp_coe, RelativeGroupLaw.fstPoint_coe, sliceIso_hom_fst]
  · simp only [schemeHomOverComp_coe, RelativeGroupLaw.sndPoint_coe, sliceIso_hom_snd_assoc, idPoint,
      Category.comp_id]
    exact (pullback.condition (f := pullback.snd f f) (g := x.1)).symm

noncomputable def pullbackCompObjIso {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) (N : Z.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback h).obj N) ≅ (Scheme.Modules.pullback (g ≫ h)).obj N :=
  (Scheme.Modules.pullbackComp g h).app N

theorem main [IsNoetherianRing R] [IsProper f] [Flat f] [GeometricallyIntegral f] (L : RelativeGroupLaw R f)
    (hH0 : ∀ (B : Type u) [CommRing B] [Algebra R B],
      Function.Bijective (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    ∃ (KL : Scheme.{u}) (ι : KL ⟶ A), IsClosedImmersion ι ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        (∃ k : T ⟶ KL, k ≫ ι = x.1) ↔ L.IsInStabilizer 𝓛 t x := by
  haveI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨Z, ι, hι, hZ⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isClosedImmersion_forall_iff_locallyIsoOver_of_flat_of_isProper
      f hH0 f ((Scheme.Modules.pullback (L.mulRight f (idPoint f))).obj 𝓛)
      ((Scheme.Modules.pullback (pullback.fst f f)).obj 𝓛) (h𝓛.pullback _) (h𝓛.pullback _)
  refine ⟨Z, ι, hι, fun t x => ?_⟩
  rw [hZ x.1]

  have e1 : (Scheme.Modules.pullback (pullback.fst (pullback.snd f f) x.1)).obj
        ((Scheme.Modules.pullback (L.mulRight f (idPoint f))).obj 𝓛) ≅
      (Scheme.Modules.pullback (sliceIso t x).hom).obj ((Scheme.Modules.pullback (L.mulRight t x)).obj 𝓛) :=
    pullbackCompObjIso _ _ 𝓛 ≪≫ (Scheme.Modules.pullbackCongr (sliceIso_hom_mulRight L t x).symm).app 𝓛 ≪≫
      (pullbackCompObjIso _ _ 𝓛).symm
  have e2 : (Scheme.Modules.pullback (pullback.fst (pullback.snd f f) x.1)).obj
        ((Scheme.Modules.pullback (pullback.fst f f)).obj 𝓛) ≅
      (Scheme.Modules.pullback (sliceIso t x).hom).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) :=
    pullbackCompObjIso _ _ 𝓛 ≪≫ (Scheme.Modules.pullbackCongr (sliceIso_hom_fst t x).symm).app 𝓛 ≪≫
      (pullbackCompObjIso _ _ 𝓛).symm
  rw [locallyIsoOver_congr _ e1 e2, ← sliceIso_hom_snd t x]
  exact locallyIsoOver_iff_of_iso (pullback.snd f t) (sliceIso t x) _ _

end P2mKSpread

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    [IsProper f] [Flat f] [GeometricallyIntegral f] (L : RelativeGroupLaw R f)
    (hH0 : ∀ (B : Type u) [CommRing B] [Algebra R B],
      Function.Bijective (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R B)))).appTop)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛) :
    ∃ (KL : Scheme.{u}) (ι : KL ⟶ A), IsClosedImmersion ι ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
        (∃ k : T ⟶ KL, k ≫ ι = x.1) ↔ L.IsInStabilizer 𝓛 t x :=
  P2mKSpread.main L hH0 𝓛 h𝓛

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_forall_iff_isInStabilizer
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_forall_iff_isInStabilizer (solution)
