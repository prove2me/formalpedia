-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_not_mem_kernelTrivial_away_of_kernelTrivial_atPrime_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/91636527-28c2-5090-8f44-6cbecb58f88e

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isClosedImmersion_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_exists_not_mem_forall_factorsThrough_iff_of_forall_atPrime_of_isProper
import Theorems.Thm_AlgebraicGeometry_Polarisation_nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Polarisation_isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit_of_commRing
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_kernelTrivial_away_of_kernelTrivial_atPrime_of_isNoetherianRing
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans"
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

namespace L4KT

variable {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S))

noncomputable abbrev bc : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S) := Spec.map (CommRingCat.ofHom φ)

noncomputable def down {R : Type} [CommRing R] {t' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S')}
    (x' : SchemeHomOver t' (pullback.snd f (bc φ))) : SchemeHomOver (t' ≫ bc φ) f :=
  ⟨x'.1 ≫ pullback.fst f (bc φ), by rw [Category.assoc, pullback.condition, ← Category.assoc, x'.2]⟩

theorem down_coe {R : Type} [CommRing R] {t' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S')}
    (x' : SchemeHomOver t' (pullback.snd f (bc φ))) : (down φ f x').1 = x'.1 ≫ pullback.fst f (bc φ) := rfl

noncomputable def H {R : Type} [CommRing R] (t' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S')) :
    pullback (pullback.snd f (bc φ)) t' ⟶ pullback f (t' ≫ bc φ) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f (bc φ)) (pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc])

noncomputable def H' {R : Type} [CommRing R] (t' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S')) :
    pullback f (t' ≫ bc φ) ⟶ pullback (pullback.snd f (bc φ)) t' :=
  pullback.lift (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ t') (by rw [pullback.condition, Category.assoc]))
    (pullback.snd _ _) (by rw [pullback.lift_snd])

theorem H'_H {R : Type} [CommRing R] (t' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S')) :
    H' φ f t' ≫ H φ f t' = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [Category.id_comp, Category.assoc, H, H', pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.id_comp, Category.assoc, H, H', pullback.lift_snd]

theorem H_snd {R : Type} [CommRing R] (t' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S')) :
    H φ f t' ≫ pullback.snd f (t' ≫ bc φ) = pullback.snd _ t' ≫ 𝟙 _ := by
  rw [H, pullback.lift_snd, Category.comp_id]

theorem H'_snd {R : Type} [CommRing R] (t' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S')) :
    H' φ f t' ≫ pullback.snd (pullback.snd f (bc φ)) t' = pullback.snd f (t' ≫ bc φ) ≫ 𝟙 _ := by
  rw [H', pullback.lift_snd, Category.comp_id]

noncomputable def G : pullback (pullback.snd f (bc φ)) (pullback.snd f (bc φ)) ⟶ pullback f f :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f (bc φ)) (pullback.snd _ _ ≫ pullback.fst f (bc φ))
    (by rw [Category.assoc, Category.assoc, (IsPullback.of_hasPullback f (bc φ)).w, ← Category.assoc, pullback.condition,
      Category.assoc])

theorem sliceAt_G {R : Type} [CommRing R] {t' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S')}
    (x' : SchemeHomOver t' (pullback.snd f (bc φ))) :
    sliceAt (pullback.snd f (bc φ)) x' ≫ G φ f = H φ f t' ≫ sliceAt f (down φ f x') := by
  apply pullback.hom_ext
  · simp only [Category.assoc, G, H, sliceAt, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, G, H, sliceAt, pullback.lift_snd, pullback.lift_snd_assoc, down_coe]

def Compat (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' (pullback.snd f (bc φ))) : Prop :=
  ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f (bc φ))),
    (L'.mul t' P Q).1 ≫ pullback.fst f (bc φ) =
      (L.mul (t' ≫ bc φ) ⟨P.1 ≫ pullback.fst f (bc φ), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ pullback.fst f (bc φ), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1

variable {f} (L : RelativeGroupLaw S f) (τ : A.Modules) (L' : RelativeGroupLaw S' (pullback.snd f (bc φ))) (hL' : Compat φ f L L')
include hL'

omit τ in

theorem one_down {R : Type} [CommRing R] (t' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S')) :
    down φ f (L'.one t') = L.one (t' ≫ bc φ) := by
  have h := hL' _ t' (L'.one t') (L'.one t')
  rw [L'.one_mul] at h
  have h2 : down φ f (L'.one t') = L.mul (t' ≫ bc φ) (down φ f (L'.one t')) (down φ f (L'.one t')) := Subtype.ext h
  letI := L.pointGroup (t' ≫ bc φ)
  have h3 : down φ f (L'.one t') * down φ f (L'.one t') = down φ f (L'.one t') * 1 := by rw [mul_one]; exact h2.symm
  exact mul_left_cancel h3

theorem nonempty_slice_iso (hτ : Scheme.Modules.IsInvertible τ) {R : Type} [CommRing R]
    {t' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S')} (x' : SchemeHomOver t' (pullback.snd f (bc φ))) :
    Nonempty ((Scheme.Modules.pullback (sliceAt (pullback.snd f (bc φ)) x')).obj
        (mumfordBundle (pullback.snd f (bc φ)) L' ((Scheme.Modules.pullback (pullback.fst f (bc φ))).obj τ)) ≅
      (Scheme.Modules.pullback (H φ f t')).obj ((Scheme.Modules.pullback (sliceAt f (down φ f x'))).obj (mumfordBundle f L τ))) := by
  obtain ⟨eΛ⟩ := nonempty_mumfordBundle_pullback_iso_pullback_mumfordBundle_of_isPullback S S' φ f L
    (pullback.snd f (bc φ)) L' (pullback.fst f (bc φ)) (IsPullback.of_hasPullback f (bc φ)) (fun t' P Q => hL' _ t' P Q) τ hτ
  refine ⟨(Scheme.Modules.pullback _).mapIso eΛ ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    eqToIso (by rw [show (pullback.lift (pullback.fst (pullback.snd f (bc φ)) (pullback.snd f (bc φ)) ≫ pullback.fst f (bc φ))
      (pullback.snd (pullback.snd f (bc φ)) (pullback.snd f (bc φ)) ≫ pullback.fst f (bc φ)) _) = G φ f from rfl, sliceAt_G]) ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm⟩

theorem locIso_iff (hτ : Scheme.Modules.IsInvertible τ) {R : Type} [CommRing R]
    {t' : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S')} (x' : SchemeHomOver t' (pullback.snd f (bc φ))) :
    LocIsoOnBase (pullback.snd (pullback.snd f (bc φ)) t')
        ((Scheme.Modules.pullback (sliceAt (pullback.snd f (bc φ)) x')).obj
          (mumfordBundle (pullback.snd f (bc φ)) L' ((Scheme.Modules.pullback (pullback.fst f (bc φ))).obj τ)))
        (𝟙_ _) ↔
      LocIsoOnBase (pullback.snd f (t' ≫ bc φ))
        ((Scheme.Modules.pullback (sliceAt f (down φ f x'))).obj (mumfordBundle f L τ)) (𝟙_ _) := by
  obtain ⟨eS⟩ := nonempty_slice_iso φ L τ L' hL' hτ x'
  have equivU := LocIsoOnBase.equivalence (pullback.snd (pullback.snd f (bc φ)) t')
  have equivD := LocIsoOnBase.equivalence (pullback.snd f (t' ≫ bc φ))
  constructor
  · intro h

    have h1 := LocIsoOnBase.pullback_of_comp_eq (pullback.snd f (t' ≫ bc φ)) (H' φ f t') (𝟙 _) (H'_snd φ f t') h

    have e1 : (Scheme.Modules.pullback (H' φ f t')).obj ((Scheme.Modules.pullback (sliceAt (pullback.snd f (bc φ)) x')).obj
          (mumfordBundle (pullback.snd f (bc φ)) L' ((Scheme.Modules.pullback (pullback.fst f (bc φ))).obj τ))) ≅
        (Scheme.Modules.pullback (sliceAt f (down φ f x'))).obj (mumfordBundle f L τ) :=
      (Scheme.Modules.pullback _).mapIso eS ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
        eqToIso (by rw [H'_H]) ≪≫ (Scheme.Modules.pullbackId _).app _
    have e2 : (Scheme.Modules.pullback (H' φ f t')).obj (𝟙_ _) ≅ 𝟙_ (pullback f (t' ≫ bc φ)).Modules :=
      Scheme.Modules.pullbackTensorUnitObjIso _
    exact equivD.trans (equivD.trans (equivD.symm (fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e1⟩⟩)) h1)
      (fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e2⟩⟩)
  · intro h
    have h1 := LocIsoOnBase.pullback_of_comp_eq (pullback.snd (pullback.snd f (bc φ)) t') (H φ f t') (𝟙 _) (H_snd φ f t') h
    have e2 : (Scheme.Modules.pullback (H φ f t')).obj (𝟙_ _) ≅ 𝟙_ (pullback (pullback.snd f (bc φ)) t').Modules :=
      Scheme.Modules.pullbackTensorUnitObjIso _
    exact equivU.trans (equivU.trans (fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso eS⟩⟩) h1)
      (fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback _).mapIso e2⟩⟩)

end L4KT

open L4KT in
theorem solution
    {S : Type} [CommRing S] [IsNoetherianRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hA : AbelianSchemePropertyBundle S f)
    (τ : A.Modules) (hτ : Scheme.Modules.IsInvertible τ) (𝔭 : PrimeSpectrum S)
    (L𝔭 : RelativeGroupLaw (Localization.AtPrime 𝔭.asIdeal) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))))
    (hL𝔭 : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)))
          (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))),
          (L𝔭.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) =
            (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))
              ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1))
    (hK : KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))) L𝔭
      ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))))).obj τ)) :
    ∃ g : S, g ∉ 𝔭.asIdeal ∧
      ∀ (Lg : RelativeGroupLaw (Localization.Away g) (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))))
        (_ : (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of (Localization.Away g)))
          (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))),
          (Lg.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))) =
            (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))
              ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
              ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))),
                by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)),
        KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))))) Lg
          ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))))).obj τ) := by
  obtain ⟨K, ιK, hKcl, hKpts⟩ :=
    AbelianSchemePropertyBundle.exists_isClosedImmersion_forall_iff_locIsoOnBase_sliceAt_mumfordBundle_of_isNoetherianRing hA L τ hτ
  haveI := hKcl
  haveI : IsProper f := hA.proper

  have he : (L.one (𝟙 _)).1 ≫ f = 𝟙 _ := (L.one (𝟙 _)).2
  haveI : IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
    have : IsClosedImmersion ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f) := by rw [he]; infer_instance
    exact IsClosedImmersion.of_comp _ f
  have hone : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)), (L.one t).1 = t ≫ (L.one (𝟙 _)).1 := fun t => by
    rw [← L.one_natural (𝟙 _) t t (Category.comp_id t)]
    rfl

  have h𝔭 : ∀ (R : Type) [CommRing R] (ψ : Spec (CommRingCat.of R) ⟶ A),
      (∃ t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal)),
          t ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭.asIdeal))) = ψ ≫ f) →
      ((∃ ψ₁ : Spec (CommRingCat.of R) ⟶ K, ψ₁ ≫ ιK = ψ) ↔
        (∃ ψ₂ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S), ψ₂ ≫ (L.one (𝟙 _)).1 = ψ)) := by
    intro R _ ψ ht
    obtain ⟨t', ht'⟩ := ht
    let x' : SchemeHomOver t' (pullback.snd f (bc (algebraMap S (Localization.AtPrime 𝔭.asIdeal)))) :=
      ⟨pullback.lift ψ t' ht'.symm, pullback.lift_snd _ _ _⟩
    have hx : (down (algebraMap S (Localization.AtPrime 𝔭.asIdeal)) f x').1 = ψ := pullback.lift_fst _ _ _
    constructor
    · rintro ⟨k, hk⟩
      have h1 := (hKpts R _ (down _ f x')).mp ⟨k, by rw [hk, hx]⟩
      have h2 := (locIso_iff (algebraMap S (Localization.AtPrime 𝔭.asIdeal)) L τ L𝔭 hL𝔭 hτ x').mpr h1
      have h3 : x' = L𝔭.one t' := hK R t' x' h2
      refine ⟨t' ≫ bc (algebraMap S (Localization.AtPrime 𝔭.asIdeal)), ?_⟩
      rw [← hx, h3, one_down _ L L𝔭 hL𝔭 t']
      exact (hone _).symm
    · rintro ⟨s, hs⟩
      have hs' : s = ψ ≫ f := by rw [← hs, Category.assoc, he, Category.comp_id]
      have hd : down (algebraMap S (Localization.AtPrime 𝔭.asIdeal)) f x' =
          L.one (t' ≫ bc (algebraMap S (Localization.AtPrime 𝔭.asIdeal))) :=
        Subtype.ext (by rw [hx, hone, ht', ← hs', hs])
      have h1 : LocIsoOnBase (pullback.snd f (t' ≫ bc (algebraMap S (Localization.AtPrime 𝔭.asIdeal))))
          ((Scheme.Modules.pullback (sliceAt f (down (algebraMap S (Localization.AtPrime 𝔭.asIdeal)) f x'))).obj
            (mumfordBundle f L τ)) (𝟙_ _) := by
        rw [hd]
        exact (isInStabilizer_iff_locIsoOnBase_pullback_sliceAt_mumfordBundle_unit_of_commRing S f L τ hτ R _ _).mp
          (L.isInStabilizer_one τ _)
      obtain ⟨k, hk⟩ := (hKpts R _ (down _ f x')).mpr h1
      exact ⟨k, by rw [hk, hx]⟩
  obtain ⟨g, hg, hspread⟩ :=
    AlgebraicGeometry.exists_not_mem_forall_factorsThrough_iff_of_forall_atPrime_of_isProper f ιK (L.one (𝟙 _)).1 𝔭 h𝔭
  refine ⟨g, hg, fun Lg hLg => ?_⟩
  intro R _ t' x' hloc'
  have h1 := (locIso_iff (algebraMap S (Localization.Away g)) L τ Lg hLg hτ x').mp hloc'
  obtain ⟨k, hk⟩ := (hKpts R _ (down _ f x')).mpr h1
  obtain ⟨s, hs⟩ := (hspread R (down (algebraMap S (Localization.Away g)) f x').1
    ⟨t', (down (algebraMap S (Localization.Away g)) f x').2.symm⟩).mp ⟨k, hk⟩
  have hs' : s = t' ≫ bc (algebraMap S (Localization.Away g)) := by
    rw [← (down (algebraMap S (Localization.Away g)) f x').2, ← hs, Category.assoc, he, Category.comp_id]
  have hψ : (down (algebraMap S (Localization.Away g)) f x').1 =
      (down (algebraMap S (Localization.Away g)) f (Lg.one t')).1 := by
    rw [one_down _ L Lg hLg t', ← hs, hs']
    exact (hone _).symm
  apply Subtype.ext
  apply pullback.hom_ext
  · exact hψ
  · rw [x'.2, (Lg.one t').2]

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_kernelTrivial_away_of_kernelTrivial_atPrime_of_isNoetherianRing
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_not_mem_kernelTrivial_away_of_kernelTrivial_atPrime_of_isNoetherianRing (solution)
