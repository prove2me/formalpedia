-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.isOpen_setOf_not_mem_and_abelian_geometricFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/df39b01e-81a8-5437-9733-73682b32b969

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_smooth_irreducibleSpace_geometricFibre_iff_of_isPullback
import Theorems.Thm_AlgebraicGeometry_isOpen_setOf_smooth_irreducibleSpace_geometricFibre_of_isProper_of_flat
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isOpen_setOf_nonempty_relativeGroupLaw_geometricFibre
import Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_isOpen_setOf_not_mem_and_abelian_geometricFibre
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.isClosedImmersion_adicThickeningι AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AdicCompletion.instIsLocalRingMaximalIdeal AlgebraicGeometry.OModulePresheaf.moduleSectionsHomSub AlgebraicGeometry.OModulePresheaf.smulSections AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup AlgebraicGeometry.OModulePresheaf.familyFramesGradedModule.moduleBase AlgebraicGeometry.OModulePresheaf.FamilyFrames.module AlgebraicGeometry.OModulePresheaf.FamilyFrames.addCommGroup"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.adicThickeningTransition_ι AlgebraicGeometry.SmallExtension.pairFst_apply AlgebraicGeometry.SmallExtension.pairSnd_apply AlgebraicGeometry.SmallExtension.tensorToDualHom_tmul AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.RelTangentPoints.const_coe AlgebraicGeometry.SquareZero.zeroSection_fst AlgebraicGeometry.SquareZero.zeroSection_snd_assoc AlgebraicGeometry.SquareZero.zeroSection_fst_assoc AlgebraicGeometry.TangentPoints.zero_coe AlgebraicGeometry.SquareZero.zeroSection_snd AlgebraicGeometry.RelTangentPoints.translate_coe Algebra.PointDerivations.map_apply_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicGeometry.OModulePresheaf.internalHom.ofAffHom_apply AlgebraicGeometry.OModulePresheaf.internalHom.toAffHom_app AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
attribute [local instance] MvPolynomial.gradedAlgebra

namespace L3Sol

universe u

theorem transport3 {k : Type u} [CommRing k] {F F' : Scheme.{u}}
    (p : F ⟶ Spec (CommRingCat.of k)) (p' : F' ⟶ Spec (CommRingCat.of k)) (e : F' ≅ F) (he : e.hom ≫ p = p') (g : ℕ) :
    (Smooth p' ∧ IrreducibleSpace ↥F' ∧ topologicalKrullDim ↥F' = g) →
    (Smooth p ∧ IrreducibleSpace ↥F ∧ topologicalKrullDim ↥F = g) := by
  rintro ⟨hs, hirr, hdim⟩
  have he' : e.inv ≫ p' = p := by rw [← he, Iso.inv_hom_id_assoc]
  have hhomeo : IsHomeomorph e.hom.base :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isHomeomorph
  refine ⟨?_, ?_, ?_⟩
  · rw [← he']; infer_instance
  · have hsurj : Function.Surjective e.hom.base := hhomeo.surjective
    have hirr' : IsIrreducible (Set.univ : Set ↥F) := by
      have := (IrreducibleSpace.isIrreducible_univ (X := ↥F')).image e.hom.base e.hom.base.hom.continuous.continuousOn
      rwa [Set.image_univ, hsurj.range_eq] at this
    exact (irreducibleSpace_def _).mpr hirr'
  · rw [← hdim]; exact (IsHomeomorph.topologicalKrullDim_eq _ hhomeo).symm

theorem exists_fibreIso {R R' : Type u} [CommRing R] [CommRing R'] (ψ : R →+* R')
    {Z Z' : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of R)) (f' : Z' ⟶ Spec (CommRingCat.of R'))
    (gZ : Z' ⟶ Z) (hpb : IsPullback gZ f' f (Spec.map (CommRingCat.ofHom ψ)))
    (k : Type u) [CommRing k] (x' : R' →+* k) :
    ∃ e : pullback f' (Spec.map (CommRingCat.ofHom x')) ≅ pullback f (Spec.map (CommRingCat.ofHom (x'.comp ψ))),
      e.hom ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (x'.comp ψ))) = pullback.snd f' (Spec.map (CommRingCat.ofHom x')) := by
  have hsq : IsPullback (pullback.fst f' (Spec.map (CommRingCat.ofHom x')) ≫ gZ)
      (pullback.snd f' (Spec.map (CommRingCat.ofHom x'))) f (Spec.map (CommRingCat.ofHom (x'.comp ψ))) := by
    have : Spec.map (CommRingCat.ofHom (x'.comp ψ)) = Spec.map (CommRingCat.ofHom x') ≫ Spec.map (CommRingCat.ofHom ψ) := by
      rw [← Spec.map_comp]; rfl
    rw [this]
    exact (IsPullback.of_hasPullback f' (Spec.map (CommRingCat.ofHom x'))).paste_horiz hpb
  exact ⟨hsq.isoPullback, hsq.isoPullback_hom_snd⟩

end L3Sol

theorem solution
    {R : Type} [CommRing R] {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of R))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hproj : ∃ (N : ℕ) (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π R N = f)
    (g : ℕ) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) (r : R)
    (hr : ∀ s : ↥(Spec (CommRingCat.of R)), r ∉ s.asIdeal → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : R →+* k),
        RingHom.ker x = s.asIdeal →
        Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g) :
    IsOpen {s : ↥(Spec (CommRingCat.of R)) | r ∉ s.asIdeal ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : R →+* k),
        RingHom.ker x = s.asIdeal →
        Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g ∧
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x))))} := by
  classical
  obtain ⟨N, ι, hι, hιf⟩ := hproj

  set Zr := pullback f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) with hZr
  set fr : Zr ⟶ Spec (CommRingCat.of (Localization.Away r)) := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) with hfr
  set gZ : Zr ⟶ Z := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) with hgZ
  have hpb : IsPullback gZ fr f (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) := IsPullback.of_hasPullback _ _
  haveI : IsProper fr := inferInstance
  haveI : Flat fr := inferInstance
  haveI : LocallyOfFinitePresentation fr := inferInstance

  have hcomap : ∀ t : ↥(Spec (CommRingCat.of (Localization.Away r))), r ∉ ((Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).base t).asIdeal := by
    intro t
    have : (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).base t ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := ⟨t, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r] at this
    exact (PrimeSpectrum.mem_basicOpen r _).mp this

  have h3 : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : (Localization.Away r) →+* k),
      Smooth (pullback.snd fr (Spec.map (CommRingCat.ofHom x))) ∧
      IrreducibleSpace ↥(pullback fr (Spec.map (CommRingCat.ofHom x))) ∧
      topologicalKrullDim ↥(pullback fr (Spec.map (CommRingCat.ofHom x))) = g := by
    intro k _ _ x
    obtain ⟨e, he⟩ := L3Sol.exists_fibreIso (algebraMap R (Localization.Away r)) f fr gZ hpb k x
    have hx : RingHom.ker (x.comp (algebraMap R (Localization.Away r))) = ((Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).base ⟨RingHom.ker x, RingHom.ker_isPrime x⟩).asIdeal := by
      rw [← RingHom.comap_ker]; rfl
    exact L3Sol.transport3 _ _ e.symm (by rw [← he, Iso.symm_hom, Iso.inv_hom_id_assoc]) g
      (hr _ (hcomap _) k (x.comp (algebraMap R (Localization.Away r))) hx)

  have hsm : Smooth fr := by
    obtain ⟨-, hV⟩ := AlgebraicGeometry.isOpen_setOf_smooth_irreducibleSpace_geometricFibre_of_isProper_of_flat fr g
    have htop : Smooth (fr ∣_ ⊤) := hV ⊤ (fun t _ k _ _ x _ => h3 k x)
    exact AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Smooth)
      (f := fr) (fun _ : Unit => ⊤) (by simp) (fun _ => htop)

  have hprojr : ∃ (N : ℕ) (ι : Zr ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) (Localization.Away r))),
      IsClosedImmersion ι ∧ ι ≫ ProjSpace.π (Localization.Away r) N = fr := by
    have hP := AlgebraicGeometry.ProjSpace.isPullback_map R (Localization.Away r) N
    haveI := hι
    let ιr := hP.lift (gZ ≫ ι) fr (by rw [Category.assoc, hιf]; exact hpb.w)
    have h1 : ιr ≫ ProjSpace.map R (Localization.Away r) N = gZ ≫ ι := hP.lift_fst _ _ _
    have h2 : ιr ≫ ProjSpace.π (Localization.Away r) N = fr := hP.lift_snd _ _ _
    refine ⟨N, ιr, ?_, h2⟩
    have big : IsPullback gZ (ιr ≫ ProjSpace.π (Localization.Away r) N) (ι ≫ ProjSpace.π R N) (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) := by
      rw [h2, hιf]; exact hpb
    have sq : IsPullback gZ ιr ι (ProjSpace.map R (Localization.Away r) N) := IsPullback.of_bot big h1.symm hP
    exact MorphismProperty.of_isPullback sq hι

  have hconn : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : (Localization.Away r) →+* k),
      ConnectedSpace ↥(pullback fr (Spec.map (CommRingCat.ofHom x))) := by
    intro k _ _ x
    haveI := (h3 k x).2.1
    infer_instance
  let εr : SchemeHomOver (𝟙 (Spec (CommRingCat.of (Localization.Away r)))) fr :=
    ⟨pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫ ε.1) (𝟙 _) (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp]),
      by rw [pullback.lift_snd]⟩

  have hG := GoodReductionJacobian.AbelianSchemePropertyBundle.isOpen_setOf_nonempty_relativeGroupLaw_geometricFibre fr hsm
    inferInstance hprojr hconn εr

  have himage : {s : ↥(Spec (CommRingCat.of R)) | r ∉ s.asIdeal ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : R →+* k),
        RingHom.ker x = s.asIdeal →
        Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom x))) ∧
        IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x))) ∧
        topologicalKrullDim ↥(pullback f (Spec.map (CommRingCat.ofHom x))) = g ∧
        Nonempty (RelativeGroupLaw k (pullback.snd f (Spec.map (CommRingCat.ofHom x))))} =
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).base '' {t : ↥(Spec (CommRingCat.of (Localization.Away r))) | ∀ (k : Type) [Field k] [IsAlgClosed k] (x : (Localization.Away r) →+* k),
        RingHom.ker x = t.asIdeal → Nonempty (RelativeGroupLaw k (pullback.snd fr (Spec.map (CommRingCat.ofHom x))))} := by
    ext s
    constructor
    · rintro ⟨hrs, hPs⟩
      have hs : s ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r))) := by
        rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]; exact (PrimeSpectrum.mem_basicOpen r s).mpr hrs
      obtain ⟨t, ht⟩ := hs
      refine ⟨t, fun k _ _ x hx => ?_, ht⟩
      have hx' : RingHom.ker (x.comp (algebraMap R (Localization.Away r))) = s.asIdeal := by
        rw [← RingHom.comap_ker, hx, ← ht]; rfl
      exact ((GoodReductionJacobian.RelativeGroupLaw.smooth_irreducibleSpace_geometricFibre_iff_of_isPullback
        (algebraMap R (Localization.Away r)) f fr gZ hpb g k x).mpr (hPs k (x.comp (algebraMap R (Localization.Away r))) hx')).2.2.2
    · rintro ⟨t, ht, rfl⟩
      refine ⟨hcomap t, fun k _ _ x hx => ?_⟩
      have hunit : IsUnit (x r) := by
        rw [isUnit_iff_ne_zero, Ne, ← RingHom.mem_ker, hx]
        exact hcomap t
      let xr : (Localization.Away r) →+* k := IsLocalization.Away.lift r hunit
      have hxr : xr.comp (algebraMap R (Localization.Away r)) = x := IsLocalization.Away.lift_comp r hunit
      have hker : RingHom.ker xr = t.asIdeal := by
        have hc : (RingHom.ker xr).under R = t.asIdeal.under R := by
          change (RingHom.ker xr).comap (algebraMap R (Localization.Away r)) = t.asIdeal.comap (algebraMap R (Localization.Away r))
          rw [RingHom.comap_ker, hxr, hx]; rfl
        rw [← IsLocalization.map_under (Submonoid.powers r) (S := (Localization.Away r)) (RingHom.ker xr), hc,
          IsLocalization.map_under (Submonoid.powers r) (S := (Localization.Away r))]
      have h4 : Smooth (pullback.snd fr (Spec.map (CommRingCat.ofHom xr))) ∧
          IrreducibleSpace ↥(pullback fr (Spec.map (CommRingCat.ofHom xr))) ∧
          topologicalKrullDim ↥(pullback fr (Spec.map (CommRingCat.ofHom xr))) = g ∧
          Nonempty (RelativeGroupLaw k (pullback.snd fr (Spec.map (CommRingCat.ofHom xr)))) :=
        ⟨(h3 k xr).1, (h3 k xr).2.1, (h3 k xr).2.2, ht k xr hker⟩
      have := (GoodReductionJacobian.RelativeGroupLaw.smooth_irreducibleSpace_geometricFibre_iff_of_isPullback
        (algebraMap R (Localization.Away r)) f fr gZ hpb g k xr).mp h4
      rwa [hxr] at this
  rw [himage]
  exact (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))).isOpenEmbedding.isOpenMap _ hG

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_isOpen_setOf_not_mem_and_abelian_geometricFibre
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_isOpen_setOf_not_mem_and_abelian_geometricFibre (solution)
