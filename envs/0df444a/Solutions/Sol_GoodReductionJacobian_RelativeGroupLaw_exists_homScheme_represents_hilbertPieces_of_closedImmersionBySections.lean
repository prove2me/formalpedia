-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/daa86f2c-cd75-59a9-bd9e-8ee341a4cd42

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Theorems.Thm_AlgebraicGeometry_exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker
import Theorems.Thm_AlgebraicGeometry_exists_hom_pullback_comp_eq_and_forall_pullbackMap_comp_eq_of_forall_spec_point
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_formallyUnramified_of_forall_specMap_comp_eq_imp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op instTopologicallyFGOfFiniteType AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.HilbertFunctor.Point.mk.injEq AlgebraicGeometry.HilbertFunctor.Point.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"
p2m_open "CategoryTheory.MonoidalCategory"

noncomputable section

namespace HomSchemeAsm

variable {S : Type} [CommRing S] {A B : Scheme.{0}}
  {f : A ⟶ Spec (CommRingCat.of S)} {g : B ⟶ Spec (CommRingCat.of S)}
  (LA : RelativeGroupLaw S f) (LB : RelativeGroupLaw S g)

def IsHom {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) : Prop :=
  ∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
    pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ =
      (LB.mul (t' ≫ s)
        ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
        ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1

def eA {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : T ⟶ pullback f t :=
  pullback.lift (LA.one t).1 (𝟙 _) (by rw [Category.id_comp]; exact (LA.one t).2)

@[scoped simp] theorem eA_fst {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    eA LA t ≫ pullback.fst f t = (LA.one t).1 := pullback.lift_fst _ _ _

@[scoped simp] theorem eA_snd {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    eA LA t ≫ pullback.snd f t = 𝟙 _ := pullback.lift_snd _ _ _

theorem isHom_iff (hAc : LA.IsCommutative) (hBc : LB.IsCommutative)
    (hA : AbelianSchemePropertyBundle S f) (hB : AbelianSchemePropertyBundle S g)
    {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) :
    IsHom LA LB s φ hφ ↔ eA LA s ≫ φ = (LB.one s).1 :=
  GoodReductionJacobian.RelativeGroupLaw.forall_mul_comp_eq_iff_one_comp_eq_of_abelianSchemePropertyBundle
    S f g LA LB hAc hBc hA hB S' s φ hφ

def compHom {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    letI := LB.pointGroup t
    letI := LB.pointGroup t'
    SchemeHomOver t g →* SchemeHomOver t' g :=
  letI := LB.pointGroup t
  letI := LB.pointGroup t'
  { toFun := schemeHomOverComp ψ hψ
    map_one' := LB.one_natural t t' ψ hψ
    map_mul' := LB.mul_natural t t' ψ hψ }

theorem comp_inv {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t g) :
    schemeHomOverComp ψ hψ (LB.inv t x) = LB.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := LB.pointGroup t
  letI := LB.pointGroup t'
  exact map_inv (compHom LB t t' ψ hψ) x

theorem inv_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) : LB.inv t (LB.one t) = LB.one t := by
  letI := LB.pointGroup t
  exact _root_.inv_one

theorem mul_inv_self {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t g) :
    LB.mul t x (LB.inv t x) = LB.one t :=
  LB.mul_inv_cancel t x

section Retr

variable {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
  (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s)

def asPt : SchemeHomOver (pullback.snd f s ≫ s) g := ⟨φ, hφ⟩

def cst : SchemeHomOver (pullback.snd f s ≫ s) g :=
  ⟨pullback.snd f s ≫ eA LA s ≫ φ, by
    rw [Category.assoc, Category.assoc, hφ, ← Category.assoc (eA LA s), eA_snd, Category.id_comp]⟩

def retr : pullback f s ⟶ B :=
  (LB.mul (pullback.snd f s ≫ s) (asPt s φ hφ) (LB.inv _ (cst LA s φ hφ))).1

theorem retr_w : retr LA LB s φ hφ ≫ g = pullback.snd f s ≫ s :=
  (LB.mul (pullback.snd f s ≫ s) (asPt s φ hφ) (LB.inv _ (cst LA s φ hφ))).2

theorem eA_w : eA LA s ≫ (pullback.snd f s ≫ s) = s := by
  rw [← Category.assoc, eA_snd, Category.id_comp]

theorem eA_comp_retr : eA LA s ≫ retr LA LB s φ hφ = (LB.one s).1 := by
  have key : schemeHomOverComp (eA LA s) (eA_w LA s)
      (LB.mul (pullback.snd f s ≫ s) (asPt s φ hφ) (LB.inv _ (cst LA s φ hφ))) = LB.one s := by
    rw [LB.mul_natural, comp_inv]
    have hc : schemeHomOverComp (eA LA s) (eA_w LA s) (cst LA s φ hφ) =
        schemeHomOverComp (eA LA s) (eA_w LA s) (asPt s φ hφ) := by
      apply Subtype.ext
      simp only [schemeHomOverComp_coe, cst, asPt]
      rw [← Category.assoc, ← Category.assoc, eA_snd, Category.id_comp]
    rw [hc, mul_inv_self]
  exact congrArg Subtype.val key

theorem retr_eq_self (h : eA LA s ≫ φ = (LB.one s).1) : retr LA LB s φ hφ = φ := by
  have hc : cst LA s φ hφ = LB.one (pullback.snd f s ≫ s) := by
    rw [← LB.one_natural s (pullback.snd f s ≫ s) (pullback.snd f s) rfl]
    apply Subtype.ext
    simp only [schemeHomOverComp_coe, cst]
    rw [h]
  show (LB.mul (pullback.snd f s ≫ s) (asPt s φ hφ) (LB.inv _ (cst LA s φ hφ))).1 = φ
  rw [hc, inv_one, LB.mul_one]
  rfl

end Retr

section BC

variable {S' S'' : Type} [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
  (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
  (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')

def bc : pullback f s'' ⟶ pullback f s :=
  pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
    (by rw [Category.assoc, hs]; exact pullback.condition)

theorem bc_w : bc ψ s s'' hs ≫ (pullback.snd f s ≫ s) = pullback.snd f s'' ≫ s'' := by
  rw [← Category.assoc, bc, pullback.lift_snd, Category.assoc, hs]

theorem specMap_comp_eA : Spec.map (CommRingCat.ofHom ψ) ≫ eA LA s = eA LA s'' ≫ bc ψ s s'' hs := by
  apply pullback.hom_ext
  · rw [Category.assoc, eA_fst, Category.assoc, bc, pullback.lift_fst, eA_fst]
    exact congrArg Subtype.val (LA.one_natural s s'' (Spec.map (CommRingCat.ofHom ψ)) hs)
  · rw [Category.assoc, eA_snd, Category.comp_id, Category.assoc, bc, pullback.lift_snd, ← Category.assoc, eA_snd,
      Category.id_comp]

variable (φ : pullback f s ⟶ B)

theorem bc_comp_w (hφ : φ ≫ g = pullback.snd f s ≫ s) : (bc ψ s s'' hs ≫ φ) ≫ g = pullback.snd f s'' ≫ s'' := by
  rw [Category.assoc, hφ, bc_w]

theorem bc_comp_retr (hφ : φ ≫ g = pullback.snd f s ≫ s) :
    bc ψ s s'' hs ≫ retr LA LB s φ hφ = retr LA LB s'' (bc ψ s s'' hs ≫ φ) (bc_comp_w ψ s s'' hs φ hφ) := by
  have key : schemeHomOverComp (bc ψ s s'' hs) (bc_w ψ s s'' hs)
      (LB.mul (pullback.snd f s ≫ s) (asPt s φ hφ) (LB.inv _ (cst LA s φ hφ))) =
      LB.mul (pullback.snd f s'' ≫ s'') (asPt s'' (bc ψ s s'' hs ≫ φ) (bc_comp_w ψ s s'' hs φ hφ))
        (LB.inv _ (cst LA s'' (bc ψ s s'' hs ≫ φ) (bc_comp_w ψ s s'' hs φ hφ))) := by
    rw [LB.mul_natural, comp_inv]
    have h1 : schemeHomOverComp (bc ψ s s'' hs) (bc_w ψ s s'' hs) (asPt s φ hφ) =
        asPt s'' (bc ψ s s'' hs ≫ φ) (bc_comp_w ψ s s'' hs φ hφ) := Subtype.ext rfl
    have h2 : schemeHomOverComp (bc ψ s s'' hs) (bc_w ψ s s'' hs) (cst LA s φ hφ) =
        cst LA s'' (bc ψ s s'' hs ≫ φ) (bc_comp_w ψ s s'' hs φ hφ) := by
      apply Subtype.ext
      simp only [schemeHomOverComp_coe, cst]
      rw [← Category.assoc (bc ψ s s'' hs), bc, pullback.lift_snd, Category.assoc,
        ← Category.assoc (Spec.map _), specMap_comp_eA LA ψ s s'' hs]
      simp only [bc, Category.assoc]
    rw [h1, h2]
  exact congrArg Subtype.val key

end BC

end HomSchemeAsm
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm"

namespace HomSchemeAsm

variable {S : Type} [CommRing S] {A B : Scheme.{0}}
  {f : A ⟶ Spec (CommRingCat.of S)} {g : B ⟶ Spec (CommRingCat.of S)}
  (LA : RelativeGroupLaw S f) (LB : RelativeGroupLaw S g)

section Mor

variable {M : Scheme.{0}} (πM : M ⟶ Spec (CommRingCat.of S))
  (ptM : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ : pullback f s ⟶ B), φ ≫ g = pullback.snd f s ≫ s → SchemeHomOver s πM)

def NatC : Prop :=
  ∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s),
    (ptM S'' s''
        (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
            (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ)
        (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs])).1 =
      Spec.map (CommRingCat.ofHom ψ) ≫ (ptM S' s φ hφ).1

def SurjC : Prop :=
  ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πM),
    ∃ (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s), ptM S' s φ hφ = x

def InjC : Prop :=
  ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ φ' : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) (hφ' : φ' ≫ g = pullback.snd f s ≫ s),
    ptM S' s φ hφ = ptM S' s φ' hφ' → φ = φ'

def UnivC (Φ : pullback f πM ⟶ B) : Prop :=
  ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s),
    pullback.map f s f πM (𝟙 A) (ptM S' s φ hφ).1 (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (ptM S' s φ hφ).2]) ≫ Φ = φ

theorem ptM_congr {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    {φ φ' : pullback f s ⟶ B} (hφ : φ ≫ g = pullback.snd f s ≫ s) (hφ' : φ' ≫ g = pullback.snd f s ≫ s)
    (h : φ = φ') : ptM S' s φ hφ = ptM S' s φ' hφ' := by
  subst h; rfl

variable (Φ : pullback f πM ⟶ B)

def uM : M ⟶ B := eA LA πM ≫ Φ

def vM : M ⟶ B := (LB.one πM).1

theorem uM_w (hΦ : Φ ≫ g = pullback.snd f πM ≫ πM) : uM LA πM Φ ≫ g = πM := by
  rw [uM, Category.assoc, hΦ, ← Category.assoc, eA_snd, Category.id_comp]

theorem vM_w : vM LB πM ≫ g = πM := (LB.one πM).2

theorem comp_vM {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver s πM) : x.1 ≫ vM LB πM = (LB.one s).1 :=
  congrArg Subtype.val (LB.one_natural πM s x.1 x.2)

theorem comp_eA {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver s πM) :
    x.1 ≫ eA LA πM = eA LA s ≫ pullback.map f s f πM (𝟙 A) x.1 (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, x.2]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, eA_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, eA_fst, Category.comp_id]
    exact congrArg Subtype.val (LA.one_natural πM s x.1 x.2)
  · rw [Category.assoc, eA_snd, Category.comp_id, Category.assoc, pullback.lift_snd, ← Category.assoc, eA_snd,
      Category.id_comp]

theorem comp_uM (hU : UnivC πM ptM Φ) {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) :
    (ptM S' s φ hφ).1 ≫ uM LA πM Φ = eA LA s ≫ φ := by
  rw [uM, ← Category.assoc, comp_eA LA πM s (ptM S' s φ hφ), Category.assoc, hU S' s φ hφ]

variable {Z : Scheme.{0}} (j : Z ⟶ M)
  (hZ : ∀ {T' : Scheme.{0}} (ψ : T' ⟶ M), ψ ≫ uM LA πM Φ = ψ ≫ vM LB πM ↔ ∃ ψ' : T' ⟶ Z, ψ' ≫ j = ψ)

include hZ

theorem exists_lift (hU : UnivC πM ptM Φ) {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) :
    ∃ w : Spec (CommRingCat.of S') ⟶ Z, w ≫ j = (ptM S' s (retr LA LB s φ hφ) (retr_w LA LB s φ hφ)).1 :=
  (hZ _).mp (by rw [comp_uM LA πM ptM Φ hU, comp_vM, eA_comp_retr])

def ptH (hU : UnivC πM ptM Φ) (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) : SchemeHomOver s (j ≫ πM) :=
  ⟨(exists_lift LA LB πM ptM Φ j hZ hU s φ hφ).choose, by
    rw [← Category.assoc, (exists_lift LA LB πM ptM Φ j hZ hU s φ hφ).choose_spec]
    exact (ptM S' s _ _).2⟩

theorem ptH_comp_j (hU : UnivC πM ptM Φ) {S' : Type} [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) :
    (ptH LA LB πM ptM Φ j hZ hU S' s φ hφ).1 ≫ j = (ptM S' s (retr LA LB s φ hφ) (retr_w LA LB s φ hφ)).1 :=
  (exists_lift LA LB πM ptM Φ j hZ hU s φ hφ).choose_spec

theorem ptH_comp_j_of_one (hU : UnivC πM ptM Φ) {S' : Type} [CommRing S']
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) (h1 : eA LA s ≫ φ = (LB.one s).1) :
    (ptH LA LB πM ptM Φ j hZ hU S' s φ hφ).1 ≫ j = (ptM S' s φ hφ).1 := by
  rw [ptH_comp_j, ptM_congr πM ptM s (retr_w LA LB s φ hφ) hφ (retr_eq_self LA LB s φ hφ h1)]

theorem one_of_factor (hU : UnivC πM ptM Φ) {S' : Type} [CommRing S']
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s)
    (w : Spec (CommRingCat.of S') ⟶ Z) (hw : w ≫ j = (ptM S' s φ hφ).1) : eA LA s ≫ φ = (LB.one s).1 := by
  have h := (hZ (ptM S' s φ hφ).1).mpr ⟨w, hw⟩
  rwa [comp_uM LA πM ptM Φ hU, comp_vM] at h

end Mor
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm"

end HomSchemeAsm
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm"

namespace HomSchemeAsm

variable {S : Type} [CommRing S] {A B : Scheme.{0}}
  {f : A ⟶ Spec (CommRingCat.of S)} {g : B ⟶ Spec (CommRingCat.of S)}
  (LA : RelativeGroupLaw S f) (LB : RelativeGroupLaw S g)
  (hAc : LA.IsCommutative) (hBc : LB.IsCommutative)
  (hA : AbelianSchemePropertyBundle S f) (hB : AbelianSchemePropertyBundle S g)
  {M : Scheme.{0}} (πM : M ⟶ Spec (CommRingCat.of S))
  (ptM : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ : pullback f s ⟶ B), φ ≫ g = pullback.snd f s ≫ s → SchemeHomOver s πM)
  (Φ : pullback f πM ⟶ B) {Z : Scheme.{0}} (j : Z ⟶ M)
  (hZ : ∀ {T' : Scheme.{0}} (ψ : T' ⟶ M), ψ ≫ uM LA πM Φ = ψ ≫ vM LB πM ↔ ∃ ψ' : T' ⟶ Z, ψ' ≫ j = ψ)
  (hU : UnivC πM ptM Φ)

section Clauses

include hZ hU

theorem natH [Mono j] (hnat : NatC πM ptM)
    (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
    (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
    (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
    (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) :
    (ptH LA LB πM ptM Φ j hZ hU S'' s'' (bc ψ s s'' hs ≫ φ) (bc_comp_w ψ s s'' hs φ hφ)).1 =
      Spec.map (CommRingCat.ofHom ψ) ≫ (ptH LA LB πM ptM Φ j hZ hU S' s φ hφ).1 := by
  rw [← cancel_mono j, Category.assoc, ptH_comp_j, ptH_comp_j,
    ← hnat S' S'' ψ s s'' hs (retr LA LB s φ hφ) (retr_w LA LB s φ hφ)]
  exact congrArg Subtype.val
    (ptM_congr πM ptM s'' _ _ (bc_comp_retr LA LB ψ s s'' hs φ hφ).symm)

include hAc hBc hA hB

theorem surjH [Mono j] (hsurj : SurjC πM ptM)
    (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver s (j ≫ πM)) :
    ∃ (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s),
      IsHom LA LB s φ hφ ∧ ptH LA LB πM ptM Φ j hZ hU S' s φ hφ = x := by
  obtain ⟨φ, hφ, hpt⟩ := hsurj S' s ⟨x.1 ≫ j, by rw [Category.assoc]; exact x.2⟩
  have h1 : eA LA s ≫ φ = (LB.one s).1 :=
    one_of_factor LA LB πM ptM Φ j hZ hU s φ hφ x.1 (by rw [hpt])
  refine ⟨φ, hφ, (isHom_iff LA LB hAc hBc hA hB s φ hφ).mpr h1, ?_⟩
  apply Subtype.ext
  rw [← cancel_mono j, ptH_comp_j_of_one LA LB πM ptM Φ j hZ hU s φ hφ h1, hpt]

theorem injH [Mono j] (hinj : InjC πM ptM)
    (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
    (φ φ' : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) (hφ' : φ' ≫ g = pullback.snd f s ≫ s)
    (h : IsHom LA LB s φ hφ) (h' : IsHom LA LB s φ' hφ')
    (he : ptH LA LB πM ptM Φ j hZ hU S' s φ hφ = ptH LA LB πM ptM Φ j hZ hU S' s φ' hφ') : φ = φ' := by
  have h1 := (isHom_iff LA LB hAc hBc hA hB s φ hφ).mp h
  have h1' := (isHom_iff LA LB hAc hBc hA hB s φ' hφ').mp h'
  apply hinj S' s φ φ' hφ hφ'
  apply Subtype.ext
  rw [← ptH_comp_j_of_one LA LB πM ptM Φ j hZ hU s φ hφ h1, ← ptH_comp_j_of_one LA LB πM ptM Φ j hZ hU s φ' hφ' h1',
    he]

theorem unramH [Mono j] (hnat : NatC πM ptM) (hsurj : SurjC πM ptM) (hinj : InjC πM ptM) :
    FormallyUnramified (j ≫ πM) := by
  apply AlgebraicGeometry.formallyUnramified_of_forall_specMap_comp_eq_imp_eq
  intro S' S'' _ _ ψ hψs hker s x₁ x₂ hx₁ hx₂ hagree
  obtain ⟨φ₁, hφ₁, hpt₁⟩ := hsurj S' s ⟨x₁ ≫ j, by rw [Category.assoc]; exact hx₁⟩
  obtain ⟨φ₂, hφ₂, hpt₂⟩ := hsurj S' s ⟨x₂ ≫ j, by rw [Category.assoc]; exact hx₂⟩
  have h1 : eA LA s ≫ φ₁ = (LB.one s).1 := one_of_factor LA LB πM ptM Φ j hZ hU s φ₁ hφ₁ x₁ (by rw [hpt₁])
  have h2 : eA LA s ≫ φ₂ = (LB.one s).1 := one_of_factor LA LB πM ptM Φ j hZ hU s φ₂ hφ₂ x₂ (by rw [hpt₂])
  have hom₁ := (isHom_iff LA LB hAc hBc hA hB s φ₁ hφ₁).mpr h1
  have hom₂ := (isHom_iff LA LB hAc hBc hA hB s φ₂ hφ₂).mpr h2

  have e1 : (ptM S'' (Spec.map (CommRingCat.ofHom ψ) ≫ s) (bc ψ s _ rfl ≫ φ₁) (bc_comp_w ψ s _ rfl φ₁ hφ₁)).1 =
      Spec.map (CommRingCat.ofHom ψ) ≫ (ptM S' s φ₁ hφ₁).1 := hnat S' S'' ψ s _ rfl φ₁ hφ₁
  have e2 : (ptM S'' (Spec.map (CommRingCat.ofHom ψ) ≫ s) (bc ψ s _ rfl ≫ φ₂) (bc_comp_w ψ s _ rfl φ₂ hφ₂)).1 =
      Spec.map (CommRingCat.ofHom ψ) ≫ (ptM S' s φ₂ hφ₂).1 := hnat S' S'' ψ s _ rfl φ₂ hφ₂
  have hbc : bc ψ s _ rfl ≫ φ₁ = bc ψ s _ rfl ≫ φ₂ := by
    apply hinj S'' (Spec.map (CommRingCat.ofHom ψ) ≫ s) _ _ (bc_comp_w ψ s _ rfl φ₁ hφ₁) (bc_comp_w ψ s _ rfl φ₂ hφ₂)
    apply Subtype.ext
    rw [e1, e2, hpt₁, hpt₂]
    show Spec.map (CommRingCat.ofHom ψ) ≫ x₁ ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ x₂ ≫ j
    rw [← Category.assoc, hagree, Category.assoc]
  have hm : pullback.map f (Spec.map (CommRingCat.ofHom ψ) ≫ s) f s (𝟙 A) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
      (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id]) = bc ψ s _ rfl := by
    apply pullback.hom_ext
    · delta pullback.map
      rw [pullback.lift_fst, bc, pullback.lift_fst, Category.comp_id]
    · delta pullback.map
      rw [pullback.lift_snd, bc, pullback.lift_snd]
  have hred : pullback.map f (Spec.map (CommRingCat.ofHom ψ) ≫ s) f s (𝟙 A) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
        (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id]) ≫ φ₁ =
      pullback.map f (Spec.map (CommRingCat.ofHom ψ) ≫ s) f s (𝟙 A) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
        (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id]) ≫ φ₂ := by
    rw [hm]; exact hbc
  have hφeq : φ₁ = φ₂ :=
    GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker
      S f g LA LB hAc hBc hA hB S' S'' ψ hψs ⟨2, hker⟩ s φ₁ φ₂ hφ₁ hφ₂ hom₁ hom₂ hred
  rw [← cancel_mono j]
  have e : (⟨x₁ ≫ j, by rw [Category.assoc]; exact hx₁⟩ : SchemeHomOver s πM) =
      ⟨x₂ ≫ j, by rw [Category.assoc]; exact hx₂⟩ := by
    rw [← hpt₁, ← hpt₂]; exact ptM_congr πM ptM s hφ₁ hφ₂ hφeq
  exact congrArg Subtype.val e

theorem piecesH [IsClosedImmersion j] (𝓛A : A.Modules) (𝓛B : B.Modules)
    (hpieces : ∀ Pℚ : Polynomial ℚ, ∃ U : M.Opens, IsClosed (U : Set M) ∧ QuasiCompact (U.ι ≫ πM) ∧
        ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s),
          (Set.range (ptM S' s φ hφ).1.base ⊆ (U : Set M) ↔
            ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (pullback.snd f s)
                (Nat.rec (motive := fun _ => (pullback f s).Modules) (𝟙_ (pullback f s).Modules)
                  (fun _ M => M ⊗ ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛A ⊗ (Scheme.Modules.pullback φ).obj 𝓛B)) d) k sk : ℕ) : ℚ) = Pℚ.eval (d : ℚ)))
    (Pℚ : Polynomial ℚ) :
    ∃ U : Z.Opens, IsClosed (U : Set Z) ∧ QuasiCompact (U.ι ≫ j ≫ πM) ∧
        ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s),
          IsHom LA LB s φ hφ →
          (Set.range (ptH LA LB πM ptM Φ j hZ hU S' s φ hφ).1.base ⊆ (U : Set Z) ↔
            ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (pullback.snd f s)
                (Nat.rec (motive := fun _ => (pullback f s).Modules) (𝟙_ (pullback f s).Modules)
                  (fun _ M => M ⊗ ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛A ⊗ (Scheme.Modules.pullback φ).obj 𝓛B)) d) k sk : ℕ) : ℚ) = Pℚ.eval (d : ℚ)) := by
  obtain ⟨U, hUc, hUqc, hU'⟩ := hpieces Pℚ
  refine ⟨j ⁻¹ᵁ U, hUc.preimage j.continuous, ?_, ?_⟩
  · haveI := hUqc
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    infer_instance
  · intro S' _ s φ hφ hhom
    have h1 := (isHom_iff LA LB hAc hBc hA hB s φ hφ).mp hhom
    rw [← hU' S' s φ hφ, ← ptH_comp_j_of_one LA LB πM ptM Φ j hZ hU s φ hφ h1]
    constructor
    · rintro h _ ⟨y, rfl⟩
      have hy := h ⟨y, rfl⟩
      simpa using hy
    · rintro h _ ⟨y, rfl⟩
      have hy := h ⟨y, rfl⟩
      simpa using hy

end Clauses
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm"

end HomSchemeAsm
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections.HomSchemeAsm"

theorem solution
    (S : Type) [CommRing S] {A B : Scheme.{0}}
    (f : A ⟶ Spec (CommRingCat.of S)) (g : B ⟶ Spec (CommRingCat.of S))
    (LA : RelativeGroupLaw S f) (LB : RelativeGroupLaw S g)
    (hAc : LA.IsCommutative) (hBc : LB.IsCommutative)
    (hA : AbelianSchemePropertyBundle S f) (hB : AbelianSchemePropertyBundle S g)
    (𝓛A : A.Modules) (hA₁ : Scheme.Modules.IsInvertible 𝓛A) (hA₂ : Scheme.Modules.ClosedImmersionBySections 𝓛A f)
    (𝓛B : B.Modules) (hB₁ : Scheme.Modules.IsInvertible 𝓛B) (hB₂ : Scheme.Modules.ClosedImmersionBySections 𝓛B g) :
    ∃ (H : Scheme.{0}) (πH : H ⟶ Spec (CommRingCat.of S))
      (pt : ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (φ : pullback f s ⟶ B), φ ≫ g = pullback.snd f s ≫ s → SchemeHomOver s πH),

      (∀ (S' S'' : Type) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s),
        (pt S'' s''
            (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ)
            (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs])).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ).1) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πH),
        ∃ (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ =
              (LB.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) ∧
          pt S' s φ hφ = x) ∧

      (∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ φ' : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s) (hφ' : φ' ≫ g = pullback.snd f s ≫ s),
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ =
              (LB.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
        (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ' =
              (LB.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ', by rw [Category.assoc, hφ', ← Category.assoc, pullback.lift_snd]⟩).1) →
        pt S' s φ hφ = pt S' s φ' hφ' → φ = φ') ∧
      IsSeparated πH ∧ LocallyOfFiniteType πH ∧ LocallyOfFinitePresentation πH ∧ FormallyUnramified πH ∧

      (∀ Pℚ : Polynomial ℚ, ∃ U : H.Opens, IsClosed (U : Set H) ∧ QuasiCompact (U.ι ≫ πH) ∧
        ∀ (S' : Type) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ : pullback f s ⟶ B) (hφ : φ ≫ g = pullback.snd f s ≫ s),
          (∀ (T : Scheme.{0}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver (t' ≫ s) f),
            pullback.lift (LA.mul (t' ≫ s) P Q).1 t' (LA.mul (t' ≫ s) P Q).2 ≫ φ =
              (LB.mul (t' ≫ s)
                ⟨pullback.lift P.1 t' P.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩
                ⟨pullback.lift Q.1 t' Q.2 ≫ φ, by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd]⟩).1) →
          (Set.range (pt S' s φ hφ).1.base ⊆ (U : Set H) ↔
            ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k), ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
              ((Scheme.Modules.geomFibreH0Finrank (pullback.snd f s)
                (Nat.rec (motive := fun _ => (pullback f s).Modules) (𝟙_ (pullback f s).Modules)
                  (fun _ M => M ⊗ ((Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛A ⊗ (Scheme.Modules.pullback φ).obj 𝓛B)) d) k sk : ℕ) : ℚ) = Pℚ.eval (d : ℚ))) := by
  haveI : Smooth f := hA.smooth
  haveI : IsProper f := hA.proper
  haveI : Smooth g := hB.smooth
  haveI : IsProper g := hB.proper
  obtain ⟨M, πM, ptM, hnat, hsurj, hinj, hsep, hlfp, hpieces⟩ :=
    AlgebraicGeometry.exists_scheme_represents_schemeHomOver_hilbertPieces_of_isProper_of_flat
      S f g 𝓛A hA₁ hA₂ 𝓛B hB₁ hB₂
  obtain ⟨Φ, hΦg, hU⟩ :=
    AlgebraicGeometry.exists_hom_pullback_comp_eq_and_forall_pullbackMap_comp_eq_of_forall_spec_point
      S f g πM ptM hnat hsurj hinj
  obtain ⟨Z, j, hjci, hjlfp, hZ⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated g πM
      (HomSchemeAsm.uM LA πM Φ) (HomSchemeAsm.vM LB πM) (HomSchemeAsm.uM_w LA πM Φ hΦg) (HomSchemeAsm.vM_w LB πM)
  haveI := hjci
  haveI := hsep
  haveI := hlfp
  haveI : LocallyOfFinitePresentation j := hjlfp inferInstance
  refine ⟨Z, j ≫ πM, HomSchemeAsm.ptH LA LB πM ptM Φ j hZ hU, ?_, ?_, ?_, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact HomSchemeAsm.natH LA LB πM ptM Φ j hZ hU hnat
  · exact HomSchemeAsm.surjH LA LB hAc hBc hA hB πM ptM Φ j hZ hU hsurj
  · exact HomSchemeAsm.injH LA LB hAc hBc hA hB πM ptM Φ j hZ hU hinj
  · exact HomSchemeAsm.unramH LA LB hAc hBc hA hB πM ptM Φ j hZ hU hnat hsurj hinj
  · exact HomSchemeAsm.piecesH LA LB hAc hBc hA hB πM ptM Φ j hZ hU 𝓛A 𝓛B hpieces

end S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections (solution)
