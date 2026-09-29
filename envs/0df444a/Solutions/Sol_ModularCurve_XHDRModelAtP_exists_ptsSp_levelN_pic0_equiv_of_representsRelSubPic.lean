-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_ptsSp_levelN_pic0_equiv_of_representsRelSubPic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8ef16302-25e5-545e-b55c-de567fd0cc11

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_abelJacobi_of_representsRelSubPic
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi
import Theorems.Thm_ModularCurve_isProper_and_smooth_and_geometricallyIntegral_twoChartIntegralModel_qExpFunctionFieldC_of_not_dvd
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_foldr_twist_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_ptsSp_levelN_pic0_equiv_of_representsRelSubPic
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions SheafOfModules.isIso_ihomModelToIhom AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module"
p2m_attr_erase "instance" "DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"
p2m_attr_erase "simp" "AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply"
p2m_attr_erase "simp" "TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero"
p2m_attr_erase "simp" "TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open ModularCurve.JHNeronObjectAtP (Fbar)
open scoped MatrixGroups

universe u

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace L0aSKit

theorem mul_val_congr {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (ht : t₁ = t₂)
    (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f) (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst ht
  obtain rfl : x₁ = x₂ := Subtype.ext hx
  obtain rfl : y₁ = y₂ := Subtype.ext hy
  rfl

def monoidalCancel {C : Type*} [Category C] [MonoidalCategory C] {M M' N N' : C}
    (eN : N ⊗ N' ≅ 𝟙_ C) (e : M ⊗ N ≅ M' ⊗ N) : M ≅ M' :=
  (ρ_ M).symm ≪≫ (whiskerLeftIso M eN.symm) ≪≫ (α_ M N N').symm ≪≫ (whiskerRightIso e N') ≪≫ α_ M' N N' ≪≫
    whiskerLeftIso M' eN ≪≫ ρ_ M'

section foldr
variable {X : Scheme.{u}} {ι : Type*}

abbrev twistStep (K : ι → X.IdealSheafData) (pos neg : ι → ℕ) (i : ι) (M : X.Modules) : X.Modules :=
  (K i ^ pos i).invModule ⊗ (K i ^ neg i).module ⊗ M

def foldrTwistCongr (K : ι → X.IdealSheafData) (pos neg : ι → ℕ) :
    ∀ (l : List ι) {M M' : X.Modules} (_ : M ≅ M'),
      l.foldr (twistStep K pos neg) M ≅ l.foldr (twistStep K pos neg) M'
  | [], _, _, e => e
  | (i :: l), _, _, e => whiskerLeftIso _ (whiskerLeftIso _ (foldrTwistCongr K pos neg l e))

theorem top_pow (n : ℕ) : (⊤ : X.IdealSheafData) ^ n = ⊤ := by
  rw [← Scheme.IdealSheafData.one_eq_top, one_pow]

end foldr

section top
variable {X : Scheme.{u}}

theorem subsingleton_sections_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z] (V : Z.Opens) :
    Subsingleton Γ(Z, V) := by
  obtain rfl : V = ⊥ := by
    ext x
    exact (IsEmpty.false x).elim
  exact CommRingCat.subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty Z.sheaf)

theorem unitToPushforwardUnit_eq_zero_of_isEmpty {Z : Scheme.{u}} (i : Z ⟶ X) [IsEmpty Z] :
    i.unitToPushforwardUnit = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  haveI : Subsingleton Γ(Z, i ⁻¹ᵁ U.unop) := subsingleton_sections_of_isEmpty _
  exact Subsingleton.elim (α := Γ(Z, i ⁻¹ᵁ U.unop)) _ _

def topModuleIso : (⊤ : X.IdealSheafData).module ≅ 𝟙_ X.Modules :=
  (kernelIsoOfEq (unitToPushforwardUnit_eq_zero_of_isEmpty (⊤ : X.IdealSheafData).subschemeι) ≪≫
    kernelZeroIsoSource : (kernel ((⊤ : X.IdealSheafData).subschemeι.unitToPushforwardUnit) :
      SheafOfModules X.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf)

theorem nonempty_topInvModuleIso : Nonempty ((⊤ : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules) :=
  MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit (topModuleIso (X := X))
    (Scheme.IdealSheafData.isInvertible_top (X := X)).nonempty_module_tensor_invModule_iso.1 ⟨λ_ _⟩

def topInvModuleIso : (⊤ : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules := nonempty_topInvModuleIso.some

def twistStepTopIso {ι : Type*} (K : ι → X.IdealSheafData) (pos neg : ι → ℕ) (i : ι) (hi : K i = ⊤)
    {M M' : X.Modules} (e : M ≅ M') : twistStep K pos neg i M ≅ M' :=
  ((eqToIso (by rw [hi, top_pow]) : (K i ^ pos i).invModule ≅ (⊤ : X.IdealSheafData).invModule) ⊗ᵢ
    ((eqToIso (by rw [hi, top_pow]) : (K i ^ neg i).module ≅ (⊤ : X.IdealSheafData).module) ⊗ᵢ e)) ≪≫
    (topInvModuleIso ⊗ᵢ (topModuleIso ⊗ᵢ Iso.refl M')) ≪≫ ((λ_ _) ≪≫ (λ_ _))

def twistStepCongr {ι : Type*} (K K' : ι → X.IdealSheafData) (pos neg : ι → ℕ) (i : ι) (hi : K i = K' i)
    {M M' : X.Modules} (e : M ≅ M') : twistStep K pos neg i M ≅ twistStep K' pos neg i M' :=
  ((eqToIso (by rw [hi]) : (K i ^ pos i).invModule ≅ (K' i ^ pos i).invModule) ⊗ᵢ
    ((eqToIso (by rw [hi]) : (K i ^ neg i).module ≅ (K' i ^ neg i).module) ⊗ᵢ e))

def foldrTwistSelectIso {ι : Type*} {κ : Type*} [DecidableEq κ] (c : ι → κ) (j : κ)
    (K K' : ι → X.IdealSheafData) (pos neg : ι → ℕ)
    (h₁ : ∀ i, c i = j → K i = K' i) (h₂ : ∀ i, c i ≠ j → K i = ⊤) :
    ∀ (l : List ι) {M M' : X.Modules} (_ : M ≅ M'),
      l.foldr (twistStep K pos neg) M ≅
        l.foldr (fun i N => if c i = j then twistStep K' pos neg i N else N) M'
  | [], _, _, e => e
  | (i :: l), M, M', e => by
    by_cases hc : c i = j
    · refine twistStepCongr K K' pos neg i (h₁ i hc) (foldrTwistSelectIso c j K K' pos neg h₁ h₂ l e) ≪≫ eqToIso ?_
      simp only [List.foldr_cons, if_pos hc]
    · refine twistStepTopIso K pos neg i (h₂ i hc) (foldrTwistSelectIso c j K K' pos neg h₁ h₂ l e) ≪≫ eqToIso ?_
      simp only [List.foldr_cons, if_neg hc]

end top

theorem comap_ker_eq_ker_of_isPullback {X₀ X T Z : Scheme.{u}} {iX : Z ⟶ X₀} {g : Z ⟶ T} {f : X₀ ⟶ X}
    {iY : T ⟶ X} [IsClosedImmersion iY] (H : IsPullback iX g f iY) : iY.ker.comap f = iX.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← H.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

theorem exists_schemeHomOver_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {A : Type u} [CommRing A] [IsLocalRing A] (tA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (v₁ v₂ : SchemeHomOver tA c) :
    ∃ s₀ : SchemeHomOver tA D.toBase, Nonempty ((h.poincare.pullbackAlong s₀).L ≅
      (RelEffCartierDiv.ofPoint c v₁.1 v₁.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c v₂.1 v₂.2).idealModule) := by
  classical

  let σ : Fin 2 → SchemeHomOver tA c := ![v₁, v₂]
  let pos : Fin 2 → ℕ := ![1, 0]
  let neg : Fin 2 → ℕ := ![0, 1]
  have hdeg : (∑ i, ((pos i : ℤ) - (neg i : ℤ))) = 0 := by decide
  let K : Fin 2 → (pullback c tA).IdealSheafData := fun i => (RelEffCartierDiv.ofPoint c (σ i).1 (σ i).2).I

  have hKinv : ∀ i, (K i).IsInvertible := fun i =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c tA) (graphOver c (σ i).1 (σ i).2) (graphOver_snd _ _ _)
  let Lv : (pullback c tA).Modules :=
    (RelEffCartierDiv.ofPoint c v₁.1 v₁.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c v₂.1 v₂.2).idealModule
  have hLv : Scheme.Modules.IsInvertible Lv := (hKinv 0).isInvertible_invModule.tensor (hKinv 1).isInvertible_module
  let Mr : RigidifiedLineBundle c ε tA :=
    { L := Lv
      isInvertible := hLv
      rigidified := (hLv.pullback (rigSection c tA ε)).nonempty_iso_tensorUnit_of_isLocalRing }

  have eT : (List.finRange 2).foldr (twistStep K pos neg) (𝟙_ (pullback c tA).Modules) ≅ Lv := by
    have hfr : List.finRange 2 = [(0 : Fin 2), 1] := rfl
    rw [hfr]
    show (K 0 ^ 1).invModule ⊗ ((K 0 ^ 0).module ⊗ ((K 1 ^ 0).invModule ⊗ ((K 1 ^ 1).module ⊗ 𝟙_ _))) ≅
      (K 0).invModule ⊗ (K 1).module
    refine (eqToIso (by rw [pow_one]) ⊗ᵢ ((eqToIso (by rw [pow_zero, Scheme.IdealSheafData.one_eq_top]) ≪≫ topModuleIso) ⊗ᵢ
      ((eqToIso (by rw [pow_zero, Scheme.IdealSheafData.one_eq_top]) ≪≫ topInvModuleIso) ⊗ᵢ
        (eqToIso (by rw [pow_one]) ⊗ᵢ Iso.refl _)))) ≪≫ ?_
    exact whiskerLeftIso _ (λ_ _ ≪≫ λ_ _ ≪≫ ρ_ _)

  have hAEZ : FibrewiseAlgEquivZero Mr := by
    intro k _ _ sk
    show IsAlgEquivZero (fibreAt c tA sk) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c tA) sk)).obj Lv)
    let ψ : SchemeHomOver (sk ≫ tA) tA := ⟨sk, rfl⟩
    let c' := pullback.snd c (sk ≫ tA)
    let x : Fin 2 → (Spec (CommRingCat.of k) ⟶ pullback c (sk ≫ tA)) := fun i =>
      graphOver c (ψ.1 ≫ (σ i).1) (by rw [Category.assoc, (σ i).2, ψ.2])
    have hx : ∀ i, x i ≫ c' = 𝟙 _ := fun i => graphOver_snd _ _ _
    let Φ₂ : pullback c (sk ≫ tA) ⟶ pullback c tA := baseChangeSnd c ψ
    let pr : pullback c' (𝟙 (Spec (CommRingCat.of k))) ⟶ _ := pullback.fst c' (𝟙 (Spec (CommRingCat.of k)))
    let Φ := pr ≫ Φ₂
    let K' : Fin 2 → (pullback c' (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData := fun i =>
      (RelEffCartierDiv.ofPoint c' (x i) (hx i)).I
    have hab : ∀ i, (K i).comap Φ₂ = (x i).ker := fun i =>
      congrArg RelEffCartierDiv.I (RelEffCartierDiv.pullbackAlong_ofPoint c (σ i).1 (σ i).2 ψ.1 ψ.2)
    have hgeo : ∀ i, (x i).ker.comap pr = K' i := by
      intro i
      have sq : CommSq (graphOver c' (x i) (hx i)) (𝟙 _) pr (x i) := ⟨by rw [Category.id_comp]; exact graphOver_fst _ _ _⟩
      exact comap_ker_eq_ker_of_isPullback (IsPullback.of_vert_isIso sq)
    have hKΦ : ∀ i, (K i).comap Φ = K' i := by
      intro i
      rw [Scheme.IdealSheafData.comap_comp, hab, hgeo i]
    have hK'inv : ∀ i, ((K i).comap Φ).IsInvertible := by
      intro i
      rw [hKΦ i]
      exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c' (𝟙 _)) (graphOver c' (x i) (hx i)) (graphOver_snd _ _ _)
    have h1inv : ∀ (Z : Scheme.{u}), (1 : Z.IdealSheafData).IsInvertible := fun Z => by
      rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
    let C0 : Fin 0 → (pullback c tA).IdealSheafData := fun _ => ⊤
    let a0 : Fin 0 → ℕ := fun _ => 0
    have hprod : (∏ F, C0 F ^ a0 F) = 1 := Fintype.prod_empty _
    have hprod' : (∏ F, (C0 F).comap Φ ^ a0 F) = 1 := Fintype.prod_empty _
    obtain ⟨eB⟩ : Nonempty ((∏ F, C0 F ^ a0 F).invModule ⊗ (∏ F, C0 F ^ a0 F).module ≅ 𝟙_ _) := by
      rw [hprod]; exact (h1inv _).nonempty_module_tensor_invModule_iso.2
    obtain ⟨eB'⟩ : Nonempty ((∏ F, (C0 F).comap Φ ^ a0 F).invModule ⊗ (∏ F, (C0 F).comap Φ ^ a0 F).module ≅ 𝟙_ _) := by
      rw [hprod']; exact (h1inv _).nonempty_module_tensor_invModule_iso.2
    obtain ⟨e4⟩ := Scheme.Modules.nonempty_pullback_foldr_twist_iso Φ K pos neg C0 a0 a0 hKinv
      (fun F => F.elim0) hK'inv (fun F => F.elim0)
    let c0 : Fin 2 → Fin 1 := fun _ => 0
    have eN : (Scheme.Modules.pullback Φ).obj ((List.finRange 2).foldr (twistStep K pos neg) (𝟙_ _)) ≅
        (List.finRange 2).foldr (fun i N => if c0 i = 0 then twistStep K' pos neg i N else N) (𝟙_ _) :=
      (Scheme.Modules.pullback Φ).mapIso (foldrTwistCongr K pos neg _ eB.symm) ≪≫ e4 ≪≫
        foldrTwistCongr _ pos neg _ eB' ≪≫
        foldrTwistSelectIso c0 0 (fun i => (K i).comap Φ) K' pos neg (fun i _ => hKΦ i) (fun i h => absurd rfl h) _ (Iso.refl _)
    have hdeg' : (∑ i ∈ Finset.univ.filter (fun i => c0 i = 0), ((pos i : ℤ) - (neg i : ℤ))) = 0 := by
      rw [Finset.filter_true_of_mem (fun _ _ => rfl)]; exact hdeg
    have hS := AlgebraicGeometry.RelPicard.isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero c' x hx (fun i => c0 i = 0) pos neg hdeg'
    have hY : IsAlgEquivZero (pullback.snd c' (𝟙 _)) ((Scheme.Modules.pullback Φ).obj Lv) :=
      (hS.of_iso eN.symm).of_iso ((Scheme.Modules.pullback Φ).mapIso eT)

    have comm₁ : (pullback.fst (pullback.snd c tA) sk ≫ pullback.fst c tA) ≫ c =
        pullback.snd (pullback.snd c tA) sk ≫ sk ≫ tA := by
      simp only [Category.assoc, pullback.condition, pullback.condition_assoc]
    let g₁ : pullback (pullback.snd c tA) sk ⟶ pullback c (sk ≫ tA) := pullback.lift _ _ comm₁
    let g : pullback (pullback.snd c tA) sk ⟶ pullback c' (𝟙 (Spec (CommRingCat.of k))) :=
      pullback.lift g₁ (pullback.snd _ sk) (by rw [Category.comp_id]; exact pullback.lift_snd _ _ _)
    have hg : g ≫ pullback.snd c' (𝟙 _) = fibreAt c tA sk := pullback.lift_snd _ _ _
    have hgΦ : g ≫ Φ = pullback.fst (pullback.snd c tA) sk := by
      dsimp only [g, g₁, Φ, Φ₂, pr, ψ]
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_fst', pullback.lift_fst_assoc, pullback.lift_fst]
      · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_snd', pullback.lift_fst_assoc, pullback.lift_snd_assoc,
          pullback.condition]
    have hF := hY.pullback g hg
    exact hF.of_iso ((Scheme.Modules.pullbackComp g Φ).app _ ≪≫ (Scheme.Modules.pullbackCongr hgΦ).app _)

  obtain ⟨s₀, hs₀, -⟩ := h.univ tA Mr hAEZ
  exact ⟨s₀, hs₀⟩

end L0aSKit

end

namespace L0aSKit

def castOver' {B T X : Scheme.{u}} {ι ι' : T ⟶ B} {f : X ⟶ B} (h : ι = ι') (x : SchemeHomOver ι f) :
    SchemeHomOver ι' f :=
  ⟨x.1, x.2.trans h⟩

theorem castOver'_val {B T X : Scheme.{u}} {ι ι' : T ⟶ B} {f : X ⟶ B} (h : ι = ι') (x : SchemeHomOver ι f) :
    (castOver' h x).1 = x.1 := rfl

def castOverEquiv' {B T X : Scheme.{u}} {ι ι' : T ⟶ B} {f : X ⟶ B} (h : ι = ι') :
    SchemeHomOver ι f ≃ SchemeHomOver ι' f where
  toFun := castOver' h
  invFun := castOver' h.symm
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem castOverEquiv'_apply {B T X : Scheme.{u}} {ι ι' : T ⟶ B} {f : X ⟶ B} (h : ι = ι') (x : SchemeHomOver ι f) :
    castOverEquiv' h x = castOver' h x := rfl

theorem val_ofFibrePt_baseChange_mul {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} (Lw : RelativeGroupLaw R f)
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} (x y : SchemeHomOver ι f) :
    (ofFibrePt ((Lw.baseChange ι).mul (𝟙 _) (toFibrePt x) (toFibrePt y))).1 = (Lw.mul ι x y).1 := by
  simp only [ofFibrePt, toFibrePt, overId, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase]
  exact mul_val_congr _ (Category.id_comp _) _ _ _ _ rfl rfl

theorem val_ofFibrePt_baseChange_mul_castOver {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} (Lw : RelativeGroupLaw R f)
    {ι ι' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} (h : ι = ι') (x y : SchemeHomOver ι f) :
    (ofFibrePt ((Lw.baseChange ι').mul (𝟙 _) (toFibrePt (castOver' h x)) (toFibrePt (castOver' h y)))).1 = (Lw.mul ι x y).1 := by
  subst h
  exact val_ofFibrePt_baseChange_mul Lw x y

end L0aSKit

set_option maxHeartbeats 16000000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [IsSeparated (toBase p (ΓN p M H hpM) hj)]
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)

    (hsm₀ : Smooth D₀.toBase) (hpr₀ : IsProper D₀.toBase) (hgc₀ : GeometricallyConnected D₀.toBase) :
    ∃ ptsSp₀ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ≃
        SchemeHomOver (resPt A ≫ Spec.map (CommRingCat.ofHom ρ)) D₀.toBase,

      (∀ a b, ptsSp₀ (a + b) =
        ofFibrePt (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange
          (resPt A ≫ Spec.map (CommRingCat.ofHom ρ))).mul _ (toFibrePt (ptsSp₀ a)) (toFibrePt (ptsSp₀ b)))) ∧

      (∀ (v₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₁.1)
      (_ : vκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 = vκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (v₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj))
      (vκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : vκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ v₂.1)
      (_ : vκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 = vκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 - Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D₀.toBase,
        Nonempty ((hD₀.poincare.pullbackAlong s₀).L ≅
          (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₁.1 v₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) v₂.1 v₂.2).idealModule) ∧
        ptsSp₀.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw) := by
  classical

  haveI : NeZero (M / p) := neZero_div p M hpM
  have hpN : ¬ p ∣ M / p := by
    intro h
    apply hpM2
    obtain ⟨k, hk⟩ := h
    refine ⟨k, ?_⟩
    have := Nat.div_mul_cancel hpM
    rw [hk] at this
    rw [pow_two]
    linarith [this]
  have hΓ₁ : CongruenceSubgroup.Gamma1 (M / p) ≤ ΓN p M H hpM := Gamma1_le_GammaH (M / p) _
  have hΓ₀ : ΓN p M H hpM ≤ CongruenceSubgroup.Gamma0 (M / p) := CohCarrier.GammaH_le_Gamma0 _
  obtain ⟨hP0, hS0, hG0⟩ :=
    ModularCurve.isProper_and_smooth_and_geometricallyIntegral_twoChartIntegralModel_qExpFunctionFieldC_of_not_dvd
      (M / p) (ΓN p M H hpM) hΓ₁ hΓ₀ p hpN (jAt (ΓN p M H hpM) hj) (coe_jAt _ hj)
  haveI := hP0; haveI := hS0; haveI := hG0

  haveI : IsCurveOver (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) := by
    obtain ⟨x, -, hx, hfd⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
      (ResidueField ↥A) (ΓN p M H hpM) (translation_mem_GammaH _ _)
    exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hx hfd
  obtain ⟨aj, hajε, haj⟩ := AlgebraicGeometry.RelPicard.exists_abelJacobi_of_representsRelSubPic (R p)
    (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) D₀ hD₀
  obtain ⟨-, hdict⟩ := AlgebraicGeometry.RelPicard.exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi (R p)
    (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) D₀ hD₀ hsm₀ hpr₀ hgc₀ aj hajε haj
  obtain ⟨pts, hadd, hnorm⟩ := hdict (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)
    (Fbar p M H hpM (ResidueField ↥A)) (𝔛.Mfib A hA ρ hρ) (𝔛.efib A hA ρ hρ) (𝔛.hefib A hA ρ hρ)

  have hbase : Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) = resPt A ≫ Spec.map (CommRingCat.ofHom ρ) := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine ⟨pts.trans (L0aSKit.castOverEquiv' hbase), ?_, ?_⟩
  ·
    intro a b
    apply Subtype.ext
    rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, L0aSKit.castOverEquiv'_apply, L0aSKit.castOverEquiv'_apply,
      L0aSKit.castOverEquiv'_apply, L0aSKit.castOver'_val, hadd]
    exact (L0aSKit.val_ofFibrePt_baseChange_mul_castOver _ hbase (pts a) (pts b)).symm

  intro v₁ vκ₁ hvκ₁f hvκ₁s Q₁ hQ₁ v₂ vκ₂ hvκ₂f hvκ₂s Q₂ hQ₂ Dw hDw

  obtain ⟨s₀, hs₀⟩ := L0aSKit.exists_schemeHomOver_poincare_pullbackAlong_iso_ofPoint_tensor_ofPoint
    (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) hD₀ (Spec.map (CommRingCat.ofHom ρ)) v₁ v₂
  refine ⟨s₀, hs₀, ?_⟩
  obtain ⟨eS⟩ := hs₀

  rw [Equiv.symm_apply_eq, Equiv.trans_apply, L0aSKit.castOverEquiv'_apply]
  apply Subtype.ext
  rw [L0aSKit.castOver'_val, NeronModelInfra.schemeHomOverComp_coe]
  have hg'c : (resPt A ≫ s₀.1) ≫ D₀.toBase = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    rw [Category.assoc, s₀.2, hbase]
  let g' : SchemeHomOver (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) D₀.toBase := ⟨resPt A ≫ s₀.1, hg'c⟩
  suffices hfin : pts (Pic0.mk Dw) = g' from (congrArg Subtype.val hfin).symm
  refine hD₀.ext_of_iso _ (pts (Pic0.mk Dw)) g' ?_

  haveI := 𝔛.efib_iso A hA ρ hρ
  have hinv : inv (𝔛.efib A hA ρ hρ) ≫ (𝔛.Mfib A hA ρ hρ).toBase =
      pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) := by
    rw [IsIso.inv_comp_eq, 𝔛.hefib]

  have hεc : (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) ≫ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π).1) ≫
      toBase p (ΓN p M H hpM) hj = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    rw [Category.assoc, (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π).2, Category.comp_id, Category.id_comp]
  let εpt : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) :=
    pullback.lift _ _ hεc
  let εbar : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (𝔛.Mfib A hA ρ hρ).C // q ≫ (𝔛.Mfib A hA ρ hρ).toBase = 𝟙 _} :=
    ⟨εpt ≫ inv (𝔛.efib A hA ρ hρ), by rw [Category.assoc, hinv, pullback.lift_snd]⟩
  have hεbar : εbar.1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) ≫ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π).1 := by
    show (εpt ≫ inv _) ≫ _ ≫ _ = _
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

  let x₁ : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (𝔛.Mfib A hA ρ hρ).C // q ≫ (𝔛.Mfib A hA ρ hρ).toBase = 𝟙 _} :=
    ⟨vκ₁ ≫ inv (𝔛.efib A hA ρ hρ), by rw [Category.assoc, hinv, hvκ₁s]⟩
  let x₂ : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (𝔛.Mfib A hA ρ hρ).C // q ≫ (𝔛.Mfib A hA ρ hρ).toBase = 𝟙 _} :=
    ⟨vκ₂ ≫ inv (𝔛.efib A hA ρ hρ), by rw [Category.assoc, hinv, hvκ₂s]⟩
  have hx₁ : x₁.1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst _ _ = resPt A ≫ v₁.1 := by
    show (vκ₁ ≫ inv _) ≫ _ ≫ _ = _
    rw [Category.assoc, IsIso.inv_hom_id_assoc, hvκ₁f]
  have hx₂ : x₂.1 ≫ 𝔛.efib A hA ρ hρ ≫ pullback.fst _ _ = resPt A ≫ v₂.1 := by
    show (vκ₂ ≫ inv _) ≫ _ ≫ _ = _
    rw [Category.assoc, IsIso.inv_hom_id_assoc, hvκ₂f]

  have hbase_inv : ∀ (Q : closedPoints (𝔛.Mfib A hA ρ hρ).C) (vκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      (𝔛.efib A hA ρ hρ).base Q.1 = vκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) →
      (vκ ≫ inv (𝔛.efib A hA ρ hρ)).base (IsLocalRing.closedPoint (ResidueField ↥A)) = Q.1 := by
    intro Q vκ hQ
    show (inv (𝔛.efib A hA ρ hρ)).base (vκ.base _) = Q.1
    rw [← hQ]
    exact congrArg (fun f : (𝔛.Mfib A hA ρ hρ).C ⟶ (𝔛.Mfib A hA ρ hρ).C => f.base Q.1) (IsIso.hom_inv_id (𝔛.efib A hA ρ hρ))
  have hpl₁ : (𝔛.Mfib A hA ρ hρ).pointEquivPlace x₁ = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁ := by
    rw [CurveModel.pointEquivPlace_apply]
    congr 1
    exact Subtype.ext (hbase_inv Q₁ vκ₁ hQ₁)
  have hpl₂ : (𝔛.Mfib A hA ρ hρ).pointEquivPlace x₂ = (𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂ := by
    rw [CurveModel.pointEquivPlace_apply]
    congr 1
    exact Subtype.ext (hbase_inv Q₂ vκ₂ hQ₂)

  obtain ⟨D₁, hD₁, hD₁pts⟩ := hnorm x₁ εbar hεbar
  obtain ⟨D₂, hD₂, hD₂pts⟩ := hnorm x₂ εbar hεbar
  have hDw12 : Dw = D₁ - D₂ := by
    apply Subtype.ext
    rw [AddSubgroupClass.coe_sub, hDw, hD₁, hD₂, hpl₁, hpl₂]
    abel

  let Lw := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀
  letI grp : Group (SchemeHomOver (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) D₀.toBase) := Lw.pointGroup _
  letI := RepresentsRelSubPic.grpObj (P := algEquivZeroGroupCut _ _) hD₀
  have pts_mul : ∀ x y, pts (x + y) = pts x * pts y := fun x y => hadd x y
  have hkey : pts (Pic0.mk Dw) * pts (Pic0.mk D₂) = pts (Pic0.mk D₁) := by
    rw [← pts_mul]
    congr 1
    show (QuotientAddGroup.mk' _) Dw + (QuotientAddGroup.mk' _) D₂ = (QuotientAddGroup.mk' _) D₁
    rw [← map_add, hDw12, sub_add_cancel]

  have hxb₁ : (resPt A ≫ v₁.1) ≫ toBase p (ΓN p M H hpM) hj = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    rw [Category.assoc, v₁.2]; exact hbase.symm
  have hxb₂ : (resPt A ≫ v₂.1) ≫ toBase p (ΓN p M H hpM) hj = Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) := by
    rw [Category.assoc, v₂.2]; exact hbase.symm
  let xb₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) (toBase p (ΓN p M H hpM) hj) :=
    ⟨resPt A ≫ v₁.1, hxb₁⟩
  let xb₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) (toBase p (ΓN p M H hpM) hj) :=
    ⟨resPt A ≫ v₂.1, hxb₂⟩
  have hP₁ : pts (Pic0.mk D₁) = ⟨xb₁.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (xb₁.1 ≫ ·) aj.2).trans xb₁.2)⟩ := by
    apply Subtype.ext
    show (pts (Pic0.mk D₁)).1 = (resPt A ≫ v₁.1) ≫ aj.1
    rw [hD₁pts, ← hx₁]; simp only [Category.assoc]
  have hP₂ : pts (Pic0.mk D₂) = ⟨xb₂.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (xb₂.1 ≫ ·) aj.2).trans xb₂.2)⟩ := by
    apply Subtype.ext
    show (pts (Pic0.mk D₂)).1 = (resPt A ≫ v₂.1) ≫ aj.1
    rw [hD₂pts, ← hx₂]; simp only [Category.assoc]
  have hN₁ := haj _ (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) xb₁
  have hN₂ := haj _ (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) xb₂
  rw [← hP₁] at hN₁
  rw [← hP₂] at hN₂
  obtain ⟨eP₁⟩ := hN₁
  obtain ⟨eP₂⟩ := hN₂

  have hPmul : ∀ a b : SchemeHomOver (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) D₀.toBase,
      Nonempty ((hD₀.poincare.pullbackAlong (a * b)).L ≅ (hD₀.poincare.pullbackAlong a).L ⊗ (hD₀.poincare.pullbackAlong b).L) := by
    intro a b
    have := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso (P := algEquivZeroGroupCut _ _) hD₀
      (T := Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) (schemeHomOverToOverHom a) (schemeHomOverToOverHom b)
    exact this
  have hPone : Nonempty ((hD₀.poincare.pullbackAlong (1 : SchemeHomOver (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) D₀.toBase)).L ≅
      𝟙_ (pullback (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).Modules) := by
    have := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso (P := algEquivZeroGroupCut _ _) hD₀
      (Over.mk (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))
    exact this

  have hI₂ := Scheme.Hom.isInvertible_ker_of_comp_eq_id
    (p := pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))))
    (graphOver (toBase p (ΓN p M H hpM) hj) (resPt A ≫ v₂.1) hxb₂) (graphOver_snd _ _ _)
  obtain ⟨⟨eI₂⟩, -⟩ := hI₂.nonempty_module_tensor_invModule_iso
  obtain ⟨em⟩ := hPmul (pts (Pic0.mk Dw)) (pts (Pic0.mk D₂))
  have hba : hD₀.poincare.pullbackAlong (pts (Pic0.mk Dw) * pts (Pic0.mk D₂)) = hD₀.poincare.pullbackAlong (pts (Pic0.mk D₁)) := by
    rw [hkey]
  have eL : (hD₀.poincare.pullbackAlong (pts (Pic0.mk Dw))).L ⊗ (hD₀.poincare.pullbackAlong (pts (Pic0.mk D₂))).L ≅
      (hD₀.poincare.pullbackAlong (pts (Pic0.mk D₁))).L := em.symm ≪≫ eqToIso (congrArg (fun M => M.L) hba)
  obtain ⟨em2⟩ := hPmul (pts (Pic0.mk D₂)) (pts (Pic0.mk D₂))⁻¹
  obtain ⟨e1⟩ := hPone
  have hone : hD₀.poincare.pullbackAlong (pts (Pic0.mk D₂) * (pts (Pic0.mk D₂))⁻¹) = hD₀.poincare.pullbackAlong 1 := by
    rw [mul_inv_cancel]
  have eN : (hD₀.poincare.pullbackAlong (pts (Pic0.mk D₂))).L ⊗ (hD₀.poincare.pullbackAlong (pts (Pic0.mk D₂))⁻¹).L ≅ 𝟙_ _ :=
    em2.symm ≪≫ eqToIso (congrArg (fun M => M.L) hone) ≪≫ e1
  let L₁ := (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) (resPt A ≫ v₁.1) hxb₁).lineBundle
  let L₂ := (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) (resPt A ≫ v₂.1) hxb₂).lineBundle
  let J₂ := (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) (resPt A ≫ v₂.1) hxb₂).idealModule
  let Jε := (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj)
    (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) ≫ (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π).1)
    ((Category.assoc _ _ _).trans ((congrArg (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)) ≫ ·)
      (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π).2).trans (Category.comp_id _)))).idealModule
  have e' : (L₁ ⊗ J₂) ⊗ (hD₀.poincare.pullbackAlong (pts (Pic0.mk D₂))).L ≅ (hD₀.poincare.pullbackAlong (pts (Pic0.mk D₁))).L :=
    whiskerLeftIso (L₁ ⊗ J₂) eP₂ ≪≫ α_ L₁ J₂ (L₂ ⊗ Jε) ≪≫ whiskerLeftIso L₁ ((α_ J₂ L₂ Jε).symm ≪≫ whiskerRightIso eI₂ Jε ≪≫ λ_ Jε) ≪≫
      eP₁.symm
  have eLM : (hD₀.poincare.pullbackAlong (pts (Pic0.mk Dw))).L ≅ L₁ ⊗ J₂ := L0aSKit.monoidalCancel eN (eL ≪≫ e'.symm)

  have eR : Nonempty ((hD₀.poincare.pullbackAlong g').L ≅ L₁ ⊗ J₂) := by
    let ψ : SchemeHomOver (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) (Spec.map (CommRingCat.ofHom ρ)) :=
      ⟨resPt A, hbase.symm⟩
    have hcomp : baseChangeSnd (toBase p (ΓN p M H hpM) hj) g' =
        baseChangeSnd (toBase p (ΓN p M H hpM) hj) ψ ≫ baseChangeSnd (toBase p (ΓN p M H hpM) hj) s₀ := by
      apply pullback.hom_ext
      · rw [Category.assoc, BaseChange.baseChangeSnd_fst', BaseChange.baseChangeSnd_fst', BaseChange.baseChangeSnd_fst']
      · rw [Category.assoc, BaseChange.baseChangeSnd_snd', BaseChange.baseChangeSnd_snd']
        simp only [← Category.assoc]
        rw [BaseChange.baseChangeSnd_snd']
        exact (Category.assoc _ _ _).symm
    haveI : SmoothOfRelativeDimension 1 ((⊤ : (X p (ΓN p M H hpM) hj).Opens).ι ≫ toBase p (ΓN p M H hpM) hj) := by
      have h01 : SmoothOfRelativeDimension (0 + 1) ((⊤ : (X p (ΓN p M H hpM) hj).Opens).ι ≫ toBase p (ΓN p M H hpM) hj) := inferInstance
      exact h01
    have htop : ∀ (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓN p M H hpM) hj)),
        Set.range u.1.base ⊆ ((⊤ : (X p (ΓN p M H hpM) hj).Opens) : Set (X p (ΓN p M H hpM) hj)) := fun u x _ => trivial
    obtain ⟨⟨e₁⟩, -⟩ := AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
      (R p) (toBase p (ΓN p M H hpM) hj) ⊤ v₁ (htop v₁) ψ hxb₁
    obtain ⟨-, ⟨e₂⟩⟩ := AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
      (R p) (toBase p (ΓN p M H hpM) hj) ⊤ v₂ (htop v₂) ψ hxb₂
    exact ⟨(Scheme.Modules.pullbackCongr hcomp).app hD₀.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd (toBase p (ΓN p M H hpM) hj) ψ)).mapIso eS ≪≫
      Scheme.Modules.pullbackTensorObjIso (baseChangeSnd (toBase p (ΓN p M H hpM) hj) ψ) _ _ ≪≫ (e₁ ⊗ᵢ e₂)⟩
  obtain ⟨eR⟩ := eR
  exact ⟨eLM ≪≫ eR.symm⟩

end S_ModularCurve_XHDRModelAtP_exists_ptsSp_levelN_pic0_equiv_of_representsRelSubPic
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_ptsSp_levelN_pic0_equiv_of_representsRelSubPic (solution)
