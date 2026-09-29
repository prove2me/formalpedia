-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_sameComponent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/cfcc3bb6-b6ce-5470-a944-29d892f87071

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
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
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_rigidifiedLineBundle_ofPoint_tensor_ofPoint_fibrewiseAlgEquivZero_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_supportedIn_ofPoint
import Theorems.Thm_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
import Theorems.Thm_ModularCurve_finite_ssPlacesQExp
import Theorems.Thm_ModularCurve_nonempty_ssPlacesQExp
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_sameComponent
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module"
p2m_attr_erase "instance" "TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

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

namespace L0aSKit

theorem isAlgEquivZero_fibreAt_ofPoint_invModule_tensor_ofPoint_module
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    {A : Type u} [CommRing A] (tA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (v₁ v₂ : SchemeHomOver tA c)
    (hK₁ : (RelEffCartierDiv.ofPoint c v₁.1 v₁.2).I.IsInvertible) (hK₂ : (RelEffCartierDiv.ofPoint c v₂.1 v₂.2).I.IsInvertible)
    (k : Type u) [Field k] [IsAlgClosed k] (sk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
    [IsProper (pullback.snd c (sk ≫ tA))] [SmoothOfRelativeDimension 1 (pullback.snd c (sk ≫ tA))]
    [GeometricallyIntegral (pullback.snd c (sk ≫ tA))] :
    IsAlgEquivZero (fibreAt c tA sk) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c tA) sk)).obj
      ((RelEffCartierDiv.ofPoint c v₁.1 v₁.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c v₂.1 v₂.2).idealModule)) := by
  classical
  let σ : Fin 2 → SchemeHomOver tA c := ![v₁, v₂]
  let pos : Fin 2 → ℕ := ![1, 0]
  let neg : Fin 2 → ℕ := ![0, 1]
  have hdeg : (∑ i, ((pos i : ℤ) - (neg i : ℤ))) = 0 := by decide
  let K : Fin 2 → (pullback c tA).IdealSheafData := fun i => (RelEffCartierDiv.ofPoint c (σ i).1 (σ i).2).I
  have hKinv : ∀ i, (K i).IsInvertible := fun i => by
    fin_cases i
    · exact hK₁
    · exact hK₂
  let Lv : (pullback c tA).Modules :=
    (RelEffCartierDiv.ofPoint c v₁.1 v₁.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c v₂.1 v₂.2).idealModule
  have eT : (List.finRange 2).foldr (twistStep K pos neg) (𝟙_ (pullback c tA).Modules) ≅ Lv := by
    have hfr : List.finRange 2 = [(0 : Fin 2), 1] := rfl
    rw [hfr]
    show (K 0 ^ 1).invModule ⊗ ((K 0 ^ 0).module ⊗ ((K 1 ^ 0).invModule ⊗ ((K 1 ^ 1).module ⊗ 𝟙_ _))) ≅
      (K 0).invModule ⊗ (K 1).module
    refine (eqToIso (by rw [pow_one]) ⊗ᵢ ((eqToIso (by rw [pow_zero, Scheme.IdealSheafData.one_eq_top]) ≪≫ topModuleIso) ⊗ᵢ
      ((eqToIso (by rw [pow_zero, Scheme.IdealSheafData.one_eq_top]) ≪≫ topInvModuleIso) ⊗ᵢ
        (eqToIso (by rw [pow_one]) ⊗ᵢ Iso.refl _)))) ≪≫ ?_
    exact whiskerLeftIso _ (λ_ _ ≪≫ λ_ _ ≪≫ ρ_ _)
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

end L0aSKit

namespace L0aSKit

theorem smoothOfRelativeDimension_one_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [SmoothOfRelativeDimension 1 f] : SmoothOfRelativeDimension 1 g := by
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.inv f).mpr ‹_›
end L0aSKit

set_option maxHeartbeats 16000000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [IsSeparated (toBase p (ΓM M H) hj)]
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D) :
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∀ (hDκ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔛.εinf))
        (D.baseChange (ResidueField ↥A)))
      (_ : Nonempty (hDκ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf (ResidueField ↥A)
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))
      (i : Fin 2)
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (huκ₁ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (_ : uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ i).base)
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (huκ₂ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (_ : uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ i).base),
    ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
      Nonempty ((hD.poincare.pullbackAlong s).L ≅
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₁.1 u₁.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u₂.1 u₂.2).idealModule) ∧
      ∀ (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (D.baseChange (ResidueField ↥A)).toBase),
        y.1 ≫ pullback.fst _ _ = resPt A ≫ s.1 →
        Nonempty ((hDκ.poincare.pullbackAlong y).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A)) uκ₁ huκ₁).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) (ResidueField ↥A)) uκ₂ huκ₂).idealModule) := by
  intro hDκ hP i u₁ hu₁ uκ₁ huκ₁f huκ₁ hc₁ u₂ hu₂ uκ₂ huκ₂f huκ₂ hc₂
  classical
  letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra

  haveI : NeZero (M / p) := neZero_div p M hpM
  haveI := 𝔛.isProper
  haveI := 𝔛.isProper0
  haveI := 𝔛.smooth0
  haveI := 𝔛.smoothLocus_relDim
  haveI : (ΓN p M H hpM).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH (M / p) _)
  have hpN : ¬ p ∣ M / p := by
    intro h; apply hpM2; obtain ⟨k, hk⟩ := h; refine ⟨k, ?_⟩
    have := Nat.div_mul_cancel hpM; rw [hk] at this; rw [pow_two]; linarith [this]
  obtain ⟨-, -, hG0⟩ :=
    ModularCurve.isProper_and_smooth_and_geometricallyIntegral_twoChartIntegralModel_qExpFunctionFieldC_of_not_dvd
      (M / p) (ΓN p M H hpM) (Gamma1_le_GammaH (M / p) _) (CohCarrier.GammaH_le_Gamma0 _) p hpN (jAt (ΓN p M H hpM) hj) (coe_jAt _ hj)
  haveI := hG0
  haveI hci : ∀ j, IsClosedImmersion (𝔛.comp A hA ρ hρ j) := 𝔛.comp_isClosedImmersion A hA ρ hρ

  let c := toBase p (ΓM M H) hj
  let c₀ := toBase p (ΓN p M H hpM) hj
  let tA : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of (R p)) := Spec.map (CommRingCat.ofHom ρ)
  let tκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Spec (CommRingCat.of (R p)) :=
    Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))
  have hbase : tκ = resPt A ≫ tA := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let x : pullback c tκ ⟶ Spec (CommRingCat.of (ResidueField ↥A)) := pullback.snd c tκ
  let ψred : SchemeHomOver tκ tA := ⟨resPt A, hbase.symm⟩
  let B : pullback c tκ ⟶ pullback c tA := baseChangeSnd c ψred
  let Θ : pullback x (𝟙 _) ⟶ pullback c tκ := pullback.fst x (𝟙 _)

  have hK : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of (R p))} (u : SchemeHomOver t c),
      Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) → (RelEffCartierDiv.ofPoint c u.1 u.2).I.IsInvertible :=
    fun u hu => RelEffCartierDiv.isInvertible_I_of_supportedIn 𝔛.smoothLocus _
      (RelEffCartierDiv.supportedIn_ofPoint u.1 u.2 𝔛.smoothLocus (fun t => hu ⟨t, rfl⟩))
  let Lu : (pullback c tA).Modules :=
    (RelEffCartierDiv.ofPoint c u₁.1 u₁.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c u₂.1 u₂.2).idealModule
  have hLu : Scheme.Modules.IsInvertible Lu := (hK u₁ hu₁).isInvertible_invModule.tensor (hK u₂ hu₂).isInvertible_module
  let Mr : RigidifiedLineBundle c 𝔛.εinf tA :=
    { L := Lu
      isInvertible := hLu
      rigidified := (hLu.pullback (rigSection c tA 𝔛.εinf)).nonempty_iso_tensorUnit_of_isLocalRing }

  have hXred : IsReduced (pullback c tκ) := 𝔛.fibre_reduced A hA ρ hρ

  obtain ⟨j, hij⟩ : ∃ j : Fin 2, (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
    fin_cases i
    · exact ⟨1, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨0, Or.inr ⟨rfl, rfl⟩⟩
  have hjs : ∀ z : ↥(pullback c tκ), z ∈ Set.range (𝔛.comp A hA ρ hρ i).base ∨ z ∈ Set.range (𝔛.comp A hA ρ hρ j).base := by
    intro z
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact 𝔛.comp_jointly_surjective A hA ρ hρ z
    · exact (𝔛.comp_jointly_surjective A hA ρ hρ z).symm
  have hcr : IsReduced (pullback (𝔛.comp A hA ρ hρ i) (𝔛.comp A hA ρ hρ j)) := by
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact 𝔛.crossing_reduced A hA ρ hρ
    · haveI := 𝔛.crossing_reduced A hA ρ hρ
      exact isReduced_of_isOpenImmersion (pullbackSymmetry (𝔛.comp A hA ρ hρ 1) (𝔛.comp A hA ρ hρ 0)).hom
  have hs0 : 0 < Nat.card ↥(pullback (𝔛.comp A hA ρ hρ i) (𝔛.comp A hA ρ hρ j)) := by
    haveI : Finite ↥(ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p) :=
      (ModularCurve.finite_ssPlacesQExp (ResidueField ↥A) p (ΓN p M H hpM) (translation_mem_GammaH _ _)).to_subtype
    haveI : Nonempty ↥(ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p) :=
      (ModularCurve.nonempty_ssPlacesQExp (M / p) (ΓN p M H hpM) (Gamma1_le_GammaH (M / p) _) (CohCarrier.GammaH_le_Gamma0 _)
        p hpN (ResidueField ↥A)).to_subtype
    haveI : Finite ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) := Finite.of_equiv _ (𝔛.nodeEquiv A hA ρ hρ).symm
    haveI : Nonempty ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)) := Nonempty.map (𝔛.nodeEquiv A hA ρ hρ).symm inferInstance
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Nat.card_pos
    · rw [Nat.card_congr (Scheme.homeoOfIso (pullbackSymmetry (𝔛.comp A hA ρ hρ 1) (𝔛.comp A hA ρ hρ 0))).toEquiv]
      exact Nat.card_pos

  have hsm : ∀ (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1),
      ¬ (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
         uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 1).base) := by
    intro u hu uκ huκ
    refine (ModularCurve.XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter p M H hpM hpM2 hj 𝔛 A hA ρ hρ _).1 ?_
    show (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
      (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))
    apply hu
    exact ⟨(Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))).base (IsLocalRing.closedPoint (ResidueField ↥A)),
      (congrArg (fun f => f.base (IsLocalRing.closedPoint (ResidueField ↥A))) huκ).symm⟩
  have hoff : ∀ (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)),
      ¬ (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 0).base ∧
         uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ 1).base) →
      uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈ Set.range (𝔛.comp A hA ρ hρ i).base →
      uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉ Set.range (𝔛.comp A hA ρ hρ j).base := by
    intro uκ h hi hj'
    rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h ⟨hi, hj'⟩
    · exact h ⟨hj', hi⟩
  have hoff₁ := hoff uκ₁ (hsm u₁ hu₁ uκ₁ huκ₁f) hc₁
  have hoff₂ := hoff uκ₂ (hsm u₂ hu₂ uκ₂ huκ₂f) hc₂

  obtain ⟨g₁, hg₁, -⟩ := AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced
    (𝔛.comp A hA ρ hρ i) uκ₁ (by
      rintro _ ⟨z, rfl⟩
      obtain rfl : z = IsLocalRing.closedPoint _ := Subsingleton.elim _ _
      exact hc₁)
  obtain ⟨g₂, hg₂, -⟩ := AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced
    (𝔛.comp A hA ρ hρ i) uκ₂ (by
      rintro _ ⟨z, rfl⟩
      obtain rfl : z = IsLocalRing.closedPoint _ := Subsingleton.elim _ _
      exact hc₂)
  subst hg₁
  subst hg₂
  have hP₁ : g₁ ≫ pullback.snd c₀ tκ = 𝟙 _ := by
    rw [← 𝔛.comp_over A hA ρ hρ i, ← Category.assoc]; exact huκ₁
  have hP₂ : g₂ ≫ pullback.snd c₀ tκ = 𝟙 _ := by
    rw [← 𝔛.comp_over A hA ρ hρ i, ← Category.assoc]; exact huκ₂

  have hεc : (tκ ≫ 𝔛.εinf.1) ≫ c = 𝟙 _ ≫ tκ := by
    rw [Category.assoc, 𝔛.εinf.2, Category.comp_id, Category.id_comp]
  let εκ : SchemeHomOver (𝟙 _) x := ⟨pullback.lift _ _ hεc, pullback.lift_snd _ _ _⟩

  obtain ⟨Mκ, ⟨eM⟩, hMκ⟩ :=
    AlgebraicGeometry.RelPicard.exists_rigidifiedLineBundle_ofPoint_tensor_ofPoint_fibrewiseAlgEquivZero_of_twoGluedSmoothCurves
      (k := ResidueField ↥A) x hXred (pullback.snd c₀ tκ) (pullback.snd c₀ tκ)
      ⟨𝔛.comp A hA ρ hρ i, 𝔛.comp_over A hA ρ hρ i⟩ ⟨𝔛.comp A hA ρ hρ j, 𝔛.comp_over A hA ρ hρ j⟩
      hjs hcr (Nat.card ↥(pullback (𝔛.comp A hA ρ hρ i) (𝔛.comp A hA ρ hρ j))) rfl hs0 εκ ⟨g₁, hP₁⟩ ⟨g₂, hP₂⟩ hoff₁ hoff₂

  have hū : ∀ (u : SchemeHomOver tA c), (resPt A ≫ u.1) ≫ c = tκ := fun u => by
    rw [Category.assoc, u.2]; exact hbase.symm
  have hūsm : ∀ (u : SchemeHomOver tA c), Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) →
      Set.range (resPt A ≫ u.1).base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) := by
    rintro u hu _ ⟨z, rfl⟩
    exact hu ⟨(resPt A).base z, rfl⟩
  have hgr : ∀ (u : SchemeHomOver tA c) (g : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback c₀ tκ)
      (_ : (g ≫ 𝔛.comp A hA ρ hρ i) ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : (g ≫ 𝔛.comp A hA ρ hρ i) ≫ pullback.snd _ _ = 𝟙 _),
      graphOver c (resPt A ≫ u.1) (hū u) = g ≫ 𝔛.comp A hA ρ hρ i := by
    intro u g hgf hgs
    apply pullback.hom_ext
    · rw [graphOver_fst, hgf]
    · rw [graphOver_snd, hgs]
  have hgr₁ := hgr u₁ g₁ huκ₁f huκ₁
  have hgr₂ := hgr u₂ g₂ huκ₂f huκ₂
  have hI₁ : (g₁ ≫ 𝔛.comp A hA ρ hρ i).ker.IsInvertible := by
    rw [← hgr₁]; exact hK ⟨resPt A ≫ u₁.1, hū u₁⟩ (hūsm u₁ hu₁)
  have hI₂ : (g₂ ≫ 𝔛.comp A hA ρ hρ i).ker.IsInvertible := by
    rw [← hgr₂]; exact hK ⟨resPt A ≫ u₂.1, hū u₂⟩ (hūsm u₂ hu₂)
  haveI : IsClosedImmersion (g₁ ≫ 𝔛.comp A hA ρ hρ i) := by rw [← hgr₁]; infer_instance
  haveI : IsClosedImmersion (g₂ ≫ 𝔛.comp A hA ρ hρ i) := by rw [← hgr₂]; infer_instance
  let p₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback x (𝟙 _) := graphOver x (g₁ ≫ 𝔛.comp A hA ρ hρ i) huκ₁
  let p₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback x (𝟙 _) := graphOver x (g₂ ≫ 𝔛.comp A hA ρ hρ i) huκ₂
  have hp₁ : p₁ ≫ Θ = g₁ ≫ 𝔛.comp A hA ρ hρ i := graphOver_fst _ _ _
  have hp₂ : p₂ ≫ Θ = g₂ ≫ 𝔛.comp A hA ρ hρ i := graphOver_fst _ _ _
  have hI₁' : p₁.ker.IsInvertible := by
    have sq : CommSq p₁ (𝟙 _) Θ (g₁ ≫ 𝔛.comp A hA ρ hρ i) := ⟨by rw [Category.id_comp]; exact hp₁⟩
    rw [← L0aSKit.comap_ker_eq_ker_of_isPullback (IsPullback.of_vert_isIso sq)]
    exact hI₁.comap_of_isOpenImmersion Θ
  have hI₂' : p₂.ker.IsInvertible := by
    have sq : CommSq p₂ (𝟙 _) Θ (g₂ ≫ 𝔛.comp A hA ρ hρ i) := ⟨by rw [Category.id_comp]; exact hp₂⟩
    rw [← L0aSKit.comap_ker_eq_ker_of_isPullback (IsPullback.of_vert_isIso sq)]
    exact hI₂.comap_of_isOpenImmersion Θ
  have bridge : Nonempty ((Scheme.Modules.pullback (Θ ≫ B)).obj Lu ≅
      (RelEffCartierDiv.ofPoint x (g₁ ≫ 𝔛.comp A hA ρ hρ i) huκ₁).lineBundle ⊗
        (RelEffCartierDiv.ofPoint x (g₂ ≫ 𝔛.comp A hA ρ hρ i) huκ₂).idealModule) := by
    obtain ⟨⟨e₁⟩, -⟩ := AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
      (R p) c 𝔛.smoothLocus u₁ hu₁ ψred (hū u₁)
    obtain ⟨-, ⟨e₂⟩⟩ := AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
      (R p) c 𝔛.smoothLocus u₂ hu₂ ψred (hū u₂)
    obtain ⟨⟨j₁⟩, -⟩ := Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso Θ (g₁ ≫ 𝔛.comp A hA ρ hρ i) p₁ hp₁ hI₁ hI₁' 1
    obtain ⟨-, ⟨j₂⟩⟩ := Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso Θ (g₂ ≫ 𝔛.comp A hA ρ hρ i) p₂ hp₂ hI₂ hI₂' 1
    have j₁' : (Scheme.Modules.pullback Θ).obj (RelEffCartierDiv.ofPoint c (resPt A ≫ u₁.1) (hū u₁)).lineBundle ≅
        (RelEffCartierDiv.ofPoint x (g₁ ≫ 𝔛.comp A hA ρ hρ i) huκ₁).lineBundle :=
      (Scheme.Modules.pullback Θ).mapIso (eqToIso (by
          show (graphOver c (resPt A ≫ u₁.1) (hū u₁)).ker.invModule = _
          rw [hgr₁, pow_one])) ≪≫ j₁ ≪≫ eqToIso (by rw [pow_one]; rfl)
    have j₂' : (Scheme.Modules.pullback Θ).obj (RelEffCartierDiv.ofPoint c (resPt A ≫ u₂.1) (hū u₂)).idealModule ≅
        (RelEffCartierDiv.ofPoint x (g₂ ≫ 𝔛.comp A hA ρ hρ i) huκ₂).idealModule :=
      (Scheme.Modules.pullback Θ).mapIso (eqToIso (by
          show (graphOver c (resPt A ≫ u₂.1) (hū u₂)).ker.module = _
          rw [hgr₂, pow_one])) ≪≫ j₂ ≪≫ eqToIso (by rw [pow_one]; rfl)
    exact ⟨((Scheme.Modules.pullbackComp Θ B).app Lu).symm ≪≫
      (Scheme.Modules.pullback Θ).mapIso (Scheme.Modules.pullbackTensorObjIso B _ _ ≪≫ (e₁ ⊗ᵢ e₂)) ≪≫
      Scheme.Modules.pullbackTensorObjIso Θ _ _ ≪≫ (j₁' ⊗ᵢ j₂')⟩

  have hAEZ : FibrewiseAlgEquivZero Mr := by
    intro k _ _ sk
    show IsAlgEquivZero (fibreAt c tA sk) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c tA) sk)).obj Lu)
    by_cases hpt : IsLocalRing.closedPoint ↥A ∈ Set.range sk.base
    ·
      obtain ⟨φ, hφ⟩ : ∃ φ : ResidueField ↥A →+* k, sk = Spec.map (CommRingCat.ofHom φ) ≫ resPt A := by
        obtain ⟨ψ, hψ⟩ : ∃ g, Spec.map g = sk := ⟨Spec.preimage sk, Spec.map_preimage sk⟩
        subst hψ
        obtain ⟨z, hz⟩ := hpt
        have hz' : z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
        subst hz'
        haveI : IsLocalHom ψ.hom := by
          rw [IsLocalRing.isLocalHom_iff_comap_closedPoint]
          exact hz
        refine ⟨IsLocalRing.ResidueField.lift ψ.hom, ?_⟩
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalRing.ResidueField.lift_comp_residue]
        rfl

      have comm₂ : (pullback.fst (pullback.snd c tA) sk ≫ pullback.fst c tA) ≫ c =
          (pullback.snd (pullback.snd c tA) sk ≫ Spec.map (CommRingCat.ofHom φ)) ≫ tκ := by
        rw [hbase]; simp only [Category.assoc, pullback.condition, pullback.condition_assoc, hφ]
      let g₂' : pullback (pullback.snd c tA) sk ⟶ pullback c tκ := pullback.lift _ _ comm₂
      let g₁' : pullback (pullback.snd c tA) sk ⟶ pullback x (𝟙 _) :=
        pullback.lift g₂' (pullback.snd _ sk ≫ Spec.map (CommRingCat.ofHom φ)) (by rw [Category.comp_id]; exact pullback.lift_snd _ _ _)
      let g : pullback (pullback.snd c tA) sk ⟶ pullback (pullback.snd x (𝟙 _)) (Spec.map (CommRingCat.ofHom φ)) :=
        pullback.lift g₁' (pullback.snd _ sk) (pullback.lift_snd _ _ _)
      have hg : g ≫ pullback.snd _ _ = fibreAt c tA sk := pullback.lift_snd _ _ _
      have hgΘB : (g ≫ pullback.fst _ _) ≫ Θ ≫ B = pullback.fst (pullback.snd c tA) sk := by
        have h1 : (g ≫ pullback.fst _ _) ≫ Θ = g₂' := by
          rw [Category.assoc]
          show g ≫ pullback.fst _ _ ≫ pullback.fst x (𝟙 _) = g₂'
          rw [pullback.lift_fst_assoc, pullback.lift_fst]
        rw [← Category.assoc, h1]
        apply pullback.hom_ext
        · rw [Category.assoc, BaseChange.baseChangeSnd_fst', pullback.lift_fst]
        · rw [Category.assoc, BaseChange.baseChangeSnd_snd', pullback.lift_snd_assoc, pullback.condition, hφ]
          simp only [Category.assoc]
          rfl
      have h2 := (hMκ k (Spec.map (CommRingCat.ofHom φ))).pullback g hg
      obtain ⟨br⟩ := bridge
      refine h2.of_iso ?_
      exact (Scheme.Modules.pullbackComp g _).app _ ≪≫
        (Scheme.Modules.pullback (g ≫ pullback.fst _ _)).mapIso (eM ≪≫ br.symm) ≪≫
        (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hgΘB).app _
    ·

      obtain ⟨ψ, rfl⟩ : ∃ g, Spec.map g = sk := ⟨Spec.preimage sk, Spec.map_preimage sk⟩
      have hker : RingHom.ker ψ.hom ≠ IsLocalRing.maximalIdeal ↥A := by
        intro hkm
        apply hpt
        haveI : IsLocalHom ψ.hom := by
          refine ⟨fun a ha => ?_⟩
          by_contra hna
          have hm : a ∈ IsLocalRing.maximalIdeal ↥A := hna
          rw [← hkm, RingHom.mem_ker] at hm
          exact ha.ne_zero hm
        exact ⟨IsLocalRing.closedPoint k, IsLocalRing.comap_closedPoint ψ.hom⟩
      haveI : (RingHom.ker ψ.hom).IsPrime := RingHom.ker_isPrime _
      have hbot : RingHom.ker ψ.hom = ⊥ :=
        ValuationSubring.eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime (Fact.out) A hA _ hker
      have hinj : Function.Injective ψ.hom := (RingHom.injective_iff_ker_eq_bot _).mpr hbot
      let φ : AlgebraicClosure ℚ →+* k := IsFractionRing.lift hinj
      have hφ : φ.comp A.subtype = ψ.hom := by
        ext a
        exact IsFractionRing.lift_algebraMap hinj a

      let sQ : Spec (CommRingCat.of ℚ) ⟶ Spec (CommRingCat.of (R p)) := Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))
      let sQk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℚ) :=
        Spec.map (CommRingCat.ofHom (φ.comp (algebraMap ℚ (AlgebraicClosure ℚ))))
      have hsk : Spec.map ψ ≫ tA = sQk ≫ sQ := by
        show Spec.map ψ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom,
          ← hφ, RingHom.comp_assoc, hρ, IsScalarTower.algebraMap_eq (R p) ℚ (AlgebraicClosure ℚ), ← RingHom.comp_assoc]

      haveI := 𝔛.smooth_generic
      haveI := 𝔛.geomIntegral_generic
      let e : pullback c (Spec.map ψ ≫ tA) ≅ pullback (pullback.snd c sQ) sQk :=
        pullback.congrHom rfl hsk ≪≫ (pullbackLeftPullbackSndIso c sQ sQk).symm
      have he : e.hom ≫ pullback.snd (pullback.snd c sQ) sQk = pullback.snd c (Spec.map ψ ≫ tA) := by
        rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← pullbackLeftPullbackSndIso_hom_snd c sQ sQk, Iso.inv_hom_id_assoc,
          pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
      haveI : IsProper (pullback.snd c (Spec.map ψ ≫ tA)) := by rw [← he]; infer_instance
      haveI : SmoothOfRelativeDimension 1 (pullback.snd c (Spec.map ψ ≫ tA)) :=
        L0aSKit.smoothOfRelativeDimension_one_of_iso e.symm he
      haveI : GeometricallyIntegral (pullback.snd c (Spec.map ψ ≫ tA)) := by
        rw [← he]
        exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral e.hom _).mpr inferInstance
      exact L0aSKit.isAlgEquivZero_fibreAt_ofPoint_invModule_tensor_ofPoint_module c tA u₁ u₂ (hK u₁ hu₁) (hK u₂ hu₂) k (Spec.map ψ)

  obtain ⟨s, hs, -⟩ := hD.univ tA Mr hAEZ
  refine ⟨s, hs, ?_⟩

  intro y hy
  obtain ⟨eP⟩ := hP
  obtain ⟨br⟩ := bridge

  have hψ' : resPt A ≫ tA = 𝟙 _ ≫ specMap (R p) (ResidueField ↥A) := by
    rw [Category.id_comp]; exact hbase.symm
  let ψ' : SchemeHomOver (𝟙 _ ≫ specMap (R p) (ResidueField ↥A)) tA := ⟨resPt A, hψ'⟩
  have hpc : postComp ⟨pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩
      (BaseChange.overR (ResidueField ↥A) y) = postComp s ψ' := Subtype.ext hy
  have hΘx : Θ ≫ pullback.snd c tκ = pullback.snd x (𝟙 _) ≫ 𝟙 _ := pullback.condition
  have hΞ : (BaseChange.κ c (ResidueField ↥A) (𝟙 _)).hom ≫ baseChangeSnd c ψ' = Θ ≫ B := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_fst', BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst]
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_snd', BaseChange.baseChangeSnd_snd', ← Category.assoc,
        BaseChange.κ_hom_snd, ← Category.assoc, hΘx, Category.comp_id]
  refine ⟨(Scheme.Modules.pullback (baseChangeSnd _ y)).mapIso eP ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (BaseChange.baseChangeSnd_κ_hom c (ResidueField ↥A) y)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso
      ((Scheme.Modules.pullbackComp _ _).app _ ≪≫
        (Scheme.Modules.pullbackCongr ((baseChangeSnd_comp c _ _).trans
          ((congrArg (baseChangeSnd c) hpc).trans (baseChangeSnd_comp c s ψ').symm))).app _ ≪≫
        ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso hs.some) ≪≫
    (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hΞ).app _ ≪≫ br⟩

end S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_sameComponent
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_sameComponent (solution)
