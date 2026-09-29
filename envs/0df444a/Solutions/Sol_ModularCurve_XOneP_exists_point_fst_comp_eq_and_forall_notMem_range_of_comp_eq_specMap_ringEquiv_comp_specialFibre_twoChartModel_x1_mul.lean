-- Prove2me | solution 1 for ModularCurve.XOneP.exists_point_fst_comp_eq_and_forall_notMem_range_of_comp_eq_specMap_ringEquiv_comp_specialFibre_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b75baf99-b3d9-54af-8f29-78a807c2c439

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_ModularCurve_XOneP_eq_of_forall_specializes_imp_eq_of_ringEquiv_stalk_of_fst_eq_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_component_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_ringEquiv_stalk_apply_germ_eq_of_ringKrullDim_le_one_twoChartIntegralModel_x1_mul
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_point_fst_comp_eq_and_forall_notMem_range_of_comp_eq_specMap_ringEquiv_comp_specialFibre_twoChartModel_x1_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply"
p2m_attr_erase "simp" "CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun"
p2m_attr_erase "simp" "KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some"
p2m_attr_erase "simp" "FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve

namespace FrobTwist

universe u

section twist

variable {X T S : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (σ : T ≅ T) (hσ : σ.hom ≫ g = g)

include hσ in
private theorem _root_.FrobTwist.inv_comp_eq : σ.inv ≫ g = g := by
  rw [← hσ, σ.inv_hom_id_assoc, hσ]

p2m_export "FrobTwist" "inv_comp_eq"

noncomputable def twistHom : pullback f g ⟶ pullback f g :=
  pullback.map f g f g (𝟙 X) σ.hom (𝟙 S) (by simp) (by rw [Category.comp_id, hσ])

noncomputable def twistInv : pullback f g ⟶ pullback f g :=
  pullback.map f g f g (𝟙 X) σ.inv (𝟙 S) (by simp) (by rw [Category.comp_id, inv_comp_eq g σ hσ])

@[reassoc (attr := simp)]
theorem twistHom_fst : twistHom f g σ hσ ≫ pullback.fst f g = pullback.fst f g := by
  rw [twistHom, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
theorem twistHom_snd : twistHom f g σ hσ ≫ pullback.snd f g = pullback.snd f g ≫ σ.hom := by
  rw [twistHom, pullback.map, pullback.lift_snd]

@[reassoc (attr := simp)]
theorem twistInv_fst : twistInv f g σ hσ ≫ pullback.fst f g = pullback.fst f g := by
  rw [twistInv, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
theorem twistInv_snd : twistInv f g σ hσ ≫ pullback.snd f g = pullback.snd f g ≫ σ.inv := by
  rw [twistInv, pullback.map, pullback.lift_snd]

noncomputable def twist : pullback f g ≅ pullback f g where
  hom := twistHom f g σ hσ
  inv := twistInv f g σ hσ
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, twistInv_fst, twistHom_fst, Category.id_comp]
    · rw [Category.assoc, twistInv_snd, twistHom_snd_assoc, σ.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, twistHom_fst, twistInv_fst, Category.id_comp]
    · rw [Category.assoc, twistHom_snd, twistInv_snd_assoc, σ.inv_hom_id, Category.comp_id, Category.id_comp]

@[reassoc (attr := simp)]
theorem twist_hom_fst : (twist f g σ hσ).hom ≫ pullback.fst f g = pullback.fst f g := twistHom_fst f g σ hσ

@[reassoc (attr := simp)]
theorem twist_hom_snd : (twist f g σ hσ).hom ≫ pullback.snd f g = pullback.snd f g ≫ σ.hom :=
  twistHom_snd f g σ hσ

@[reassoc (attr := simp)]
theorem twist_inv_fst : (twist f g σ hσ).inv ≫ pullback.fst f g = pullback.fst f g := twistInv_fst f g σ hσ

@[reassoc (attr := simp)]
theorem twist_inv_snd : (twist f g σ hσ).inv ≫ pullback.snd f g = pullback.snd f g ≫ σ.inv :=
  twistInv_snd f g σ hσ

theorem comp_twist_hom_eq {P P' : T ⟶ pullback f g} (hP : P ≫ pullback.snd f g = 𝟙 T)
    (hP' : P' ≫ pullback.snd f g = 𝟙 T) (h : P' ≫ pullback.fst f g = σ.hom ≫ P ≫ pullback.fst f g) :
    P' ≫ (twist f g σ hσ).hom = σ.hom ≫ P := by
  apply pullback.hom_ext
  · rw [Category.assoc, twist_hom_fst, h, Category.assoc]
  · rw [Category.assoc, twist_hom_snd, reassoc_of% hP', Category.assoc, hP, Category.comp_id]

theorem twist_hom_base_apply_eq {P P' : T ⟶ pullback f g} (hP : P ≫ pullback.snd f g = 𝟙 T)
    (hP' : P' ≫ pullback.snd f g = 𝟙 T) (h : P' ≫ pullback.fst f g = σ.hom ≫ P ≫ pullback.fst f g)
    (t : ↥T) (ht : σ.hom.base t = t) :
    (twist f g σ hσ).hom.base (P'.base t) = P.base t := by
  have := congrArg (fun φ => φ.base t) (comp_twist_hom_eq f g σ hσ hP hP' h)
  simpa [ht] using this

end twist

section liftThrough

variable {C Y : Scheme.{u}} (i : C ⟶ Y) [IsClosedImmersion i] (i' : C ⟶ Y) [IsReduced C]
  (hrange : Set.range i'.base ⊆ Set.range i.base)

omit [IsClosedImmersion i] [IsReduced C] in
include hrange in
theorem surjective_snd_base : Function.Surjective (pullback.snd i i').base := by
  intro c
  obtain ⟨b, hb⟩ := hrange ⟨c, rfl⟩
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback b c hb
  exact ⟨z, hz⟩

include hrange in
theorem isIso_snd : IsIso (pullback.snd i i') := by
  haveI : Surjective (pullback.snd i i') := ⟨surjective_snd_base i i' hrange⟩
  exact isIso_of_isClosedImmersion_of_surjective _

noncomputable def liftThrough : C ⟶ C :=
  haveI := isIso_snd i i' hrange
  inv (pullback.snd i i') ≫ pullback.fst i i'

@[reassoc (attr := simp)]
theorem liftThrough_comp : liftThrough i i' hrange ≫ i = i' := by
  haveI := isIso_snd i i' hrange
  rw [liftThrough, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

end liftThrough

section liftAut

variable {C Y : Scheme.{u}} (i : C ⟶ Y) [IsClosedImmersion i] [IsReduced C] (τ : Y ≅ Y)
  (hτ : τ.hom.base '' Set.range i.base ⊆ Set.range i.base)
  (hτ' : τ.inv.base '' Set.range i.base ⊆ Set.range i.base)

omit [IsClosedImmersion i] [IsReduced C] in
include hτ in
theorem range_comp_hom_subset : Set.range (i ≫ τ.hom).base ⊆ Set.range i.base := by
  rintro _ ⟨c, rfl⟩
  exact hτ ⟨i.base c, ⟨c, rfl⟩, by simp⟩

omit [IsClosedImmersion i] [IsReduced C] in
include hτ' in
theorem range_comp_inv_subset : Set.range (i ≫ τ.inv).base ⊆ Set.range i.base := by
  rintro _ ⟨c, rfl⟩
  exact hτ' ⟨i.base c, ⟨c, rfl⟩, by simp⟩

noncomputable def liftAut : C ≅ C where
  hom := liftThrough i (i ≫ τ.hom) (range_comp_hom_subset i τ hτ)
  inv := liftThrough i (i ≫ τ.inv) (range_comp_inv_subset i τ hτ')
  hom_inv_id := by
    rw [← cancel_mono i, Category.assoc, liftThrough_comp, liftThrough_comp_assoc, Category.assoc,
      τ.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono i, Category.assoc, liftThrough_comp, liftThrough_comp_assoc, Category.assoc,
      τ.inv_hom_id, Category.comp_id, Category.id_comp]

@[reassoc (attr := simp)]
theorem liftAut_hom_comp : (liftAut i τ hτ hτ').hom ≫ i = i ≫ τ.hom :=
  liftThrough_comp i (i ≫ τ.hom) (range_comp_hom_subset i τ hτ)

@[reassoc (attr := simp)]
theorem liftAut_inv_comp : (liftAut i τ hτ hτ').inv ≫ i = i ≫ τ.inv :=
  liftThrough_comp i (i ≫ τ.inv) (range_comp_inv_subset i τ hτ')

end liftAut

section generic

variable {C Y : Scheme.{u}} (i : C ⟶ Y) [IsClosedImmersion i]

theorem range_eq_closure_singleton (ξ : ↥C) (hξ : IsGenericPoint ξ ⊤) :
    Set.range i.base = closure {i.base ξ} := by
  apply le_antisymm
  · calc Set.range i.base = i.base '' Set.univ := Set.image_univ.symm
      _ = i.base '' closure {ξ} := by rw [hξ.def, Set.top_eq_univ]
      _ ⊆ closure (i.base '' {ξ}) := image_closure_subset_closure_image i.base.hom.continuous
      _ = closure {i.base ξ} := by rw [Set.image_singleton]
  · exact i.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨ξ, rfl⟩)

theorem image_range_subset_of_apply_eq (ξ : ↥C) (hξ : IsGenericPoint ξ ⊤) (τ : Y ⟶ Y)
    (hfix : τ.base (i.base ξ) = i.base ξ) : τ.base '' Set.range i.base ⊆ Set.range i.base := by
  rw [range_eq_closure_singleton i ξ hξ]
  calc τ.base '' closure {i.base ξ} ⊆ closure (τ.base '' {i.base ξ}) :=
        image_closure_subset_closure_image τ.base.hom.continuous
    _ = closure {i.base ξ} := by rw [Set.image_singleton, hfix]
    _ ⊆ closure {i.base ξ} := le_rfl

end generic

end FrobTwist

namespace FrobFix

theorem surjective_fst_of_range_subset {Y C₁ C₂ : Scheme.{0}} (i₁ : C₁ ⟶ Y) (i₂ : C₂ ⟶ Y)
    (h : Set.range i₁.base ⊆ Set.range i₂.base) : Function.Surjective (pullback.fst i₁ i₂).base := by
  intro a
  obtain ⟨b, hb⟩ := h ⟨a, rfl⟩
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback a b hb.symm
  exact ⟨z, hz⟩

theorem eq_of_specializes_of_isGenericPoint {Y C₁ C₂ : Scheme.{0}} (i₁ : C₁ ⟶ Y) (i₂ : C₂ ⟶ Y)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IrreducibleSpace ↥C₁] [IrreducibleSpace ↥C₂] [Infinite ↥C₁]
    (hcover : ∀ z : ↥Y, z ∈ Set.range i₁.base ∨ z ∈ Set.range i₂.base) (hfin : Finite ↥(pullback i₁ i₂))
    (ξ₁ : ↥C₁) (hξ₁ : IsGenericPoint ξ₁ ⊤) (y : ↥Y) (hy : y ⤳ i₁.base ξ₁) : y = i₁.base ξ₁ := by
  rcases hcover y with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · have h1 : i₁.base ξ₁ ⤳ i₁.base a := (hξ₁.specializes (Set.mem_univ a)).map i₁.base.hom.continuous
    exact ((hy.antisymm h1).eq)
  · exfalso
    have hcl : IsClosed (Set.range i₂.base) := i₂.isClosedEmbedding.isClosed_range
    have hmem : i₁.base ξ₁ ∈ Set.range i₂.base :=
      hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨b, rfl⟩) (specializes_iff_mem_closure.mp hy)
    have hsub : Set.range i₁.base ⊆ Set.range i₂.base := by
      calc Set.range i₁.base = i₁.base '' Set.univ := Set.image_univ.symm
        _ = i₁.base '' closure {ξ₁} := by rw [hξ₁.def, Set.top_eq_univ]
        _ ⊆ closure (i₁.base '' {ξ₁}) := image_closure_subset_closure_image i₁.base.hom.continuous
        _ = closure {i₁.base ξ₁} := by rw [Set.image_singleton]
        _ ⊆ Set.range i₂.base := hcl.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)
    haveI : Infinite ↥(pullback i₁ i₂) := Infinite.of_surjective _ (surjective_fst_of_range_subset i₁ i₂ hsub)
    exact (not_finite ↥(pullback i₁ i₂)).elim

theorem isIntegral_of_geometricallyIntegral {k : Type} [Field k] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] : IsIntegral C := by
  haveI : IsIntegral (pullback c (Spec.map (CommRingCat.ofHom (algebraMap k k)))) :=
    SmoothProperCurve.isIntegral_pullback_Spec_field k c (Spec.map (CommRingCat.ofHom (algebraMap k k)))
  have hid : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _ := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]; exact Spec.map_id _
  haveI : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by rw [hid]; infer_instance
  exact IsIntegral.of_isIso (pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap k k))))

theorem infinite_of_smooth {k : Type} [Field k] [IsAlgClosed k] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] : Infinite ↥C :=
  Set.infinite_univ_iff.mp ((AlgebraicCurve.infinite_setOf_isClosed_singleton c).mono (Set.subset_univ _))

theorem forall_specializes_imp_eq_of_isIso {Y : Scheme.{0}} (τ : Y ⟶ Y) [IsIso τ] (y : ↥Y)
    (hmin : ∀ t, t ⤳ y → t = y) : ∀ t, t ⤳ τ.base y → t = τ.base y := by
  intro t ht
  have h1 : (inv τ).base t ⤳ (inv τ).base (τ.base y) := ht.map (inv τ).base.hom.continuous
  have h2 : (inv τ).base (τ.base y) = y := by
    change (τ ≫ inv τ).base y = y
    rw [IsIso.hom_inv_id]
    rfl
  rw [h2] at h1
  have h3 := hmin _ h1
  calc t = (inv τ ≫ τ).base t := by rw [IsIso.inv_hom_id]; rfl
    _ = τ.base ((inv τ).base t) := rfl
    _ = τ.base y := by rw [h3]

theorem base_apply_eq_of_comp_fst_eq
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (τ : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶
      pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) [IsIso τ]
    (hτ : τ ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) :
    ∀ (ξ₁ : ↥C₁), IsGenericPoint ξ₁ ⊤ → τ.base (i₁.1.base ξ₁) = i₁.1.base ξ₁ := by
  intro ξ₁ hξ₁
  classical
  haveI : IsIntegral C₁ := isIntegral_of_geometricallyIntegral c₁
  haveI : IsIntegral C₂ := isIntegral_of_geometricallyIntegral c₂
  haveI : Infinite ↥C₁ := infinite_of_smooth c₁
  haveI hfin : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by rw [hn]; exact hn0.ne')

  have hmin : ∀ t, t ⤳ i₁.1.base ξ₁ → t = i₁.1.base ξ₁ := fun t ht =>
    eq_of_specializes_of_isGenericPoint i₁.1 i₂.1 hcover hfin ξ₁ hξ₁ t ht
  have hmin' := forall_specializes_imp_eq_of_isIso τ (i₁.1.base ξ₁) hmin

  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
  obtain ⟨hgerm, hdim⟩ :=
    ModularCurve.XOneP.germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_component_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ c₁ i₁ ϖ hϖ ξ₁ hξ₁
  obtain ⟨V, e, hzFin, hVA, hVm, hVj, -, -, hchart⟩ :=
    ModularCurve.XOneP.exists_valuationSubring_ringEquiv_stalk_apply_germ_eq_of_ringKrullDim_le_one_twoChartIntegralModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj ϖ hϖ _ _ rfl hgerm hdim

  have hfst : (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (i₁.1.base ξ₁) =
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (τ.base (i₁.1.base ξ₁)) := by
    change _ = (τ ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (i₁.1.base ξ₁)
    rw [hτ]
  exact (ModularCurve.XOneP.eq_of_forall_specializes_imp_eq_of_ringEquiv_stalk_of_fst_eq_twoChartModel_x1_mul
    p M hM hpM L ζ hζ K hK A hAp hζA j hj k _ _ hmin hmin' V hVA hVm hVj hzFin e hchart hfst).symm

theorem image_range_subset
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (τ : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶
      pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) [IsIso τ]
    (hτ : τ ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) :
    τ.base '' Set.range i₁.1.base ⊆ Set.range i₁.1.base := by
  haveI : IsIntegral C₁ := isIntegral_of_geometricallyIntegral c₁
  exact FrobTwist.image_range_subset_of_apply_eq i₁.1 (genericPoint C₁) (genericPoint_spec C₁) τ
    (base_apply_eq_of_comp_fst_eq p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 τ hτ
      (genericPoint C₁) (genericPoint_spec C₁))

theorem range_comp_subset
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (τ : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶
      pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) [IsIso τ]
    (hτ : τ ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) :
    Set.range (i₁.1 ≫ τ).base ⊆ Set.range i₁.1.base := by
  rintro _ ⟨c, rfl⟩
  exact image_range_subset p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 τ hτ
    ⟨i₁.1.base c, ⟨c, rfl⟩, rfl⟩

end FrobFix

namespace TPKit
universe u
theorem range_comp_base {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Set.range (f ≫ g).base = g.base '' Set.range f.base := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
end TPKit

set_option maxHeartbeats 6400000 in
open AlgebraicGeometry.RelPicard.BaseChange in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n) :
    ∀ (σk : k ≃+* k), (σk : k →+* k).comp (algebraMap A k) = algebraMap A k →
    ∀ (c : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (y : Spec (CommRingCat.of k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)),
      y ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = 𝟙 _ →
      y ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
        Spec.map (CommRingCat.ofHom (σk : k →+* k)) ≫ c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) →
      (∀ t, c.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) →
      ∃ c' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁,
        c'.1 ≫ i₁.1 = y ∧
        (∀ t, c'.1.base t ∉ Set.range (pullback.fst i₁.1 i₂.1).base) ∧
        (c'.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (IsLocalRing.closedPoint k) =
          (c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (IsLocalRing.closedPoint k) := by
  intro σk hσk c y hy₂ hy₁ hnode
  classical

  let φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (σk : k →+* k))
  haveI : IsIso (CommRingCat.ofHom (σk : k →+* k)) := σk.toCommRingCatIso.isIso_hom
  haveI hφiso : IsIso φ := inferInstance
  have hφ : φ ≫ specMap A k = specMap A k := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hσk]
  have hφinv : inv φ ≫ specMap A k = specMap A k := by rw [IsIso.inv_comp_eq, hφ]
  let ψ : SchemeHomOver (specMap A k) (specMap A k) := ⟨φ, hφ⟩
  let ψ' : SchemeHomOver (specMap A k) (specMap A k) := ⟨inv φ, hφinv⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k), τ = baseChangeSnd (ModularCurve.TwoChart.modelTo A (↥K) j) ψ := ⟨_, rfl⟩
  haveI hτiso : IsIso τ := by
    rw [hτdef]
    refine ⟨baseChangeSnd (ModularCurve.TwoChart.modelTo A (↥K) j) ψ', ?_, ?_⟩
    · rw [baseChangeSnd_comp]
      have : postComp ψ' ψ = ⟨𝟙 _, Category.id_comp _⟩ := Subtype.ext (IsIso.hom_inv_id φ)
      rw [this, baseChangeSnd_id]
    · rw [baseChangeSnd_comp]
      have : postComp ψ ψ' = ⟨𝟙 _, Category.id_comp _⟩ := Subtype.ext (IsIso.inv_hom_id φ)
      rw [this, baseChangeSnd_id]
  have hτ_fst : τ ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) := by
    rw [hτdef, baseChangeSnd_fst']
  have hτ_snd : τ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ φ := by
    rw [hτdef, baseChangeSnd_snd']
  have hτ'_fst : inv τ ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) := by
    rw [IsIso.inv_comp_eq, hτ_fst]
  have hτ'_snd : inv τ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ inv φ := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, hτ_snd, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

  let z : Spec (CommRingCat.of k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) := c.1 ≫ i₁.1
  have hz_snd : z ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = 𝟙 _ := by
    show (c.1 ≫ i₁.1) ≫ baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k = 𝟙 _
    rw [Category.assoc, i₁.2, c.2]
  have hy : y = φ ≫ z ≫ inv τ := by
    apply pullback.hom_ext
    · rw [hy₁]; simp only [z, Category.assoc, hτ'_fst]; rfl
    · rw [hy₂]; simp only [Category.assoc, hτ'_snd, reassoc_of% hz_snd, IsIso.hom_inv_id]

  have hcover' : ∀ t : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), t ∈ Set.range i₂.1.base ∨ t ∈ Set.range i₁.1.base := fun t => (hcover t).symm
  have hred' : IsReduced (pullback i₂.1 i₁.1) := isReduced_of_isOpenImmersion (pullbackSymmetry i₂.1 i₁.1).hom
  have hn' : Nat.card ↥(pullback i₂.1 i₁.1) = n := by
    rw [Nat.card_congr (Scheme.homeoOfIso (pullbackSymmetry i₂.1 i₁.1)).toEquiv]; exact hn
  have L2₁' := FrobFix.range_comp_subset p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 (inv τ) hτ'_fst
  have L2₂ := FrobFix.image_range_subset p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₂ C₁ c₂ c₁ i₂ i₁ hcover' hred' n hn' hn0 τ hτ_fst

  have hyrange : Set.range y.base ⊆ Set.range i₁.1.base := by
    rw [hy, show φ ≫ z ≫ inv τ = (φ ≫ c.1) ≫ (i₁.1 ≫ inv τ) by simp only [z, Category.assoc], TPKit.range_comp_base]
    exact (Set.image_subset_range _ _).trans L2₁'
  obtain ⟨c'₁, hc', -⟩ := AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_range_subset_of_isReduced i₁.1 y hyrange
  have hc'₂ : c'₁ ≫ c₁ = 𝟙 _ := by
    rw [← i₁.2, ← Category.assoc, hc', hy₂]
  refine ⟨⟨c'₁, hc'₂⟩, hc', ?_, ?_⟩
  ·
    intro t ht
    rw [Scheme.Pullback.range_fst] at ht
    obtain ⟨w, hw⟩ := ht

    have hyt : y.base t = (inv τ).base (z.base (φ.base t)) := by
      rw [hy]; rfl
    have hzt : z.base (φ.base t) = τ.base (i₂.1.base w) := by
      rw [hw]
      show z.base (φ.base t) = τ.base ((c'₁ ≫ i₁.1).base t)
      rw [hc', hyt]
      show _ = (inv τ ≫ τ).base _
      rw [IsIso.inv_hom_id]; rfl
    have hmem : z.base (φ.base t) ∈ Set.range i₂.1.base := L2₂ ⟨i₂.1.base w, ⟨w, rfl⟩, hzt.symm⟩
    apply hnode (φ.base t)
    rw [Scheme.Pullback.range_fst]
    exact hmem
  ·
    show ((c'₁ ≫ i₁.1) ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (IsLocalRing.closedPoint k) = _
    rw [hc', hy₁]
    show (z ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (φ.base (IsLocalRing.closedPoint k)) =
      (z ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base (IsLocalRing.closedPoint k)
    rw [Subsingleton.elim (φ.base (IsLocalRing.closedPoint k)) (IsLocalRing.closedPoint k)]

end S_ModularCurve_XOneP_exists_point_fst_comp_eq_and_forall_notMem_range_of_comp_eq_specMap_ringEquiv_comp_specialFibre_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_point_fst_comp_eq_and_forall_notMem_range_of_comp_eq_specMap_ringEquiv_comp_specialFibre_twoChartModel_x1_mul (solution)
