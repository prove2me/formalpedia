-- Prove2me | solution 1 for ModularCurve.XOneP.isInvertible_comap_ker_and_comap_ker_eq_prod_ofPoint_of_map_maximalIdeal_eq_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c68c07e6-c0a7-585e-8d0f-5d1007c3c928

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
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_support_ker_eq_singleton_and_map_germ_ker_ideal_eq_maximalIdeal_of_field
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_eq_and_ext_and_support_dichotomy
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_map_germ_ker_ideal_eq_ker_stalkMap
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_vanishingIdeal_closure_eq_branchIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_stalkMap_map_germ_ideal_le_and_map_germ_ker_eq_bot
import Theorems.Thm_ModularCurve_XOneP_map_stalkMap_branchIdeal_eq_branchIdeal_specialFibre_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_mem_range_of_comp_baseChange_mem_closure_genericPoint_of_map_maximalIdeal_eq_twoChartModel_x1_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_ker_stalkMap_eq_branchIdeal_and_branchIdeal_sup_branchIdeal_eq_maximalIdeal_of_isReduced_pullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_ker_eq_vanishingIdeal_closure_singleton_genericPoint
import Theorems.Thm_ModularCurve_XOneP_isIntegral_subscheme_ker_and_ker_eq_vanishingIdeal_closure_and_ker_inf_ker_eq_ker_of_map_maximalIdeal_eq_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_genericPoint_specializes_crossing_and_baseChange_twoChartModel_x1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_isInvertible_comap_ker_and_comap_ker_eq_prod_ofPoint_of_map_maximalIdeal_eq_twoChartModel_x1_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "MvPolynomial CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

namespace CrossAsm

universe u

open IsLocalRing

theorem map_eq_maximalIdeal_of_ker_eq {B D : Type*} [CommRing B] [CommRing D] [IsLocalRing B] [IsLocalRing D]
    (φ : B →+* D) (hφ : Function.Surjective φ) {P Q : Ideal B} (hker : RingHom.ker φ = Q)
    (hsum : P ⊔ Q = maximalIdeal B) : Ideal.map φ P = maximalIdeal D := by
  have hQ : Ideal.map φ Q = ⊥ := by
    rw [← hker, Ideal.map_eq_bot_iff_le_ker]
  calc Ideal.map φ P = Ideal.map φ P ⊔ Ideal.map φ Q := by rw [hQ, sup_bot_eq]
    _ = Ideal.map φ (P ⊔ Q) := (Ideal.map_sup φ P Q).symm
    _ = maximalIdeal D := by rw [hsum, IsLocalRing.map_maximalIdeal_of_surjective φ hφ]

theorem maximalIdeal_le_map_germ_comap
    {XO Y D D' Xa : Scheme.{u}} (bc : Y ⟶ XO) (fstO : XO ⟶ Xa) (fstk : Y ⟶ Xa) (hfst : bc ≫ fstO = fstk)
    (iD : D ⟶ Y) [IsClosedImmersion iD] (e : D' ⟶ D) [IsIso e]
    (I : XO.IdealSheafData) (IA : Xa.IdealSheafData) (hI : IA.comap fstO ≤ I)
    (c : D') (d : D) (hc : e.base c = d) (y : Y) (hd : iD.base d = y)
    (UA : Xa.affineOpens) (hUA : fstk.base y ∈ (UA : Xa.Opens))
    (P : Ideal (Xa.presheaf.stalk (fstk.base y)))
    (hP : P ≤ Ideal.map (Xa.presheaf.germ (UA : Xa.Opens) (fstk.base y) hUA).hom (IA.ideal UA))
    (Qk : Ideal (Y.presheaf.stalk y))
    (hQk : (RingHom.ker (iD.stalkMap d).hom).comap (Y.presheaf.stalkSpecializes (specializes_of_eq hd)).hom = Qk)
    (hsum : Ideal.map (fstk.stalkMap y).hom P ⊔ Qk = maximalIdeal (Y.presheaf.stalk y))
    (U' : D'.affineOpens) (hU' : c ∈ (U' : D'.Opens)) :
    maximalIdeal (D'.presheaf.stalk c) ≤
      Ideal.map (D'.presheaf.germ (U' : D'.Opens) c hU').hom ((I.comap (e ≫ iD ≫ bc)).ideal U') := by
  obtain ⟨hchart, -, -⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.map_germ_ideal_eq_and_ext_and_support_dichotomy (X := D')
  obtain ⟨hcomap, -⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.map_stalkMap_map_germ_ideal_le_and_map_germ_ker_eq_bot.{u}
  subst hc hd hfst

  have hxUA : bc.base (iD.base (e.base c)) ∈ fstO ⁻¹ᵁ (UA : Xa.Opens) := hUA
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ :=
    XO.isBasis_affineOpens.exists_subset_of_mem_open hxUA (fstO ⁻¹ᵁ (UA : Xa.Opens)).isOpen
  have hcFV : c ∈ (e ≫ iD ≫ bc) ⁻¹ᵁ V := hxV
  obtain ⟨_, ⟨V', hV', rfl⟩, hcV', hV'le⟩ :=
    D'.isBasis_affineOpens.exists_subset_of_mem_open hcFV ((e ≫ iD ≫ bc) ⁻¹ᵁ V).isOpen
  rw [hchart (I.comap (e ≫ iD ≫ bc)) c U' ⟨V', hV'⟩ hU' hcV']

  have h1 := hcomap (e ≫ iD ≫ bc) I c ⟨V, hV⟩ hxV ⟨V', hV'⟩ hcV' hV'le
  have h2 : Ideal.map (fstO.stalkMap (bc.base (iD.base (e.base c)))).hom
        (Ideal.map (Xa.presheaf.germ (UA : Xa.Opens) _ hUA).hom (IA.ideal UA)) ≤
      Ideal.map (XO.presheaf.germ V _ hxV).hom (I.ideal ⟨V, hV⟩) := by
    refine (hcomap fstO IA _ UA hUA ⟨V, hV⟩ hxV hVle).trans ?_
    exact Ideal.map_mono (Scheme.IdealSheafData.le_def.mp hI _)

  have hQk' : RingHom.ker (iD.stalkMap (e.base c)).hom = Qk := by
    rw [← hQk]
    have : Y.presheaf.stalkSpecializes (specializes_of_eq (rfl : iD.base (e.base c) = iD.base (e.base c))) = 𝟙 _ :=
      Y.presheaf.stalkSpecializes_refl _
    rw [this, CommRingCat.hom_id, Ideal.comap_id]

  have hsurjD : Function.Surjective (iD.stalkMap (e.base c)).hom := iD.stalkMap_surjective _
  have h3 : Ideal.map (iD.stalkMap (e.base c)).hom (Ideal.map ((bc ≫ fstO).stalkMap (iD.base (e.base c))).hom P) =
      maximalIdeal _ :=
    map_eq_maximalIdeal_of_ker_eq _ hsurjD hQk' hsum
  have hsurje : Function.Surjective (e.stalkMap c).hom := by
    haveI : IsIso (e.stalkMap c) := inferInstance
    exact (ConcreteCategory.bijective_of_isIso (e.stalkMap c)).2
  have h4 : Ideal.map (e.stalkMap c).hom (maximalIdeal _) = maximalIdeal (D'.presheaf.stalk c) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hsurje

  have eF : ((e ≫ iD ≫ bc).stalkMap c).hom =
      (e.stalkMap c).hom.comp ((iD.stalkMap (e.base c)).hom.comp (bc.stalkMap (iD.base (e.base c))).hom) := by
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp]; rfl
  have eG : ((bc ≫ fstO).stalkMap (iD.base (e.base c))).hom =
      (bc.stalkMap (iD.base (e.base c))).hom.comp (fstO.stalkMap (bc.base (iD.base (e.base c)))).hom := by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  calc maximalIdeal (D'.presheaf.stalk c)
      = Ideal.map (e.stalkMap c).hom (Ideal.map (iD.stalkMap (e.base c)).hom
          (Ideal.map ((bc ≫ fstO).stalkMap (iD.base (e.base c))).hom P)) := by rw [h3, h4]
    _ = Ideal.map (e.stalkMap c).hom (Ideal.map (iD.stalkMap (e.base c)).hom
          (Ideal.map (bc.stalkMap (iD.base (e.base c))).hom
            (Ideal.map (fstO.stalkMap (bc.base (iD.base (e.base c)))).hom P))) := by
        simp only [Ideal.map_map, eG]
        exact (Ideal.map_map (I := P) (fstO.stalkMap (bc.base (iD.base (e.base c)))).hom
          ((e.stalkMap c).hom.comp ((iD.stalkMap (e.base c)).hom.comp (bc.stalkMap (iD.base (e.base c))).hom))).symm
    _ ≤ Ideal.map (e.stalkMap c).hom (Ideal.map (iD.stalkMap (e.base c)).hom
          (Ideal.map (bc.stalkMap (iD.base (e.base c))).hom
            (Ideal.map (XO.presheaf.germ V _ hxV).hom (I.ideal ⟨V, hV⟩)))) :=
        Ideal.map_mono (Ideal.map_mono (Ideal.map_mono ((Ideal.map_mono hP).trans h2)))
    _ = Ideal.map ((e ≫ iD ≫ bc).stalkMap c).hom (Ideal.map (XO.presheaf.germ V _ hxV).hom (I.ideal ⟨V, hV⟩)) := by
        simp only [Ideal.map_map, eF]
        exact (Ideal.map_map (I := I.ideal ⟨V, hV⟩) (XO.presheaf.germ V (bc.base (iD.base (e.base c))) hxV).hom
          ((e.stalkMap c).hom.comp ((iD.stalkMap (e.base c)).hom.comp (bc.stalkMap (iD.base (e.base c))).hom))).symm
    _ ≤ _ := h1

theorem maximalIdeal_le_map_germ_comap'
    {XO Y D D' Xa : Scheme.{u}} (bc : Y ⟶ XO) (fstO : XO ⟶ Xa) (fstk : Y ⟶ Xa) (hfst : bc ≫ fstO = fstk)
    (iD : D ⟶ Y) [IsClosedImmersion iD] (e : D' ⟶ D) [IsIso e]
    (I : XO.IdealSheafData) (IA : Xa.IdealSheafData) (hI : IA.comap fstO ≤ I)
    (c : D') (d : D) (hc : e.base c = d)
    (UA : Xa.affineOpens) (hUA : fstk.base (iD.base d) ∈ (UA : Xa.Opens))
    (P : Ideal (Xa.presheaf.stalk (fstk.base (iD.base d))))
    (hP : P ≤ Ideal.map (Xa.presheaf.germ (UA : Xa.Opens) (fstk.base (iD.base d)) hUA).hom (IA.ideal UA))
    (Qk : Ideal (Y.presheaf.stalk (iD.base d)))
    (hQk : RingHom.ker (iD.stalkMap d).hom = Qk)
    (hsum : Ideal.map (fstk.stalkMap (iD.base d)).hom P ⊔ Qk = maximalIdeal (Y.presheaf.stalk (iD.base d)))
    (U' : D'.affineOpens) (hU' : c ∈ (U' : D'.Opens)) :
    maximalIdeal (D'.presheaf.stalk c) ≤
      Ideal.map (D'.presheaf.germ (U' : D'.Opens) c hU').hom ((I.comap (e ≫ iD ≫ bc)).ideal U') := by
  refine maximalIdeal_le_map_germ_comap bc fstO fstk hfst iD e I IA hI c d hc (iD.base d) rfl UA hUA P hP Qk ?_ hsum U' hU'
  rw [← hQk, TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, Ideal.comap_id]

theorem spec_of_comp {X Y Z W : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ W} {ξ : W} {ν : X}
    (h : ξ ⤳ (a ≫ b ≫ c).base ν) : ξ ⤳ c.base (b.base (a.base ν)) := h

theorem map_branchIdeal_spec_of_comp {X Y Z W : Scheme.{u}} {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ W} {ξ : W} {ν : X}
    (h : ξ ⤳ (a ≫ b ≫ c).base ν) {R : Type*} [Semiring R]
    (f : W.presheaf.stalk (c.base (b.base (a.base ν))) →+* R) :
    Ideal.map f (Scheme.branchIdeal (spec_of_comp h)) = Ideal.map f (Scheme.branchIdeal h) := rfl

theorem exists_eq_of_injective_of_card {P : Type*} {n : ℕ} (hn : Nat.card P = n) (hn0 : 0 < n)
    (w : Fin n → P) (hw : Function.Injective w) (ν : P) : ∃ i, w i = ν := by
  haveI : Finite P := Nat.finite_of_card_ne_zero (by omega)
  have hb : Function.Bijective w := hw.bijective_of_nat_card_le (by simp [hn])
  exact hb.2 ν

theorem ideal_finset_prod {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData) (U : X.affineOpens) :
    (∏ i ∈ s, I i).ideal U = ∏ i ∈ s, (I i).ideal U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Scheme.IdealSheafData.ideal_top, show (1 : X.IdealSheafData) = ⊤ from rfl, Ideal.one_eq_top]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, ih]

theorem map_germ_finset_prod {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (U : X.affineOpens) (x : X) (hx : x ∈ (U : X.Opens)) :
    Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom ((∏ i ∈ s, I i).ideal U) =
      ∏ i ∈ s, Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom ((I i).ideal U) := by
  rw [ideal_finset_prod]
  exact map_prod (Ideal.mapHom (X.presheaf.germ (U : X.Opens) x hx).hom) _ s

theorem isInvertible_finset_prod {X : Scheme.{u}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (hI : ∀ i ∈ s, (I i).IsInvertible) : (∏ i ∈ s, I i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Scheme.IdealSheafData.isInvertible_top (X := X)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (hI a (Finset.mem_insert_self a s)).mul (ih fun i hi => hI i (Finset.mem_insert_of_mem hi))

end CrossAsm

set_option maxHeartbeats 1600000 in
open IsLocalRing in

theorem CrossAsm.onσ₂
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
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ρO : A →+* O) (hunr : Ideal.map ρO (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal O)
    (toκ : O →+* k) (htoκ : toκ.comp ρO = algebraMap A k)
    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))

    (z : Fin n → (Spec (CommRingCat.of k) ⟶ pullback i₁.1 i₂.1))
    (hz₁ : ∀ i, (z i ≫ pullback.fst i₁.1 i₂.1) ≫ c₁ = 𝟙 _) (hz₂ : ∀ i, (z i ≫ pullback.snd i₁.1 i₂.1) ≫ c₂ = 𝟙 _)
    (hzinj : Function.Injective fun i => (z i).base (IsLocalRing.closedPoint k))
    [IsIntegral C₁] [IsIntegral C₂] (i : Fin n)
    (U : (pullback c₂ (𝟙 (Spec (CommRingCat.of k)))).affineOpens)
    (hx : (graphOver c₂ (z i ≫ pullback.snd i₁.1 i₂.1) (hz₂ i)).base (closedPoint k) ∈
      (U : (pullback c₂ (𝟙 (Spec (CommRingCat.of k)))).Opens)) :
    Ideal.map ((pullback c₂ (𝟙 (Spec (CommRingCat.of k)))).presheaf.germ (U : (pullback c₂ (𝟙 _)).Opens) _ hx).hom
      (((((i₁.1 ≫ bc).ker).comap (pullback.fst c₂ (𝟙 (Spec (CommRingCat.of k))) ≫ i₂.1 ≫ bc))).ideal U) =
    maximalIdeal _ := by
  classical
  haveI : IsReduced (pullback i₁.1 i₂.1) := hred
  haveI : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨-, -, hdich₂⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.map_germ_ideal_eq_and_ext_and_support_dichotomy
      (X := pullback c₂ (𝟙 (Spec (CommRingCat.of k))))
  obtain ⟨-, -, hvan₁, -, hrange₁, -, -, -, -, -, -⟩ :=
    ModularCurve.XOneP.isIntegral_subscheme_ker_and_ker_eq_vanishingIdeal_closure_and_ker_inf_ker_eq_ker_of_map_maximalIdeal_eq_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 O ρO hunr toκ htoκ bc hbc₁ hbc₂
  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
  have hIA₁ : ((i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).ker).comap
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))) ≤ (i₁.1 ≫ bc).ker := by
    rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker, Category.assoc, hbc₁]

  let fstk := pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)
  let fstO := pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))
  let C₂' := pullback c₂ (𝟙 (Spec (CommRingCat.of k)))
  let e₂ : C₂' ⟶ C₂ := pullback.fst c₂ (𝟙 (Spec (CommRingCat.of k)))
  let F₂ : C₂' ⟶ _ := e₂ ≫ i₂.1 ≫ bc
  let σ : Spec (CommRingCat.of k) ⟶ C₂' := graphOver c₂ (z i ≫ pullback.snd i₁.1 i₂.1) (hz₂ i)
  let pt : ↥(Spec (CommRingCat.of k)) := closedPoint k
  let ν : ↥(pullback i₁.1 i₂.1) := (z i).base pt
  have heσ : e₂.base (σ.base pt) = (pullback.snd i₁.1 i₂.1).base ν := by
    show (σ ≫ e₂).base pt = (z i ≫ pullback.snd i₁.1 i₂.1).base pt
    rw [graphOver_fst]
  apply le_antisymm
  · refine (hdich₂ _ U _ hx).2 ?_
    rw [Scheme.IdealSheafData.support_comap]
    show F₂.base (σ.base pt) ∈ (((i₁.1 ≫ bc).ker).support : Set _)
    rw [hvan₁, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    show F₂.base (σ.base pt) ∈ closure {(i₁.1 ≫ bc).base (genericPoint ↥C₁)}
    rw [← hrange₁]
    refine ⟨(pullback.fst i₁.1 i₂.1).base ν, ?_⟩
    show (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ((z i).base pt) = (σ ≫ e₂ ≫ i₂.1 ≫ bc).base pt
    rw [pullback.condition_assoc, ← Category.assoc σ, graphOver_fst]
    rfl
  ·
    obtain ⟨h₁, h₂, -, -⟩ := ModularCurve.XOneP.genericPoint_specializes_crossing_and_baseChange_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 O ρO ϖ hϖ toκ htoκ bc hbc₁ hbc₂ ν
    have hy₂ : i₂.1.base ((pullback.snd i₁.1 i₂.1).base ν) = i₁.1.base ((pullback.fst i₁.1 i₂.1).base ν) := by
      show (pullback.snd _ _ ≫ i₂.1).base _ = (pullback.fst _ _ ≫ i₁.1).base _
      rw [pullback.condition]
    have hk₁ : i₁.1.base (genericPoint ↥C₁) ⤳ i₁.1.base ((pullback.fst i₁.1 i₂.1).base ν) :=
      (genericPoint_specializes _).map i₁.1.continuous
    have hk₂ : i₂.1.base (genericPoint ↥C₂) ⤳ i₁.1.base ((pullback.fst i₁.1 i₂.1).base ν) :=
      ((genericPoint_specializes _).map i₂.1.continuous).trans (specializes_of_eq hy₂)
    obtain ⟨-, hker₂, hsumk⟩ := AlgebraicGeometry.Scheme.ker_stalkMap_eq_branchIdeal_and_branchIdeal_sup_branchIdeal_eq_maximalIdeal_of_isReduced_pullback c₁ c₂ i₁.1 i₂.1 hcover ν hk₁ hy₂ hk₂
    obtain ⟨hbe₁, -⟩ := ModularCurve.XOneP.map_stalkMap_branchIdeal_eq_branchIdeal_specialFibre_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 ν h₁ h₂ hk₁ hy₂ hk₂
    obtain ⟨_, ⟨UA, hUA, rfl⟩, hxUA, -⟩ :=
      (ModularCurve.TwoChartModel A (↥K) j).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (fstk.base (i₁.1.base ((pullback.fst i₁.1 i₂.1).base ν)))) isOpen_univ
    have h₁' := CrossAsm.spec_of_comp h₁
    have hP : Scheme.branchIdeal h₁' ≤ Ideal.map ((ModularCurve.TwoChartModel A (↥K) j).presheaf.germ UA _ hxUA).hom
        (((i₁.1 ≫ fstk).ker).ideal ⟨UA, hUA⟩) := by
      rw [AlgebraicGeometry.Scheme.Hom.ker_eq_vanishingIdeal_closure_singleton_genericPoint (i₁.1 ≫ fstk)]
      exact (AlgebraicGeometry.Scheme.IdealSheafData.map_germ_vanishingIdeal_closure_eq_branchIdeal h₁' ⟨UA, hUA⟩ hxUA).ge
    have hbe₁' := (CrossAsm.map_branchIdeal_spec_of_comp h₁ _).trans hbe₁
    have hsum' : Ideal.map (fstk.stalkMap (i₁.1.base ((pullback.fst i₁.1 i₂.1).base ν))).hom (Scheme.branchIdeal h₁') ⊔
        Scheme.branchIdeal hk₂ = maximalIdeal _ := by
      rw [hbe₁']; exact hsumk
    exact CrossAsm.maximalIdeal_le_map_germ_comap (XO := pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
      (Y := pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) (D := C₂) (D' := C₂')
      (Xa := ModularCurve.TwoChartModel A (↥K) j)
      bc fstO fstk hbc₁ i₂.1 e₂ ((i₁.1 ≫ bc).ker) ((i₁.1 ≫ fstk).ker) hIA₁ (σ.base pt)
      ((pullback.snd i₁.1 i₂.1).base ν) heσ (i₁.1.base ((pullback.fst i₁.1 i₂.1).base ν)) hy₂ ⟨UA, hUA⟩ hxUA
      (Scheme.branchIdeal h₁') hP (Scheme.branchIdeal hk₂) hker₂ hsum' U hx

set_option maxHeartbeats 1600000 in
open IsLocalRing in

theorem CrossAsm.onσ₁
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
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ρO : A →+* O) (hunr : Ideal.map ρO (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal O)
    (toκ : O →+* k) (htoκ : toκ.comp ρO = algebraMap A k)
    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))

    (z : Fin n → (Spec (CommRingCat.of k) ⟶ pullback i₁.1 i₂.1))
    (hz₁ : ∀ i, (z i ≫ pullback.fst i₁.1 i₂.1) ≫ c₁ = 𝟙 _) (hz₂ : ∀ i, (z i ≫ pullback.snd i₁.1 i₂.1) ≫ c₂ = 𝟙 _)
    (hzinj : Function.Injective fun i => (z i).base (IsLocalRing.closedPoint k))
    [IsIntegral C₁] [IsIntegral C₂] (i : Fin n)
    (U : (pullback c₁ (𝟙 (Spec (CommRingCat.of k)))).affineOpens)
    (hx : (graphOver c₁ (z i ≫ pullback.fst i₁.1 i₂.1) (hz₁ i)).base (closedPoint k) ∈
      (U : (pullback c₁ (𝟙 (Spec (CommRingCat.of k)))).Opens)) :
    Ideal.map ((pullback c₁ (𝟙 (Spec (CommRingCat.of k)))).presheaf.germ (U : (pullback c₁ (𝟙 _)).Opens) _ hx).hom
      (((((i₂.1 ≫ bc).ker).comap (pullback.fst c₁ (𝟙 (Spec (CommRingCat.of k))) ≫ i₁.1 ≫ bc))).ideal U) =
    maximalIdeal _ := by
  classical
  haveI : IsReduced (pullback i₁.1 i₂.1) := hred
  haveI : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨-, -, hdich₁⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.map_germ_ideal_eq_and_ext_and_support_dichotomy
      (X := pullback c₁ (𝟙 (Spec (CommRingCat.of k))))
  obtain ⟨-, -, -, hvan₂, -, hrange₂, -, -, -, -, -⟩ :=
    ModularCurve.XOneP.isIntegral_subscheme_ker_and_ker_eq_vanishingIdeal_closure_and_ker_inf_ker_eq_ker_of_map_maximalIdeal_eq_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 O ρO hunr toκ htoκ bc hbc₁ hbc₂
  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
  have hIA₂ : ((i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).ker).comap
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))) ≤ (i₂.1 ≫ bc).ker := by
    rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker, Category.assoc, hbc₁]

  let fstk := pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)
  let fstO := pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))
  let C₁' := pullback c₁ (𝟙 (Spec (CommRingCat.of k)))
  let e₁ : C₁' ⟶ C₁ := pullback.fst c₁ (𝟙 (Spec (CommRingCat.of k)))
  let F₁ : C₁' ⟶ _ := e₁ ≫ i₁.1 ≫ bc
  let σ : Spec (CommRingCat.of k) ⟶ C₁' := graphOver c₁ (z i ≫ pullback.fst i₁.1 i₂.1) (hz₁ i)
  let pt : ↥(Spec (CommRingCat.of k)) := closedPoint k
  let ν : ↥(pullback i₁.1 i₂.1) := (z i).base pt
  have heσ : e₁.base (σ.base pt) = (pullback.fst i₁.1 i₂.1).base ν := by
    show (σ ≫ e₁).base pt = (z i ≫ pullback.fst i₁.1 i₂.1).base pt
    rw [graphOver_fst]
  apply le_antisymm
  · refine (hdich₁ _ U _ hx).2 ?_
    rw [Scheme.IdealSheafData.support_comap]
    show F₁.base (σ.base pt) ∈ (((i₂.1 ≫ bc).ker).support : Set _)
    rw [hvan₂, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    show F₁.base (σ.base pt) ∈ closure {(i₂.1 ≫ bc).base (genericPoint ↥C₂)}
    rw [← hrange₂]
    refine ⟨(pullback.snd i₁.1 i₂.1).base ν, ?_⟩
    show (pullback.snd i₁.1 i₂.1 ≫ i₂.1 ≫ bc).base ((z i).base pt) = (σ ≫ e₁ ≫ i₁.1 ≫ bc).base pt
    rw [← pullback.condition_assoc, ← Category.assoc σ, graphOver_fst]
    rfl
  ·
    obtain ⟨h₁, h₂, -, -⟩ := ModularCurve.XOneP.genericPoint_specializes_crossing_and_baseChange_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 O ρO ϖ hϖ toκ htoκ bc hbc₁ hbc₂ ν
    have hy₂ : i₂.1.base ((pullback.snd i₁.1 i₂.1).base ν) = i₁.1.base ((pullback.fst i₁.1 i₂.1).base ν) := by
      show (pullback.snd _ _ ≫ i₂.1).base _ = (pullback.fst _ _ ≫ i₁.1).base _
      rw [pullback.condition]
    have hk₁ : i₁.1.base (genericPoint ↥C₁) ⤳ i₁.1.base ((pullback.fst i₁.1 i₂.1).base ν) :=
      (genericPoint_specializes _).map i₁.1.continuous
    have hk₂ : i₂.1.base (genericPoint ↥C₂) ⤳ i₁.1.base ((pullback.fst i₁.1 i₂.1).base ν) :=
      ((genericPoint_specializes _).map i₂.1.continuous).trans (specializes_of_eq hy₂)
    obtain ⟨hker₁, -, hsumk⟩ := AlgebraicGeometry.Scheme.ker_stalkMap_eq_branchIdeal_and_branchIdeal_sup_branchIdeal_eq_maximalIdeal_of_isReduced_pullback c₁ c₂ i₁.1 i₂.1 hcover ν hk₁ hy₂ hk₂
    obtain ⟨-, hbe₂⟩ := ModularCurve.XOneP.map_stalkMap_branchIdeal_eq_branchIdeal_specialFibre_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 ν h₁ h₂ hk₁ hy₂ hk₂
    obtain ⟨_, ⟨UA, hUA, rfl⟩, hxUA, -⟩ :=
      (ModularCurve.TwoChartModel A (↥K) j).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (fstk.base (i₁.1.base ((pullback.fst i₁.1 i₂.1).base ν)))) isOpen_univ
    have h₂' := CrossAsm.spec_of_comp h₂
    have hP : Scheme.branchIdeal h₂' ≤ Ideal.map ((ModularCurve.TwoChartModel A (↥K) j).presheaf.germ UA _ hxUA).hom
        (((i₂.1 ≫ fstk).ker).ideal ⟨UA, hUA⟩) := by
      rw [AlgebraicGeometry.Scheme.Hom.ker_eq_vanishingIdeal_closure_singleton_genericPoint (i₂.1 ≫ fstk)]
      exact (AlgebraicGeometry.Scheme.IdealSheafData.map_germ_vanishingIdeal_closure_eq_branchIdeal h₂' ⟨UA, hUA⟩ hxUA).ge
    have hbe₂' := (CrossAsm.map_branchIdeal_spec_of_comp h₂ _).trans hbe₂
    have hsum' : Ideal.map (fstk.stalkMap (i₁.1.base ((pullback.fst i₁.1 i₂.1).base ν))).hom (Scheme.branchIdeal h₂') ⊔
        Scheme.branchIdeal hk₁ = maximalIdeal _ := by
      rw [hbe₂', sup_comm]; exact hsumk
    exact CrossAsm.maximalIdeal_le_map_germ_comap' (XO := pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
      (Y := pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) (D := C₁) (D' := C₁')
      (Xa := ModularCurve.TwoChartModel A (↥K) j)
      bc fstO fstk hbc₁ i₁.1 e₁ ((i₂.1 ≫ bc).ker) ((i₂.1 ≫ fstk).ker) hIA₂ (σ.base pt)
      ((pullback.fst i₁.1 i₂.1).base ν) heσ ⟨UA, hUA⟩ hxUA
      (Scheme.branchIdeal h₂') hP (Scheme.branchIdeal hk₁) hker₁ hsum' U hx

open IsLocalRing in
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
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ρO : A →+* O) (hunr : Ideal.map ρO (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal O)
    (toκ : O →+* k) (htoκ : toκ.comp ρO = algebraMap A k)
    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))

    (z : Fin n → (Spec (CommRingCat.of k) ⟶ pullback i₁.1 i₂.1))
    (hz₁ : ∀ i, (z i ≫ pullback.fst i₁.1 i₂.1) ≫ c₁ = 𝟙 _) (hz₂ : ∀ i, (z i ≫ pullback.snd i₁.1 i₂.1) ≫ c₂ = 𝟙 _)
    (hzinj : Function.Injective fun i => (z i).base (IsLocalRing.closedPoint k))
    [IsIntegral C₁] [IsIntegral C₂] :
    (((i₁.1 ≫ bc).ker).comap (pullback.fst c₂ (𝟙 (Spec (CommRingCat.of k))) ≫ i₂.1 ≫ bc)).IsInvertible ∧
    ((i₁.1 ≫ bc).ker).comap (pullback.fst c₂ (𝟙 (Spec (CommRingCat.of k))) ≫ i₂.1 ≫ bc) =
      ∏ i : Fin n, (RelEffCartierDiv.ofPoint c₂ (z i ≫ pullback.snd i₁.1 i₂.1) (hz₂ i)).I ∧
    (((i₂.1 ≫ bc).ker).comap (pullback.fst c₁ (𝟙 (Spec (CommRingCat.of k))) ≫ i₁.1 ≫ bc)).IsInvertible ∧
    ((i₂.1 ≫ bc).ker).comap (pullback.fst c₁ (𝟙 (Spec (CommRingCat.of k))) ≫ i₁.1 ≫ bc) =
      ∏ i : Fin n, (RelEffCartierDiv.ofPoint c₁ (z i ≫ pullback.fst i₁.1 i₂.1) (hz₁ i)).I := by
  classical

  obtain ⟨-, hext₂, hdich₂⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.map_germ_ideal_eq_and_ext_and_support_dichotomy
      (X := pullback c₂ (𝟙 (Spec (CommRingCat.of k))))
  obtain ⟨-, hext₁, hdich₁⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.map_germ_ideal_eq_and_ext_and_support_dichotomy
      (X := pullback c₁ (𝟙 (Spec (CommRingCat.of k))))
  obtain ⟨-, -, hvan₁, hvan₂, hrange₁, hrange₂, hne₁₂, hne₂₁, -, -, -⟩ :=
    ModularCurve.XOneP.isIntegral_subscheme_ker_and_ker_eq_vanishingIdeal_closure_and_ker_inf_ker_eq_ker_of_map_maximalIdeal_eq_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 O ρO hunr toκ htoκ bc hbc₁ hbc₂
  obtain ⟨hoff₂, hoff₁⟩ :=
    ModularCurve.XOneP.mem_range_of_comp_baseChange_mem_closure_genericPoint_of_map_maximalIdeal_eq_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 O ρO hunr toκ htoκ bc hbc₁ hbc₂

  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr

  have hzsurj : ∀ ν : ↥(pullback i₁.1 i₂.1), ∃ i, (z i).base (closedPoint k) = ν :=
    CrossAsm.exists_eq_of_injective_of_card hn hn0 _ hzinj
  haveI : IsReduced (pullback i₁.1 i₂.1) := hred
  haveI : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by omega)

  have hIA₁ : ((i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).ker).comap
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))) ≤ (i₁.1 ≫ bc).ker := by
    rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker, Category.assoc, hbc₁]
  have hIA₂ : ((i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).ker).comap
      (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))) ≤ (i₂.1 ≫ bc).ker := by
    rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker, Category.assoc, hbc₁]

  have side₂ : ((i₁.1 ≫ bc).ker).comap (pullback.fst c₂ (𝟙 (Spec (CommRingCat.of k))) ≫ i₂.1 ≫ bc) =
      ∏ i : Fin n, (RelEffCartierDiv.ofPoint c₂ (z i ≫ pullback.snd i₁.1 i₂.1) (hz₂ i)).I := by

    let Y := pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)
    let fstk := pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)
    let fstO := pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))
    let C₂' := pullback c₂ (𝟙 (Spec (CommRingCat.of k)))
    let e₂ : C₂' ⟶ C₂ := pullback.fst c₂ (𝟙 (Spec (CommRingCat.of k)))
    let F₂ : C₂' ⟶ _ := e₂ ≫ i₂.1 ≫ bc
    let σ : Fin n → (Spec (CommRingCat.of k) ⟶ C₂') := fun i =>
      graphOver c₂ (z i ≫ pullback.snd i₁.1 i₂.1) (hz₂ i)
    let pt : ↥(Spec (CommRingCat.of k)) := closedPoint k
    let 𝔭 : Fin n → C₂'.IdealSheafData := fun i => (RelEffCartierDiv.ofPoint c₂ (z i ≫ pullback.snd i₁.1 i₂.1) (hz₂ i)).I
    have h𝔭 : ∀ i, 𝔭 i = (σ i).ker := fun i => RelEffCartierDiv.ofPoint_I _ _ _

    have heσ : ∀ i, e₂.base ((σ i).base pt) = (pullback.snd i₁.1 i₂.1).base ((z i).base pt) := by
      intro i
      show (σ i ≫ e₂).base pt = (z i ≫ pullback.snd i₁.1 i₂.1).base pt
      rw [graphOver_fst]
    have hσinj : Function.Injective fun i => (σ i).base pt := by
      intro i i' h
      apply hzinj
      have h' := congrArg e₂.base h
      simp only [heσ] at h'
      exact (pullback.snd i₁.1 i₂.1).isClosedEmbedding.injective h'

    have hsuppσ : ∀ i, ((𝔭 i).support : Set C₂') = {(σ i).base pt} := fun i => by
      rw [h𝔭]; exact (AlgebraicGeometry.Scheme.Hom.support_ker_eq_singleton_and_map_germ_ker_ideal_eq_maximalIdeal_of_field (σ i)).1
    have hgermσ : ∀ i (U : C₂'.affineOpens) (hx : (σ i).base pt ∈ (U : C₂'.Opens)),
        Ideal.map (C₂'.presheaf.germ (U : C₂'.Opens) ((σ i).base pt) hx).hom ((𝔭 i).ideal U) =
          maximalIdeal _ := fun i U hx => by
      rw [h𝔭]; exact (AlgebraicGeometry.Scheme.Hom.support_ker_eq_singleton_and_map_germ_ker_ideal_eq_maximalIdeal_of_field (σ i)).2 U hx

    have hprod : ∀ (c : C₂') (U : C₂'.affineOpens) (hx : c ∈ (U : C₂'.Opens)),
        Ideal.map (C₂'.presheaf.germ (U : C₂'.Opens) c hx).hom ((∏ i : Fin n, 𝔭 i).ideal U) =
          if ∃ i, (σ i).base pt = c then maximalIdeal _ else ⊤ := by
      intro c U hx
      rw [CrossAsm.map_germ_finset_prod]
      split_ifs with hc
      · obtain ⟨i, rfl⟩ := hc
        rw [Finset.prod_eq_single i]
        · exact hgermσ i U hx
        · intro i' _ hi'
          rw [Ideal.one_eq_top]
          refine (hdich₂ (𝔭 i') U _ hx).1 ?_
          rw [hsuppσ i', Set.mem_singleton_iff]
          exact fun h => hi' (hσinj h).symm
        · intro h; exact absurd (Finset.mem_univ i) h
      · push Not at hc
        rw [← Ideal.one_eq_top]
        refine Finset.prod_eq_one fun i' _ => ?_
        rw [Ideal.one_eq_top]
        refine (hdich₂ (𝔭 i') U _ hx).1 ?_
        rw [hsuppσ i', Set.mem_singleton_iff]
        exact fun h => hc i' h.symm

    have hsuppJ : ∀ c : C₂', c ∈ ((((i₁.1 ≫ bc).ker).comap F₂).support : Set C₂') ↔
        F₂.base c ∈ closure {(i₁.1 ≫ bc).base (genericPoint ↥C₁)} := by
      intro c
      rw [Scheme.IdealSheafData.support_comap]
      show F₂.base c ∈ (((i₁.1 ≫ bc).ker).support : Set _) ↔ _
      rw [hvan₁, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl

    have hoffσ : ∀ c : C₂', (¬ ∃ i, (σ i).base pt = c) → c ∉ ((((i₁.1 ≫ bc).ker).comap F₂).support : Set C₂') := by
      intro c hc hmem
      rw [hsuppJ] at hmem

      obtain ⟨a, ha⟩ := hoff₂ (e₂.base c) hmem
      have hpre : a ∈ Set.range (pullback.fst i₁.1 i₂.1).base := by
        rw [Scheme.Pullback.range_fst]; exact ⟨e₂.base c, ha.symm⟩
      obtain ⟨ν, hν⟩ := hpre
      obtain ⟨i, hi⟩ := hzsurj ν
      apply hc ⟨i, ?_⟩
      apply e₂.isOpenEmbedding.injective
      rw [heσ, hi]
      apply i₂.1.isClosedEmbedding.injective
      show (pullback.snd i₁.1 i₂.1 ≫ i₂.1).base ν = _
      rw [← pullback.condition, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, hν, ha]

    have honσ : ∀ i (U : C₂'.affineOpens) (hx : (σ i).base pt ∈ (U : C₂'.Opens)),
        Ideal.map (C₂'.presheaf.germ (U : C₂'.Opens) ((σ i).base pt) hx).hom ((((i₁.1 ≫ bc).ker).comap F₂).ideal U) =
          maximalIdeal _ := fun i U hx =>
      CrossAsm.onσ₂ p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 O ρO hunr toκ htoκ
        bc hbc₁ hbc₂ z hz₁ hz₂ hzinj i U hx

    refine hext₂ _ _ fun c => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hcU, -⟩ :=
      C₂'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ c) isOpen_univ
    refine ⟨⟨U, hU⟩, hcU, ?_⟩
    rw [hprod c ⟨U, hU⟩ hcU]
    split_ifs with hc
    · obtain ⟨i, rfl⟩ := hc
      exact honσ i ⟨U, hU⟩ hcU
    · exact (hdich₂ _ ⟨U, hU⟩ c hcU).1 (hoffσ c hc)

  have side₁ : ((i₂.1 ≫ bc).ker).comap (pullback.fst c₁ (𝟙 (Spec (CommRingCat.of k))) ≫ i₁.1 ≫ bc) =
      ∏ i : Fin n, (RelEffCartierDiv.ofPoint c₁ (z i ≫ pullback.fst i₁.1 i₂.1) (hz₁ i)).I := by

    let Y := pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)
    let fstk := pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)
    let fstO := pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))
    let C₁' := pullback c₁ (𝟙 (Spec (CommRingCat.of k)))
    let e₁ : C₁' ⟶ C₁ := pullback.fst c₁ (𝟙 (Spec (CommRingCat.of k)))
    let F₁ : C₁' ⟶ _ := e₁ ≫ i₁.1 ≫ bc
    let σ : Fin n → (Spec (CommRingCat.of k) ⟶ C₁') := fun i =>
      graphOver c₁ (z i ≫ pullback.fst i₁.1 i₂.1) (hz₁ i)
    let pt : ↥(Spec (CommRingCat.of k)) := closedPoint k
    let 𝔭 : Fin n → C₁'.IdealSheafData := fun i => (RelEffCartierDiv.ofPoint c₁ (z i ≫ pullback.fst i₁.1 i₂.1) (hz₁ i)).I
    have h𝔭 : ∀ i, 𝔭 i = (σ i).ker := fun i => RelEffCartierDiv.ofPoint_I _ _ _

    have heσ : ∀ i, e₁.base ((σ i).base pt) = (pullback.fst i₁.1 i₂.1).base ((z i).base pt) := by
      intro i
      show (σ i ≫ e₁).base pt = (z i ≫ pullback.fst i₁.1 i₂.1).base pt
      rw [graphOver_fst]
    have hσinj : Function.Injective fun i => (σ i).base pt := by
      intro i i' h
      apply hzinj
      have h' := congrArg e₁.base h
      simp only [heσ] at h'
      exact (pullback.fst i₁.1 i₂.1).isClosedEmbedding.injective h'

    have hsuppσ : ∀ i, ((𝔭 i).support : Set C₁') = {(σ i).base pt} := fun i => by
      rw [h𝔭]; exact (AlgebraicGeometry.Scheme.Hom.support_ker_eq_singleton_and_map_germ_ker_ideal_eq_maximalIdeal_of_field (σ i)).1
    have hgermσ : ∀ i (U : C₁'.affineOpens) (hx : (σ i).base pt ∈ (U : C₁'.Opens)),
        Ideal.map (C₁'.presheaf.germ (U : C₁'.Opens) ((σ i).base pt) hx).hom ((𝔭 i).ideal U) =
          maximalIdeal _ := fun i U hx => by
      rw [h𝔭]; exact (AlgebraicGeometry.Scheme.Hom.support_ker_eq_singleton_and_map_germ_ker_ideal_eq_maximalIdeal_of_field (σ i)).2 U hx

    have hprod : ∀ (c : C₁') (U : C₁'.affineOpens) (hx : c ∈ (U : C₁'.Opens)),
        Ideal.map (C₁'.presheaf.germ (U : C₁'.Opens) c hx).hom ((∏ i : Fin n, 𝔭 i).ideal U) =
          if ∃ i, (σ i).base pt = c then maximalIdeal _ else ⊤ := by
      intro c U hx
      rw [CrossAsm.map_germ_finset_prod]
      split_ifs with hc
      · obtain ⟨i, rfl⟩ := hc
        rw [Finset.prod_eq_single i]
        · exact hgermσ i U hx
        · intro i' _ hi'
          rw [Ideal.one_eq_top]
          refine (hdich₁ (𝔭 i') U _ hx).1 ?_
          rw [hsuppσ i', Set.mem_singleton_iff]
          exact fun h => hi' (hσinj h).symm
        · intro h; exact absurd (Finset.mem_univ i) h
      · push Not at hc
        rw [← Ideal.one_eq_top]
        refine Finset.prod_eq_one fun i' _ => ?_
        rw [Ideal.one_eq_top]
        refine (hdich₁ (𝔭 i') U _ hx).1 ?_
        rw [hsuppσ i', Set.mem_singleton_iff]
        exact fun h => hc i' h.symm

    have hsuppJ : ∀ c : C₁', c ∈ ((((i₂.1 ≫ bc).ker).comap F₁).support : Set C₁') ↔
        F₁.base c ∈ closure {(i₂.1 ≫ bc).base (genericPoint ↥C₂)} := by
      intro c
      rw [Scheme.IdealSheafData.support_comap]
      show F₁.base c ∈ (((i₂.1 ≫ bc).ker).support : Set _) ↔ _
      rw [hvan₂, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl

    have hoffσ : ∀ c : C₁', (¬ ∃ i, (σ i).base pt = c) → c ∉ ((((i₂.1 ≫ bc).ker).comap F₁).support : Set C₁') := by
      intro c hc hmem
      rw [hsuppJ] at hmem

      obtain ⟨b, hb⟩ := hoff₁ (e₁.base c) hmem
      have hpre : e₁.base c ∈ Set.range (pullback.fst i₁.1 i₂.1).base := by
        rw [Scheme.Pullback.range_fst]; exact ⟨b, hb⟩
      obtain ⟨ν, hν⟩ := hpre
      obtain ⟨i, hi⟩ := hzsurj ν
      apply hc ⟨i, ?_⟩
      apply e₁.isOpenEmbedding.injective
      rw [heσ, hi, hν]

    have honσ : ∀ i (U : C₁'.affineOpens) (hx : (σ i).base pt ∈ (U : C₁'.Opens)),
        Ideal.map (C₁'.presheaf.germ (U : C₁'.Opens) ((σ i).base pt) hx).hom ((((i₂.1 ≫ bc).ker).comap F₁).ideal U) =
          maximalIdeal _ := fun i U hx =>
      CrossAsm.onσ₁ p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 O ρO hunr toκ htoκ
        bc hbc₁ hbc₂ z hz₁ hz₂ hzinj i U hx

    refine hext₁ _ _ fun c => ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hcU, -⟩ :=
      C₁'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ c) isOpen_univ
    refine ⟨⟨U, hU⟩, hcU, ?_⟩
    rw [hprod c ⟨U, hU⟩ hcU]
    split_ifs with hc
    · obtain ⟨i, rfl⟩ := hc
      exact honσ i ⟨U, hU⟩ hcU
    · exact (hdich₁ _ ⟨U, hU⟩ c hcU).1 (hoffσ c hc)
  refine ⟨?_, side₂, ?_, side₁⟩
  · rw [side₂]
    exact CrossAsm.isInvertible_finset_prod _ _ fun i _ => RelEffCartierDiv.isInvertible_I _
  · rw [side₁]
    exact CrossAsm.isInvertible_finset_prod _ _ fun i _ => RelEffCartierDiv.isInvertible_I _

end S_ModularCurve_XOneP_isInvertible_comap_ker_and_comap_ker_eq_prod_ofPoint_of_map_maximalIdeal_eq_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_isInvertible_comap_ker_and_comap_ker_eq_prod_ofPoint_of_map_maximalIdeal_eq_twoChartModel_x1_mul (solution)
