-- Prove2me | solution 1 for ModularCurve.XOneP.pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_igusaModel_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/dfd9a023-2429-5d3a-a532-4310c9fc258b

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
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing
import Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_infinite_setOf_isClosed_singleton
import Theorems.Thm_ModularCurve_XOneP_eq_of_forall_specializes_imp_eq_of_ringEquiv_stalk_of_fst_eq_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_germ_mem_maximalIdeal_and_ringKrullDim_stalk_le_one_of_isGenericPoint_component_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_ringEquiv_stalk_apply_germ_eq_of_ringKrullDim_le_one_twoChartIntegralModel_x1_mul
import Theorems.Thm_AlgebraicCurve_CurveModel_pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq
import Theorems.Thm_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_igusaModel_twoChartModel_x1_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct"
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module"
p2m_attr_erase "instance" "TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve P2MW.S_ModularCurve_XOneP_pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_igusaModel_twoChartModel_x1_mul.AlgebraicCurve"

namespace IsCyclotomicExtension
p2m_export "IsCyclotomicExtension" "integral eq Rat.surjective_algebraMap_int_residueField_of_isDiscreteValuationRing"
namespace Rat
p2m_export "IsCyclotomicExtension.Rat" "surjective_algebraMap_int_residueField_of_isDiscreteValuationRing"
p2m_open "IsCyclotomicExtension.Rat IsCyclotomicExtension"

theorem maximalIdeal_le_ker_of_charP (p : ℕ) [Fact p.Prime]
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (hp0 : (p : A) ≠ 0)
    {k : Type*} [CommRing k] [IsDomain k] [CharP k p] (φ : A →+* k) :
    IsLocalRing.maximalIdeal A ≤ RingHom.ker φ := by
  have hp : (p : A) ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hne : RingHom.ker φ ≠ ⊥ := fun h => hp0 (by rwa [h, Ideal.mem_bot] at hp)
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmax : (RingHom.ker φ).IsMaximal := IsPrime.to_maximal_ideal hne
  exact (IsLocalRing.eq_maximalIdeal hmax).ge

theorem apply_pow_eq_apply_of_isDiscreteValuationRing (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    {k : Type*} [CommRing k] [IsDomain k] [CharP k p] (φ : A →+* k) (a : A) :
    φ a ^ p = φ a := by
  have hp0 : (p : A) ≠ 0 := fun h => by
    have h' := congrArg (algebraMap A L) h
    rw [map_natCast, map_zero] at h'
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h')
  obtain ⟨n, hn⟩ := IsCyclotomicExtension.Rat.surjective_algebraMap_int_residueField_of_isDiscreteValuationRing
    p L A hAp (IsLocalRing.residue A a)
  have hres : IsLocalRing.residue A a = IsLocalRing.residue A (n : A) := by
    rw [← hn, eq_intCast, map_intCast]
  have hmem : a - (n : A) ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq.1 hres
  have hker := maximalIdeal_le_ker_of_charP p A hp0 φ hmem
  rw [RingHom.mem_ker, map_sub, sub_eq_zero, map_intCast] at hker
  have hfix : ((n : k)) ^ p = n := by rw [← frobenius_def, map_intCast]
  rw [hker, hfix]

theorem frobenius_comp_algebraMap_eq (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (k : Type*) [CommRing k] [IsDomain k] [CharP k p] [Algebra A k] :
    (frobenius k p).comp (algebraMap A k) = algebraMap A k :=
  RingHom.ext fun a => apply_pow_eq_apply_of_isDiscreteValuationRing p L A hAp (algebraMap A k) a

end IsCyclotomicExtension.Rat

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "SemilinearAut SemilinearAut.toRingAut SemilinearAut.baseAut SemilinearAut.toRingAut_inv SemilinearAut.smul_algebraMap Place Place.ext CurveModel TwoChartIntegralModel.chartAlgFin TwoChartIntegralModel infinite_setOf_isClosed_singleton CurveModel.pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq" namespace Place p2m_export "AlgebraicCurve.Place" "ext ne_top' toValuationSubring" end AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

theorem AlgebraicCurve.Place.eq_of_le {k F : Type*} [Field k] [Field F] [Algebra k F] {v w : AlgebraicCurve.Place k F}
    (h : v.toValuationSubring ≤ w.toValuationSubring) : v = w :=
  AlgebraicCurve.Place.ext (ValuationSubring.eq_of_le_of_ne_top v.toValuationSubring h w.ne_top')

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FrobTwist

universe u

section twist

variable {X T S : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (σ : T ≅ T) (hσ : σ.hom ≫ g = g)

include hσ in
theorem inv_comp_eq : σ.inv ≫ g = g := by
  rw [← hσ, σ.inv_hom_id_assoc, hσ]

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

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

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve P2MW.S_ModularCurve_XOneP_pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_igusaModel_twoChartModel_x1_mul.AlgebraicCurve"

namespace FrobPTTools

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

section FFMap

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (θ : X ⟶ Y) [IsIso θ]

theorem genericPoint_specializes : θ.base (genericPoint X) ⤳ genericPoint Y := by
  rw [genericPoint_eq_of_isOpenImmersion θ]

noncomputable def ffMap : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes (genericPoint_specializes θ) ≫ θ.stalkMap (genericPoint X)

@[reassoc]
theorem SpecMap_ffMap_fromSpecStalk :
    Spec.map (ffMap θ) ≫ Y.fromSpecStalk (genericPoint Y) = X.fromSpecStalk (genericPoint X) ≫ θ := by
  rw [ffMap, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem ffMap_germ_apply (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    ffMap θ (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (θ ⁻¹ᵁ U) (genericPoint X)
        (show θ.base (genericPoint X) ∈ U by rwa [genericPoint_eq_of_isOpenImmersion θ]) (θ.app U s) := by
  rw [← CommRingCat.comp_apply, ffMap, TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
  rfl

theorem ffMap_germ_of_eq {Z : Scheme.{u}} (g₂ : Y ⟶ Z) (g₁ : X ⟶ Z) (e : g₁ = θ ≫ g₂)
    (U : Z.Opens) (h₂ : genericPoint Y ∈ g₂ ⁻¹ᵁ U) (h₁ : genericPoint X ∈ g₁ ⁻¹ᵁ U) (s : Γ(Z, U)) :
    ffMap θ (Y.presheaf.germ (g₂ ⁻¹ᵁ U) (genericPoint Y) h₂ (g₂.app U s)) =
      X.presheaf.germ (g₁ ⁻¹ᵁ U) (genericPoint X) h₁ (g₁.app U s) := by
  subst e
  rw [ffMap_germ_apply]
  rfl

end FFMap

section Misc

theorem spec_map_comp_eq_id {A B : Type u} [CommRing A] [CommRing B] (a : A →+* B) (b : B →+* A)
    (hab : ∀ x, a (b x) = x) :
    Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show a.comp b = RingHom.id B from RingHom.ext hab, CommRingCat.ofHom_id]
  exact Spec.map_id _

theorem isIso_spec_map_of_bijective {A : Type u} [CommRing A] (f : A →+* A) (hf : Function.Bijective f) :
    IsIso (Spec.map (CommRingCat.ofHom f)) := by
  let e := RingEquiv.ofBijective f hf
  refine ⟨⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom), ?_, ?_⟩⟩
  · exact spec_map_comp_eq_id _ _ (fun x => e.apply_symm_apply x)
  · exact spec_map_comp_eq_id _ _ (fun x => e.symm_apply_apply x)

end Misc

section Laurent

open HahnSeries

variable {A B : Type*} [CommRing A] [CommRing B]

theorem coeffMap_ofPowerSeries (f : A →+* B) (g : PowerSeries A) :
    ModularCurve.coeffMap f (HahnSeries.ofPowerSeries ℤ A g) =
      HahnSeries.ofPowerSeries ℤ B (PowerSeries.map f g) := by
  ext n
  rw [ModularCurve.coeffMap_coeff]
  change f ((g : LaurentSeries A).coeff n) = ((PowerSeries.map f g : PowerSeries B) : LaurentSeries B).coeff n
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with h
  · rw [map_zero]
  · rw [PowerSeries.coeff_map]

theorem coeffMap_frobenius_ofPowerSeries_map (p : ℕ) [Fact p.Prime] [CharP B p] (π : A →+* B)
    (hπ : (frobenius B p).comp π = π) (x : PowerSeries A) :
    ModularCurve.coeffMap (frobenius B p) (HahnSeries.ofPowerSeries ℤ B (PowerSeries.map π x)) =
      HahnSeries.ofPowerSeries ℤ B (PowerSeries.map π x) := by
  rw [coeffMap_ofPowerSeries, ← RingHom.comp_apply (PowerSeries.map (frobenius B p)) (PowerSeries.map π) x,
    ← PowerSeries.map_comp, hπ]

end Laurent

end FrobPTTools

open FrobPTTools

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
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

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)
    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₁ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 →
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
        HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)))

    (frobIg : SemilinearAut k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hfrobIg : ∀ (x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (n : ℤ),
      ((frobIg • x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k).coeff n = ((x : LaurentSeries k).coeff n) ^ p) :
    ∀ (c c' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      c'.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
        Spec.map (CommRingCat.ofHom (frobenius k p)) ≫ c.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) →
      Mdl₁.pointEquivPlace ⟨c'.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c'.2⟩ =
        frobIg • Mdl₁.pointEquivPlace ⟨c.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c.2⟩ := by
  intro c c' hc
  classical

  haveI : IsIntegral C₁ := FrobFix.isIntegral_of_geometricallyIntegral c₁

  have hL1 : (frobenius k p).comp (algebraMap A k) = algebraMap A k :=
    IsCyclotomicExtension.Rat.frobenius_comp_algebraMap_eq p L A hAp k
  haveI hσiso : IsIso (Spec.map (CommRingCat.ofHom (frobenius k p))) :=
    FrobPTTools.isIso_spec_map_of_bijective (frobenius k p) (bijective_frobenius k p)
  let σ : Spec (CommRingCat.of k) ≅ Spec (CommRingCat.of k) := asIso (Spec.map (CommRingCat.ofHom (frobenius k p)))
  have hσhom : σ.hom = Spec.map (CommRingCat.ofHom (frobenius k p)) := rfl
  have hσ : σ.hom ≫ specMap A k = specMap A k := by
    rw [hσhom]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hL1]
  let τ := FrobTwist.twist (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) σ hσ
  have hτfst : τ.hom ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) := FrobTwist.twist_hom_fst _ _ _ _
  have hτinvfst : τ.inv ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) := FrobTwist.twist_inv_fst _ _ _ _

  have himg : τ.hom.base '' Set.range i₁.1.base ⊆ Set.range i₁.1.base :=
    FrobFix.image_range_subset p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 τ.hom hτfst
  have himg' : τ.inv.base '' Set.range i₁.1.base ⊆ Set.range i₁.1.base :=
    FrobFix.image_range_subset p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 τ.inv hτinvfst
  have hrange_e : Set.range (e₁.hom ≫ i₁.1).base = Set.range i₁.1.base := by
    ext z
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨e₁.hom.base m, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨e₁.inv.base y, ?_⟩
      change (e₁.inv ≫ e₁.hom ≫ i₁.1).base y = _
      rw [e₁.inv_hom_id_assoc]
  let θ : Mdl₁.C ≅ Mdl₁.C := FrobTwist.liftAut (e₁.hom ≫ i₁.1) τ (by rw [hrange_e]; exact himg)
    (by rw [hrange_e]; exact himg')
  let Wt : Mdl₁.C ⟶ Mdl₁.C := θ.hom
  haveI hWtiso : IsIso Wt := inferInstance
  have hWt : Wt ≫ e₁.hom ≫ i₁.1 = (e₁.hom ≫ i₁.1) ≫ τ.hom :=
    FrobTwist.liftAut_hom_comp (e₁.hom ≫ i₁.1) τ _ _

  let g₂ : Mdl₁.C ⟶ ModularCurve.TwoChartModel A (↥K) j :=
    e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)
  have hWt_g₂ : Wt ≫ g₂ = g₂ := by
    change Wt ≫ e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) =
      e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)
    rw [reassoc_of% hWt, hτfst]
  have htb : Mdl₁.toBase = e₁.hom ≫ i₁.1 ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) := by
    rw [← he₁]
    exact congrArg (e₁.hom ≫ ·) i₁.2.symm
  have hWt_base : Wt ≫ Mdl₁.toBase = Mdl₁.toBase ≫ σ.hom := by
    rw [htb, reassoc_of% hWt, FrobTwist.twist_hom_snd]
    simp only [Category.assoc]

  have hsnd₁ : i₁.1 ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = c₁ := i₁.2
  have hP : (c.1 ≫ i₁.1) ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = 𝟙 _ := by
    rw [Category.assoc, hsnd₁, c.2]
  have hP' : (c'.1 ≫ i₁.1) ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = 𝟙 _ := by
    rw [Category.assoc, hsnd₁, c'.2]
  have hcomp : (c'.1 ≫ i₁.1) ≫ τ.hom = σ.hom ≫ c.1 ≫ i₁.1 :=
    FrobTwist.comp_twist_hom_eq (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) σ hσ hP hP'
      (by simpa only [Category.assoc, hσhom] using hc)
  have hxWt : (c'.1 ≫ e₁.inv) ≫ Wt = σ.hom ≫ c.1 ≫ e₁.inv := by
    rw [← cancel_mono (e₁.hom ≫ i₁.1)]
    simp only [Category.assoc]
    rw [hWt]
    simp only [Category.assoc, e₁.inv_hom_id_assoc]
    simpa only [Category.assoc] using hcomp
  let x : {q : Spec (CommRingCat.of k) ⟶ Mdl₁.C // q ≫ Mdl₁.toBase = 𝟙 _} :=
    ⟨c'.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c'.2⟩
  let x' : {q : Spec (CommRingCat.of k) ⟶ Mdl₁.C // q ≫ Mdl₁.toBase = 𝟙 _} :=
    ⟨c.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact c.2⟩
  have hxx' : x'.1.base (IsLocalRing.closedPoint k) = Wt.base (x.1.base (IsLocalRing.closedPoint k)) := by
    change (c.1 ≫ e₁.inv).base _ = ((c'.1 ≫ e₁.inv) ≫ Wt).base _
    rw [hxWt]
    change _ = (c.1 ≫ e₁.inv).base (σ.hom.base (IsLocalRing.closedPoint k))
    congr 1
    exact Subsingleton.elim _ _

  let Ig := ↥(ModularCurve.igusaFunctionFieldX1C k M w)
  let α : Ig ≃+* Ig := SemilinearAut.toRingAut frobIg
  have hff : (FrobPTTools.ffMap Wt).hom.comp Mdl₁.ffEquiv.toRingHom = Mdl₁.ffEquiv.toRingHom.comp α.toRingHom := by

    let V : (ModularCurve.TwoChartModel A (↥K) j).Opens := (ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤
    let U : Mdl₁.C.Opens := g₂ ⁻¹ᵁ V
    let sec : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) → Γ(ModularCurve.TwoChartModel A (↥K) j, V) := fun a =>
      ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
        ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a)
    haveI : Nonempty ↥U := hne₁
    have hηU : genericPoint Mdl₁.C ∈ U :=
      ((genericPoint_spec Mdl₁.C).mem_open_set_iff U.2).mpr (by
        obtain ⟨⟨y, hy⟩⟩ := hne₁
        exact ⟨y, Set.mem_univ _, hy⟩)
    let rd : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) → Ig := fun a =>
      Mdl₁.ffEquiv.symm (Mdl₁.C.germToFunctionField U (g₂.app V (sec a)))
    have hrd : ∀ a, Mdl₁.ffEquiv (rd a) = Mdl₁.C.presheaf.germ U (genericPoint Mdl₁.C) hηU (g₂.app V (sec a)) := by
      intro a
      change Mdl₁.ffEquiv (Mdl₁.ffEquiv.symm _) = _
      rw [RingEquiv.apply_symm_apply]

    have hread : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
        y.map (algebraMap A k) ≠ 0 →
        ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
          HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        ((rd a : Ig) : LaurentSeries k) =
          HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)) :=
      fun a x y hy hxy => hgauss₁ a x y hy hxy

    have hfrob_coe : ∀ z : Ig, ((frobIg • z : Ig) : LaurentSeries k) = ModularCurve.coeffMap (frobenius k p) (z : LaurentSeries k) := by
      intro z
      ext m
      rw [hfrobIg, ModularCurve.coeffMap_coeff, frobenius_def]
    have hfix : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
        y.map (algebraMap A k) ≠ 0 →
        ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
          HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        frobIg • rd a = rd a := by
      intro a x y hy hxy
      apply Subtype.ext
      rw [hfrob_coe, hread a x y hy hxy, map_div₀,
        FrobPTTools.coeffMap_frobenius_ofPowerSeries_map p (algebraMap A k) hL1,
        FrobPTTools.coeffMap_frobenius_ofPowerSeries_map p (algebraMap A k) hL1]

    have hcoe_alg : ∀ d : k, ((algebraMap k Ig d : Ig) : LaurentSeries k) = HahnSeries.single 0 d := by
      intro d
      change algebraMap k (LaurentSeries k) d = HahnSeries.single 0 d
      exact ModularCurve.algebraMap_laurentSeries_eq_single k d
    have hbase : ∀ d : k, SemilinearAut.baseAut frobIg d = d ^ p := by
      intro d
      have h := hfrobIg (algebraMap k Ig d) 0
      rw [SemilinearAut.smul_algebraMap] at h
      change ((algebraMap k Ig (SemilinearAut.baseAut frobIg d) : Ig) : LaurentSeries k).coeff 0 =
        ((algebraMap k Ig d : Ig) : LaurentSeries k).coeff 0 ^ p at h
      rwa [hcoe_alg, hcoe_alg, HahnSeries.coeff_single_same, HahnSeries.coeff_single_same] at h

    let T : Set Ig := {z | ∃ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 ∧
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧ z = rd a}
    let S : Set Ig := Set.range (algebraMap k Ig) ∪ T
    have hp0 : (p : A) ≠ 0 := fun h => by
      have h' := congrArg (algebraMap A L) h
      rw [map_natCast, map_zero] at h'
      exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast h')
    have hyres : ∀ y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 → y.map (algebraMap A k) ≠ 0 := by
      intro y hy h0
      apply hy
      ext m
      have hm := congrArg (PowerSeries.coeff m) h0
      rw [PowerSeries.coeff_map, map_zero] at hm
      rw [PowerSeries.coeff_map, map_zero, IsLocalRing.residue_eq_zero_iff]
      exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (algebraMap A k)) (RingHom.mem_ker.2 hm)
    have hgen : Subfield.closure S = ⊤ := by
      let val : Ig →+* LaurentSeries k := (ModularCurve.igusaFunctionFieldX1C k M w).toSubfield.subtype
      have hval : ∀ z : Ig, val z = (z : LaurentSeries k) := fun _ => rfl

      have hle : (IntermediateField.adjoin k {r : LaurentSeries k |
          ∃ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
            y.map (IsLocalRing.residue A) ≠ 0 ∧
            (((b : ↥K) : LaurentSeries L)) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
              = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
            r = HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) /
                  HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k))}).toSubfield ≤ (Subfield.closure S).map val := by
        rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
        rintro r (⟨d, rfl⟩ | ⟨b, x, y, hy, hxy, rfl⟩)
        · exact ⟨algebraMap k Ig d, Subfield.subset_closure (Or.inl ⟨d, rfl⟩), rfl⟩
        · let a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) := ⟨(b : ↥K), b.2⟩
          have hy' : y.map (algebraMap A k) ≠ 0 := hyres y hy
          refine ⟨rd a, Subfield.subset_closure (Or.inr ⟨a, x, y, hy', hxy, rfl⟩), ?_⟩
          rw [hval, hread a x y hy' hxy]
      rw [eq_top_iff]
      intro z _
      obtain ⟨hz, -⟩ := ModularCurve.XOneP.coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul
        p M hM hpM L ζ hζ K hK A hAp hζA j hj k w
      obtain ⟨z', hz'S, hzz⟩ := hle (hz z)
      have : z' = z := Subtype.ext hzz
      exact this ▸ hz'S
    have hconst : ∀ d : k, FrobPTTools.ffMap Wt (Mdl₁.ffEquiv (algebraMap k Ig d)) =
        Mdl₁.ffEquiv (α (algebraMap k Ig d)) := by
      intro d
      change _ = Mdl₁.ffEquiv (frobIg • algebraMap k Ig d)
      rw [SemilinearAut.smul_algebraMap, hbase, Mdl₁.ffEquiv_algebraMap, Mdl₁.ffEquiv_algebraMap]
      have key := FrobPTTools.ffMap_germ_of_eq Wt Mdl₁.toBase (Mdl₁.toBase ≫ σ.hom) hWt_base.symm ⊤
        (show genericPoint Mdl₁.C ∈ Mdl₁.toBase ⁻¹ᵁ ⊤ from trivial)
        (show genericPoint Mdl₁.C ∈ (Mdl₁.toBase ≫ σ.hom) ⁻¹ᵁ ⊤ from trivial)
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv d)
      have hσapp : (Mdl₁.toBase ≫ σ.hom).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv d) =
          Mdl₁.toBase.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv (d ^ p)) := by
        rw [Scheme.Hom.comp_app]
        change Mdl₁.toBase.app _ (σ.hom.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv d)) = _
        have e6 := CategoryTheory.ConcreteCategory.congr_hom
          (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (frobenius k p))) d
        rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e6
        rw [hσhom]
        erw [← e6]
        rfl
      rw [hσapp] at key
      exact key
    have hchart : ∀ z ∈ T, FrobPTTools.ffMap Wt (Mdl₁.ffEquiv z) = Mdl₁.ffEquiv (α z) := by
      rintro z ⟨a, x, y, hy, hxy, rfl⟩
      change _ = Mdl₁.ffEquiv (frobIg • rd a)
      rw [hfix a x y hy hxy, hrd]
      exact FrobPTTools.ffMap_germ_of_eq Wt g₂ g₂ hWt_g₂.symm V hηU hηU (sec a)
    apply RingHom.eq_of_eqOn_of_field_closure_eq_top hgen
    rintro z (⟨d, rfl⟩ | hz)
    · exact hconst d
    · exact hchart z hz
  have hffMap : FrobPTTools.ffMap Wt = CommRingCat.ofHom
      (Mdl₁.ffEquiv.toRingHom.comp (α.toRingHom.comp Mdl₁.ffEquiv.symm.toRingHom)) := by
    ext v
    have := RingHom.congr_fun hff (Mdl₁.ffEquiv.symm v)
    simpa using this
  have hα : α = (SemilinearAut.toRingAut frobIg⁻¹).symm := by
    rw [SemilinearAut.toRingAut_inv, RingEquiv.symm_symm]
  have hθgen : Mdl₁.C.fromSpecStalk (genericPoint Mdl₁.C) ≫ Wt =
      Spec.map (CommRingCat.ofHom (Mdl₁.ffEquiv.toRingHom.comp
        ((SemilinearAut.toRingAut frobIg⁻¹).symm.toRingHom.comp Mdl₁.ffEquiv.symm.toRingHom))) ≫
        Mdl₁.C.fromSpecStalk (genericPoint Mdl₁.C) := by
    rw [← FrobPTTools.SpecMap_ffMap_fromSpecStalk Wt, hffMap, hα]

  have key := AlgebraicCurve.CurveModel.pointEquivPlace_eq_smul_pointEquivPlace_of_fromSpecStalk_comp_eq_of_apply_closedPoint_eq
    Mdl₁ frobIg⁻¹ Wt hθgen x x' hxx'

  rw [key, smul_inv_smul]

end S_ModularCurve_XOneP_pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_igusaModel_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_igusaModel_twoChartModel_x1_mul (solution)
