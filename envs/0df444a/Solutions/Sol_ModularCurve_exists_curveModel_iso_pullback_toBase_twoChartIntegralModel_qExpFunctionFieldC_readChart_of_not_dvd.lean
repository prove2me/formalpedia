-- Prove2me | solution 1 for ModularCurve.exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4a0cf361-6c99-584c-8f7d-2a9ebc81968c

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_JacJ1_ChartAlgebra
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_isSeparable_adjoin_jqModC_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec"
p2m_attr_erase "simp" "CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun"
p2m_attr_erase "simp" "KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_ModularCurve_exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd.AlgebraicCurve ModularCurve~coeffMap_jqModC IsLocalRing"

noncomputable section

namespace F6PH

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T]

theorem finiteIndex_of_gamma1_le (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) (h : CongruenceSubgroup.Gamma1 M ≤ Γ) :
    Γ.FiniteIndex := by
  haveI : (CongruenceSubgroup.Gamma1 M).FiniteIndex := CongruenceSubgroup.instFiniteIndexGamma1 M
  exact Subgroup.finiteIndex_of_le h

theorem coeffMap_coeffMap {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (y : LaurentSeries R) : coeffMap g (coeffMap f y) = coeffMap (g.comp f) y := by
  ext n; rfl

theorem coeffEmb_coeffMap_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (R : Type*) [CommRing R] [Algebra R ℚ]
    [Algebra R L] [IsScalarTower R ℚ L] (y : LaurentSeries R) :
    coeffMap (algebraMap R L) y = coeffEmb L (coeffMap (algebraMap R ℚ) y) := by
  ext n
  show algebraMap R L (y.coeff n) = algebraMap ℚ L (algebraMap R ℚ (y.coeff n))
  rw [← IsScalarTower.algebraMap_apply]

theorem coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

theorem coeffEmb_jqModC (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L (jqModC ℚ) = jqModC L :=
  map_jqModC (algebraMap ℚ L)

end F6PH

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel.chartAlgFin TwoChartIntegralModel.chartAlgInf TwoChartIntegralModel TwoChartIntegralModel.ιFin TwoChartIntegralModel.toBase CurveModel CurveModel.X₀ CurveModel.glued CurveModel.ι₀ CurveModel.gluedToBase CurveModel.gluedFunctionFieldEquiv CurveModel.gluedFunctionFieldEquiv_algebraMap CurveModel.chartRing TwoChartIntegralModel.exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing CurveModel.isProper_smooth_places_affineCover_glued"
namespace CurveModel
p2m_export "AlgebraicCurve.CurveModel" "isProper placeOfPoint toBase C range_stalk_eq ffEquiv finset_subset_affineOpen ffEquiv_algebraMap placeOfPoint_bijective smooth incl₀ X₀ glued ι₀ gluedToBase ιU_eq gluedFunctionFieldEquiv gluedFunctionFieldEquiv_algebraMap thetaHom thetaHom_toStalk ffEquiv_symm_algebraMap_stalk chartRing centre isProper_smooth_places_affineCover_glued"
p2m_open "AlgebraicCurve.CurveModel AlgebraicCurve"

section Read

p2m_open "AlgebraicCurve.CurveModel P2MW.S_ModularCurve_exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd.AlgebraicCurve.CurveModel"

universe u

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
  [FiniteDimensional ↥(IntermediateField.adjoin K ({t} : Set L)) L]

theorem gluedFunctionFieldEquiv_symm_germToFunctionField_app
    {Y : Scheme.{u}} (g : glued K t ⟶ Y) {B : Type u} [CommRing B]
    (ι : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion ι]
    (φ : B →+* ↥(chartRing K ({t} : Set L)))
    (hsq : ι₀ K t ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ ι) (b : B)
    [hne : Nonempty (Scheme.Opens.toScheme ((g ⁻¹ᵁ (ι ''ᵁ ⊤))))] :
    (gluedFunctionFieldEquiv K t).symm
        ((glued K t).germToFunctionField (g ⁻¹ᵁ (ι ''ᵁ ⊤))
          ((g.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)))) =
      ((φ b : ↥(chartRing K ({t} : Set L))) : L) := by

  let p₀ : X₀ K t := genericPoint (X₀ K t)
  have hx : (ι₀ K t).base p₀ ∈ g ⁻¹ᵁ (ι ''ᵁ ⊤) := by
    show (ι₀ K t ≫ g) p₀ ∈ ι ''ᵁ ⊤
    rw [hsq, Scheme.Hom.image_top_eq_opensRange]
    exact ⟨_, rfl⟩
  set σ : Γ(Y, ι ''ᵁ ⊤) := (ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) with hσ
  set s : Γ(glued K t, g ⁻¹ᵁ (ι ''ᵁ ⊤)) := (g.app (ι ''ᵁ ⊤)).hom σ with hs

  have h1 : (glued K t).germToFunctionField (g ⁻¹ᵁ (ι ''ᵁ ⊤)) s =
      algebraMap ((glued K t).presheaf.stalk ((ι₀ K t).base p₀)) (glued K t).functionField
        ((glued K t).presheaf.germ (g ⁻¹ᵁ (ι ''ᵁ ⊤)) ((ι₀ K t).base p₀) hx s) := by
    change (glued K t).presheaf.germ _ (genericPoint (glued K t)) _ s =
      ((glued K t).presheaf.stalkSpecializes (genericPoint_specializes ((ι₀ K t).base p₀)))
        ((glued K t).presheaf.germ (g ⁻¹ᵁ (ι ''ᵁ ⊤)) ((ι₀ K t).base p₀) hx s)
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  rw [h1, ffEquiv_symm_algebraMap_stalk K t (chartRing K ({t} : Set L)) (incl₀ K t) (ι₀ K t) (ιU_eq K t).symm p₀]

  rw [Scheme.Hom.germ_stalkMap_apply]

  have e1 : ((ι₀ K t).app (g ⁻¹ᵁ (ι ''ᵁ ⊤))).hom s = ((ι₀ K t ≫ g).app (ι ''ᵁ ⊤)).hom σ := by
    rw [hs, Scheme.Hom.comp_app]; rfl
  rw [e1, Scheme.Hom.congr_app hsq (ι ''ᵁ ⊤)]
  erw [TopCat.Presheaf.germ_res_apply]
  change thetaHom K t (chartRing K ({t} : Set L)) (incl₀ K t) p₀
      ((X₀ K t).presheaf.germ ((Spec.map (CommRingCat.ofHom φ)) ⁻¹ᵁ (ι ⁻¹ᵁ (ι ''ᵁ ⊤))) p₀ _
        (((Spec.map (CommRingCat.ofHom φ)).app (ι ⁻¹ᵁ (ι ''ᵁ ⊤))).hom ((ι.app (ι ''ᵁ ⊤)).hom σ))) = _
  erw [← Scheme.Hom.germ_stalkMap_apply (Spec.map (CommRingCat.ofHom φ)) (ι ⁻¹ᵁ (ι ''ᵁ ⊤)) p₀]

  have h3 : (ι.app (ι ''ᵁ ⊤)).hom σ =
      (Spec (CommRingCat.of B)).presheaf.map (eqToHom (ι.preimage_image_eq ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := by
    rw [hσ, ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_app]
  rw [h3]
  erw [TopCat.Presheaf.germ_res_apply]

  change thetaHom K t (chartRing K ({t} : Set L)) (incl₀ K t) p₀
      (((Spec.map (CommRingCat.ofHom φ)).stalkMap p₀)
        (StructureSheaf.toStalk B ((Spec.map (CommRingCat.ofHom φ)).base p₀) b)) = _
  erw [AlgebraicGeometry.stalkMap_toStalk_apply (CommRingCat.ofHom φ) p₀ b]
  exact thetaHom_toStalk K t (chartRing K ({t} : Set L)) (incl₀ K t) (fun a => rfl) p₀ (φ b)

end Read

end AlgebraicCurve.CurveModel

open F6PH in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)) :
    ∃ (Mfib : CurveModel (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
      (efib : Mfib.C ⟶ pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ))))
      (_ : IsIso efib)
      (_ : Nonempty (Scheme.Opens.toScheme
        ((efib ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) ''ᵁ ⊤)))),
      efib ≫ pullback.snd (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ))) = Mfib.toBase ∧
      ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)) (y : LaurentSeries ↥A),
        coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) →
        ((Mfib.ffEquiv.symm
            (Mfib.C.germToFunctionField
              ((efib ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) ''ᵁ ⊤))
              (((efib ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))).app ((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) ''ᵁ ⊤)).hom
                (((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j).appIso ⊤).inv
                  ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))).inv b))))
          : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A)) =
          coeffMap (residue ↥A) y := by
  classical
  letI instAlg : Algebra ↥(GaloisRep.ratLocalizedAt p) (ResidueField ↥A) := ((residue ↥A).comp ρ).toAlgebra

  have hT : ModularGroup.T ∈ Γ := hΓ₁ (F6PH.T_mem_Gamma1 M)
  haveI : Γ.FiniteIndex := F6PH.finiteIndex_of_gamma1_le M Γ hΓ₁
  obtain ⟨x, hx, htx, hfdx⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A) Γ hT
  haveI := hfdx
  have hx0 : x ≠ 0 := fun h0 => htx (by rw [h0]; exact isAlgebraic_zero)
  haveI : Fact (x ≠ 0) := ⟨hx0⟩
  have hxmem : jqModC (ResidueField ↥A) ∈ qExpFunctionFieldC (ResidueField ↥A) Γ := by rw [← hx]; exact x.2
  have hxe : (⟨jqModC (ResidueField ↥A), hxmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) = x := Subtype.ext hx.symm
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin (ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) := by
    haveI : Algebra.IsAlgebraic
        ↥(IntermediateField.adjoin (ResidueField ↥A) ({(⟨jqModC (ResidueField ↥A), hxmem⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) := by
      rw [hxe]; exact Algebra.IsAlgebraic.of_finite _ _
    have key := ModularCurve.isSeparable_adjoin_jqModC_of_isAlgebraic (ResidueField ↥A) (qExpFunctionFieldC (ResidueField ↥A) Γ) hxmem
    rw [hxe] at key
    exact key

  obtain ⟨⟨eFin, hjF, hreadF⟩, ⟨eInf, hjI, hreadI⟩⟩ :=
    ModularCurve.exists_algEquiv_residueField_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_chartRing
      M Γ hΓ₁ hΓ₀ p hpM j hj A hA ρ hρ x hx

  obtain ⟨hliftF, hliftI⟩ :=
    ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC Γ p j hj
  have hcompat : ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))
      (b' : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)) (n : ℕ),
      (b : ↥(qExpFunctionFieldC ℚ Γ)) = (b' : ↥(qExpFunctionFieldC ℚ Γ)) * j ^ n →
      ((eFin ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b)) : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) = ((eInf ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b')) : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) * x ^ n := by
    intro b b' n h
    obtain ⟨y₀, hy₀⟩ := hliftI b'
    have hyA : coeffMap A.subtype (coeffMap ρ y₀) = coeffEmb (AlgebraicClosure ℚ) (((b' : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) := by
      rw [F6PH.coeffMap_coeffMap, hρ, ← hy₀, F6PH.coeffEmb_coeffMap_algebraMap]
    have hyB : coeffMap A.subtype (coeffMap ρ y₀ * jqModC ↥A ^ n) =
        coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) := by
      rw [map_mul, map_pow, hyA, F6PH.coeffMap_jqModC, h]
      show _ = coeffEmb (AlgebraicClosure ℚ) (((b' : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) * ((j : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) ^ n)
      rw [map_mul, map_pow, hj, F6PH.coeffEmb_jqModC]
    have h1 := hreadF b _ hyB
    have h2 := hreadI b' _ hyA
    apply Subtype.ext
    rw [h1, map_mul, map_pow, ← h2, F6PH.coeffMap_jqModC, MulMemClass.coe_mul, SubmonoidClass.coe_pow, hx]

  obtain ⟨hPr, hSm, ⟨P, hPbij, hPst⟩, hAff⟩ :=
    AlgebraicCurve.CurveModel.isProper_smooth_places_affineCover_glued (ResidueField ↥A) (L := ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) x htx
  obtain ⟨es, hes_iso, hes, hpinF, hpinI⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_iso_glued_pullback_toBase_of_algEquiv_chartAlg_chartRing
      ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j (ResidueField ↥A) x eFin eInf hjF hjI hcompat
  let Ms : CurveModel (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) :=
    { C := CurveModel.glued (ResidueField ↥A) x
      toBase := CurveModel.gluedToBase (ResidueField ↥A) x
      isProper := hPr
      smooth := hSm
      ffEquiv := CurveModel.gluedFunctionFieldEquiv (ResidueField ↥A) x
      ffEquiv_algebraMap := CurveModel.gluedFunctionFieldEquiv_algebraMap (ResidueField ↥A) x
      placeOfPoint := P
      placeOfPoint_bijective := hPbij
      range_stalk_eq := hPst
      finset_subset_affineOpen := hAff }

  let rF : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) →+* ↥(CurveModel.chartRing (ResidueField ↥A) ({x} : Set ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))) :=
    eFin.toAlgHom.toRingHom.comp (Algebra.TensorProduct.includeRight
      (R := ↥(GaloisRep.ratLocalizedAt p)) (A := ResidueField ↥A) (B := ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))).toRingHom
  have rF_apply : ∀ b, rF b = eFin ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b) := fun b => rfl
  have hsq : CurveModel.ι₀ (ResidueField ↥A) x ≫ (es ≫ pullback.fst _ _) =
      Spec.map (CommRingCat.ofHom rF) ≫ TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j := hpinF

  have hne : Nonempty (Scheme.Opens.toScheme
      ((es ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))) ⁻¹ᵁ
        ((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) ''ᵁ ⊤))) := by
    let p₀ : CurveModel.X₀ (ResidueField ↥A) x := Classical.arbitrary _
    refine ⟨⟨(CurveModel.ι₀ (ResidueField ↥A) x).base p₀, ?_⟩⟩
    show ((CurveModel.ι₀ (ResidueField ↥A) x) ≫ es ≫
        pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)))) p₀ ∈
      (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) ''ᵁ ⊤
    rw [hsq, Scheme.Hom.image_top_eq_opensRange]
    exact ⟨_, rfl⟩
  refine ⟨Ms, es, hes_iso, hne, hes, ?_⟩

  intro b y hy
  haveI := hne
  have hread := AlgebraicCurve.CurveModel.gluedFunctionFieldEquiv_symm_germToFunctionField_app (ResidueField ↥A) x
    (es ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ))))
    (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) rF hsq b
  calc _ = (((eFin ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b)).1 : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A)) :=
        congrArg (fun z : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) => (z : LaurentSeries (ResidueField ↥A))) hread
    _ = coeffMap (residue ↥A) y := hreadF b y hy

end

end S_ModularCurve_exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_exists_curveModel_iso_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_readChart_of_not_dvd (solution)
