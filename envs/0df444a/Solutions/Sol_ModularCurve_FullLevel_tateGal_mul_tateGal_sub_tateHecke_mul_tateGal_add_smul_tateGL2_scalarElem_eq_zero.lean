-- Prove2me | solution 1 for ModularCurve.FullLevel.tateGal_mul_tateGal_sub_tateHecke_mul_tateGal_add_smul_tateGL2_scalarElem_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/3e15bc7a-d83b-59af-bc3c-052aebe8a627

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ModularCurve_FullLevel_eval_gl2Jac_scalarElem_eq_diamondHBar_inv_eval_pow
import Theorems.Thm_ModularCurve_frobeniusQuadratic_tateModule_jH
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_diamondHBar_mul
import Theorems.Thm_ModularCurve_heckeOperatorHAlong_comm
import Theorems.Thm_ModularCurve_heckeOperatorHAlong_diamondHBar_comm
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGal_sub_tateHecke_mul_tateGal_add_smul_tateGL2_scalarElem_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.coe_laurentReductionDegZero ModularCurve.laurentReductionDiv_apply ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero"
p2m_attr_erase "simp" "TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq"
p2m_attr_erase "simp" "NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

noncomputable section

namespace W6ES

open ModularCurve ModularCurve.FullLevel

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section Diamond

variable (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ)

theorem diamondHBar_one (x : JH N H) : diamondHBar N H 1 x = x := by
  have h := ModularCurve.diamondHBar_mul N H 1 1 x
  rw [mul_one] at h
  simp only [diamondHBar_apply] at h ⊢
  exact MulAction.injective (AlgebraicCurve.SemilinearAut.ofAlgAut (diamondAutHBar N H 1)) h.symm

theorem diamondHBar_inv_mul (d : (ZMod N)ˣ) (x : JH N H) :
    diamondHBar N H d⁻¹ (diamondHBar N H d x) = x := by
  rw [← ModularCurve.diamondHBar_mul, inv_mul_cancel, diamondHBar_one]

end Diamond

section Component

variable (N p : ℕ) [NeZero N] [Fact p.Prime] (H : Subgroup (ZMod N)ˣ) (S : Set ℕ)

theorem frobeniusQuadratic_diaInv_level (hin : HeckeDiamondInputsHAll N H)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : Gal) (hσ : A.IsFrobeniusAt σ ℓ) (x : TateModule p (JH N H)) (n : ℕ) :
    σ • σ • (x : ℕ → JH N H) n
      - diamondHBar N H (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN))⁻¹
          (genOpH N H S (.T ℓ hℓ hℓS hℓN) (σ • (x : ℕ → JH N H) n))
      + ℓ • diamondHBar N H (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN))⁻¹
          ((x : ℕ → JH N H) n) = 0 := by
  have hES := ModularCurve.frobeniusQuadratic_tateModule_jH N p H S hin hℓ hℓS hℓN hℓp A hA σ hσ x

  have hJ : diamondHBar N H (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN))
        (σ • σ • (x : ℕ → JH N H) n) -
      genOpH N H S (.T ℓ hℓ hℓS hℓN) (σ • (x : ℕ → JH N H) n) +
      ℓ • (x : ℕ → JH N H) n = 0 :=
    congrArg (fun z : ↥(TateModule p (JH N H)) => (z : ℕ → JH N H) n) hES

  have key := congrArg
    (diamondHBar N H (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓN))⁻¹) hJ
  simp only [map_add (diamondHBar N H _), map_sub (diamondHBar N H _), map_nsmul (diamondHBar N H _),
    map_zero (diamondHBar N H _)] at key
  rw [diamondHBar_inv_mul] at key
  exact key

end Component

section Idx

variable {q : ℕ} [Fact q.Prime]

theorem pow_val_eq_pow_mod (ζ : Idx q) (n : ℕ) : ζ.val ^ n = ζ.val ^ (n % q) := by
  conv_lhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, ζ.isPrimitiveRoot.pow_eq_one, one_pow, one_mul]

theorem Idx.pow_pow (a b : (ZMod q)ˣ) (ζ : Idx q) : (ζ.pow a).pow b = ζ.pow (a * b) := by
  apply Idx.ext
  rw [Idx.val_pow, Idx.val_pow, Idx.val_pow, ← pow_mul, Units.val_mul, ZMod.val_mul,
    ← pow_val_eq_pow_mod]

theorem Idx.pow_comm (a b : (ZMod q)ˣ) (ζ : Idx q) : (ζ.pow a).pow b = (ζ.pow b).pow a := by
  rw [Idx.pow_pow, Idx.pow_pow, mul_comm]

theorem Idx.pow_one (ζ : Idx q) : ζ.pow 1 = ζ := by
  apply Idx.ext
  haveI : Fact (1 < q) := ⟨(Fact.out : q.Prime).one_lt⟩
  rw [Idx.val_pow, Units.val_one, ZMod.val_one, _root_.pow_one]

theorem frob_smul {ℓ : ℕ} (hℓq : ℓ.Coprime q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : Gal) (hσ : A.IsFrobeniusAt σ ℓ) (ζ : Idx q) :
    σ • ζ = ζ.pow (ZMod.unitOfCoprime ℓ hℓq) := by
  apply Idx.ext
  rw [Idx.val_smul, Idx.val_pow, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_val_eq_pow_mod]
  exact ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A σ ℓ q hA hσ hℓq.symm ζ.val
    ζ.isPrimitiveRoot.pow_eq_one

theorem frob_inv_smul {ℓ : ℕ} (hℓq : ℓ.Coprime q)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : Gal) (hσ : A.IsFrobeniusAt σ ℓ) (ζ : Idx q) :
    σ⁻¹ • ζ = ζ.pow (ZMod.unitOfCoprime ℓ hℓq)⁻¹ := by
  have h := frob_smul hℓq A hA σ hσ (ζ.pow (ZMod.unitOfCoprime ℓ hℓq)⁻¹)
  rw [Idx.pow_pow, inv_mul_cancel, Idx.pow_one] at h
  nth_rw 1 [← h]
  rw [inv_smul_smul]

end Idx

section HeckeCommute

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

omit [Fact q.Prime] [NeZero M'] in
theorem coprime_q_of_not_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ q * M') : ℓ.Coprime q :=
  (Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hd => h (hd.mul_right M')

omit [Fact q.Prime] [NeZero M'] in
theorem coprime_level_of_not_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ q * M') : ℓ.Coprime (q ^ 2 * M') := by
  refine Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 (coprime_q_of_not_dvd q M' hℓ h)) ?_
  exact (Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hd => h (hd.mul_left q)

omit [Fact q.Prime] [NeZero M'] in
theorem not_dvd_level_of_coprime {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ℓ.Coprime (q ^ 2 * M')) : ¬ ℓ ∣ q ^ 2 * M' :=
  (Nat.Prime.coprime_iff_not_dvd hℓ).1 h

theorem heckeGenCommute : HeckeGenCommute q M' := by
  intro ℓ ℓ'
  by_cases h1 : (ℓ : ℕ) ∣ q * M'
  · rw [heckeGenJac_of_dvd h1, zero_mul, mul_zero]
  by_cases h2 : (ℓ' : ℕ) ∣ q * M'
  · rw [heckeGenJac_of_dvd h2, zero_mul, mul_zero]
  have hℓ : (ℓ : ℕ).Prime := ℓ.2
  have hℓ' : (ℓ' : ℕ).Prime := ℓ'.2
  have hq1 := coprime_q_of_not_dvd q M' hℓ h1
  have hq2 := coprime_q_of_not_dvd q M' hℓ' h2
  have hN1 := coprime_level_of_not_dvd q M' hℓ h1
  have hN2 := coprime_level_of_not_dvd q M' hℓ' h2
  haveI : Fact (ℓ : ℕ).Prime := ⟨hℓ⟩
  haveI : Fact (ℓ' : ℕ).Prime := ⟨hℓ'⟩
  refine AddMonoidHom.ext fun x => Jac.ext fun ζ => ?_
  show (heckeGenJac q M' ℓ (heckeGenJac q M' ℓ' x)).eval ζ =
    (heckeGenJac q M' ℓ' (heckeGenJac q M' ℓ x)).eval ζ
  rw [heckeGenJac_eval hℓ h1 hq1 hN1, heckeGenJac_eval hℓ' h2 hq2 hN2, heckeGenJac_eval hℓ' h2 hq2 hN2,
    heckeGenJac_eval hℓ h1 hq1 hN1, Idx.pow_comm]

  set y := x.eval ((ζ.pow (ZMod.unitOfCoprime (ℓ' : ℕ) hq2)⁻¹).pow (ZMod.unitOfCoprime (ℓ : ℕ) hq1)⁻¹)
  set a : (ZMod (q ^ 2 * M'))ˣ := (ZMod.unitOfCoprime (ℓ : ℕ) hN1)⁻¹
  set b : (ZMod (q ^ 2 * M'))ˣ := (ZMod.unitOfCoprime (ℓ' : ℕ) hN2)⁻¹
  rw [ModularCurve.heckeOperatorHAlong_diamondHBar_comm, ← ModularCurve.diamondHBar_mul,
    ModularCurve.heckeOperatorHAlong_comm (q ^ 2 * M') (levelH q M') ℓ ℓ', mul_comm a b,
    ModularCurve.diamondHBar_mul, ModularCurve.heckeOperatorHAlong_diamondHBar_comm]

variable {q M'} in
theorem heckeJac_heckeGen' {ℓ : ℕ} (hℓ : ℓ.Prime) :
    heckeJac q M' (heckeGen ⟨ℓ, hℓ⟩) = heckeGenJac q M' ℓ :=
  heckeJac_heckeGen (heckeGenCommute q M') ⟨ℓ, hℓ⟩

end HeckeCommute

section EvalTate

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} {lam : ℕ}

def evalTate (ζ : Idx q) (x : TateModule lam (Jac q M')) : TateModule lam (jacComp q M') :=
  ⟨fun n => ((x : ℕ → Jac q M') n).eval ζ, fun n =>
    ⟨by rw [← Jac.eval_zsmul, TateModule.torsion, Jac.eval_zero],
     by rw [← Jac.eval_zsmul, TateModule.compat]⟩⟩

omit [Fact q.Prime] in
@[scoped simp] theorem evalTate_apply (ζ : Idx q) (x : TateModule lam (Jac q M')) (n : ℕ) :
    ((evalTate ζ x : TateModule lam (jacComp q M')) : ℕ → jacComp q M') n = ((x : ℕ → Jac q M') n).eval ζ :=
  rfl

end EvalTate

section Main

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime]

scoped instance : NeZero (q ^ 2 * M') :=
  ⟨Nat.mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩

theorem main (hG : GL2Laws q M')
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ.Coprime q) (hℓM' : ¬ ℓ ∣ M') (hℓlam : ℓ ≠ lam)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime ℓ)
    (σ : Gal) (hσ : P.IsFrobeniusAt σ ℓ) :
    tateGal q M' lam σ * tateGal q M' lam σ
      - tateHecke q M' lam (heckeGen ⟨ℓ, hℓ⟩) * tateGal q M' lam σ
      + (ℓ : ℤ_[lam]) • tateGL2 q M' lam (CuspidalType.scalarElem q (ZMod.unitOfCoprime ℓ hℓq)) = 0 := by

  have hℓqM' : ¬ ℓ ∣ q * M' := by
    intro h
    rcases (Nat.Prime.dvd_mul hℓ).1 h with h2 | h2
    · exact (Nat.Prime.coprime_iff_not_dvd hℓ).1 hℓq h2
    · exact hℓM' h2
  have hN : ℓ.Coprime (q ^ 2 * M') := coprime_level_of_not_dvd q M' hℓ hℓqM'
  have hℓN : ¬ ℓ ∣ q ^ 2 * M' := not_dvd_level_of_coprime q M' hℓ hN
  have hin := ModularCurve.heckeDiamondInputsHAll (q ^ 2 * M') (levelH q M')

  refine LinearMap.ext fun x => ?_
  rw [LinearMap.zero_apply, LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
    Module.End.mul_apply, LinearMap.smul_apply]
  refine Subtype.ext (funext fun n => ?_)
  rw [TateModule.coe_add, TateModule.coe_sub, TateModule.coe_zero, Pi.add_apply, Pi.sub_apply,
    Pi.zero_apply, TateModule.natCast_padicInt_smul_apply, tateGal_apply_coe, tateGal_apply_coe,
    tateHecke_apply_coe, tateGal_apply_coe, tateGL2_apply_coe, heckeJac_heckeGen' hℓ]
  refine Jac.ext fun ζ => ?_
  rw [Jac.eval_add, Jac.eval_sub, Jac.eval_zsmul, Jac.eval_zero, galJac_eval, galJac_eval,
    heckeGenJac_eval hℓ hℓqM' hℓq hN, galJac_eval,
    ModularCurve.FullLevel.eval_gl2Jac_scalarElem_eq_diamondHBar_inv_eval_pow q M' hG ℓ hℓq hN,
    frob_inv_smul hℓq P hP σ hσ ζ, frob_inv_smul hℓq P hP σ hσ (ζ.pow (ZMod.unitOfCoprime ℓ hℓq)⁻¹),
    Idx.pow_pow, ← mul_inv, ← pow_two, natCast_zsmul]

  have key := frobeniusQuadratic_diaInv_level (q ^ 2 * M') lam (levelH q M') (∅ : Set ℕ) hin hℓ
    (Set.notMem_empty ℓ) hℓN hℓlam P hP σ hσ
    (evalTate (ζ.pow ((ZMod.unitOfCoprime ℓ hℓq) ^ 2)⁻¹) x) n
  rw [genOpH_T, evalTate_apply] at key
  exact key

end Main

end W6ES
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGal_sub_tateHecke_mul_tateGal_add_smul_tateGL2_scalarElem_eq_zero.W6ES"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGal_sub_tateHecke_mul_tateGal_add_smul_tateGL2_scalarElem_eq_zero.W6ES"

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime]
    (hG : ModularCurve.FullLevel.GL2Laws q M')
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ.Coprime q) (hℓM' : ¬ ℓ ∣ M') (hℓlam : ℓ ≠ lam)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : P.IsFrobeniusAt σ ℓ) :
    ModularCurve.FullLevel.tateGal q M' lam σ * ModularCurve.FullLevel.tateGal q M' lam σ
      - ModularCurve.FullLevel.tateHecke q M' lam (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)
          * ModularCurve.FullLevel.tateGal q M' lam σ
      + (ℓ : ℤ_[lam]) • ModularCurve.FullLevel.tateGL2 q M' lam
          (CuspidalType.scalarElem q (ZMod.unitOfCoprime ℓ hℓq)) = 0 :=
  W6ES.main q M' lam hG hℓ hℓq hℓM' hℓlam P hP σ hσ

end S_ModularCurve_FullLevel_tateGal_mul_tateGal_sub_tateHecke_mul_tateGal_add_smul_tateGL2_scalarElem_eq_zero
end P2MW
export P2MW.S_ModularCurve_FullLevel_tateGal_mul_tateGal_sub_tateHecke_mul_tateGal_add_smul_tateGL2_scalarElem_eq_zero (solution)
