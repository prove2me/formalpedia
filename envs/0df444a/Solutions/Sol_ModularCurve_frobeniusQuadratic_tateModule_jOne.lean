-- Prove2me | solution 1 for ModularCurve.frobeniusQuadratic_tateModule_jOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/263fecc8-3de1-5e6e-9606-04fdf2ec96b8

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt
import Theorems.Thm_ModularCurve_reductionQExpModL_gamma1_heckeOperatorOneBar
import Theorems.Thm_ModularCurve_heckeDiamondInputsAll
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
import Theorems.Thm_ModularCurve_qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_frobeniusQuadratic_tateModule_jOne
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CellDissection.fintypeV"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X"
p2m_attr_erase "simp" "CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap"
p2m_attr_erase "simp" "KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"
p2m_attr_erase "simp" "WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"
p2m_attr_erase "simp" "FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq"
p2m_attr_erase "simp" "NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "HeckeAlgOne heckeGenOne diamondGen heckeOperatorOneBar HeckeDiamondCommuteBar HeckeDiamondInputsAll heckeModuleOneBar heckeModuleOneBar_heckeGenOne_smul heckeModuleOneBar_diamondGen_smul qExpFunctionFieldC JOne JOneC arithmeticRingAut coe_arithmeticRingAut_apply arithmeticRingAut_algebraMap arithmeticGalois galois_smul_pic0_def coeffMap_coeffMap coeffMap_id coeffMap_congr coeffEmb coeffMap_coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange IsBaseChangeAutOf baseChangeAut isBaseChangeAutOf_baseChangeAut baseChangeAut_of_not diamondAutBar diamondOneBar diamondOneBar_apply ReductionInputsQExpModL reductionQExpModL qExpFrobeniusPushforwardModL qExpFrobeniusPullbackModL GammaH_bot xHFunctionFieldC JH exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd reductionQExpModL_gammaH_smul_of_isFrobeniusAt reductionQExpModL_gamma1_heckeOperatorOneBar heckeDiamondInputsAll eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental"
namespace A2JOneFrobQuad
p2m_open "ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_frobeniusQuadratic_tateModule_jOne.ModularCurve AlgebraicCurve IntermediateField"

section Commute

variable {L : Type*} [Field L] [Algebra ℚ L] {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

def conjAlgHom (σ : L ≃ₐ[ℚ] L) (τ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀) :
    laurentBaseChange L F₀ →ₐ[L] laurentBaseChange L F₀ :=
  { (((arithmeticRingAut F₀ σ.symm).trans (τ : laurentBaseChange L F₀ ≃+* laurentBaseChange L F₀)).trans
      (arithmeticRingAut F₀ σ)).toRingHom with
    commutes' := fun c => by
      show arithmeticRingAut F₀ σ (τ (arithmeticRingAut F₀ σ.symm (algebraMap L _ c))) = algebraMap L _ c
      rw [arithmeticRingAut_algebraMap, AlgEquiv.commutes, arithmeticRingAut_algebraMap,
        AlgEquiv.apply_symm_apply] }

theorem conjAlgHom_apply (σ : L ≃ₐ[ℚ] L) (τ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀)
    (x : laurentBaseChange L F₀) :
    conjAlgHom σ τ x = arithmeticRingAut F₀ σ (τ (arithmeticRingAut F₀ σ.symm x)) :=
  rfl

theorem arithmeticRingAut_comm_of_isBaseChangeAutOf {σ₀ : F₀ ≃ₐ[ℚ] F₀}
    {τ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀} (hτ : IsBaseChangeAutOf L σ₀ τ)
    (σ : L ≃ₐ[ℚ] L) (x : laurentBaseChange L F₀) :
    arithmeticRingAut F₀ σ (τ x) = τ (arithmeticRingAut F₀ σ x) := by

  have key : conjAlgHom σ τ = τ.toAlgHom := by
    refine IntermediateField.adjoin_algHom_ext L fun y hy => ?_
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    show arithmeticRingAut F₀ σ (τ (arithmeticRingAut F₀ σ.symm ⟨coeffEmb L y₀, _⟩)) = τ ⟨coeffEmb L y₀, _⟩

    have h1 : arithmeticRingAut F₀ σ.symm ⟨coeffEmb L y₀, coeffEmb_mem_laurentBaseChange L hy₀⟩ =
        ⟨coeffEmb L y₀, coeffEmb_mem_laurentBaseChange L hy₀⟩ :=
      Subtype.ext (coeffMap_coeffEmb σ.symm y₀)
    rw [h1]

    have h2 := hτ ⟨y₀, hy₀⟩
    refine Subtype.ext ?_
    rw [coe_arithmeticRingAut_apply, h2, coeffMap_coeffEmb]
  have h := congrArg (fun φ : laurentBaseChange L F₀ →ₐ[L] laurentBaseChange L F₀ =>
    φ (arithmeticRingAut F₀ σ x)) key
  simp only [conjAlgHom_apply, AlgEquiv.toAlgHom_apply] at h
  rw [← h]
  congr 2
  exact Subtype.ext (by
    rw [coe_arithmeticRingAut_apply, coe_arithmeticRingAut_apply, coeffMap_coeffMap,
      coeffMap_congr (g := RingHom.id L) (RingHom.ext fun a => σ.symm_apply_apply a), coeffMap_id])

theorem arithmeticGalois_mul_ofAlgAut_baseChangeAut (σ₀ : F₀ ≃ₐ[ℚ] F₀) (σ : L ≃ₐ[ℚ] L) :
    arithmeticGalois F₀ σ * SemilinearAut.ofAlgAut (baseChangeAut L σ₀) =
      SemilinearAut.ofAlgAut (baseChangeAut L σ₀) * arithmeticGalois F₀ σ := by
  rcases Classical.em
      (∃ τ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀, IsBaseChangeAutOf L σ₀ τ) with h | h
  · have hτ := isBaseChangeAutOf_baseChangeAut h
    refine Subtype.ext (Prod.ext (RingEquiv.ext fun x => ?_) ?_)
    · exact arithmeticRingAut_comm_of_isBaseChangeAutOf hτ σ x
    · show σ.toRingEquiv * 1 = 1 * σ.toRingEquiv
      rw [mul_one, one_mul]
  · rw [baseChangeAut_of_not h, show (AlgEquiv.refl : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀)
      = 1 from rfl, map_one, mul_one, one_mul]

end Commute

theorem smul_diamondOneBar (M d : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (z : JOne M) :
    σ • diamondOneBar M d z = diamondOneBar M d (σ • z) := by
  rw [diamondOneBar_apply, diamondOneBar_apply, galois_smul_pic0_def, galois_smul_pic0_def,
    ← mul_smul, ← mul_smul, diamondAutBar, arithmeticGalois_mul_ofAlgAut_baseChangeAut]

section Transport

variable (M : ℕ) [NeZero M] {ℓ : ℕ} [Fact ℓ.Prime]
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hℓM : ¬ ℓ ∣ M) (hA : A.LiesOverPrime ℓ)

include hℓM hA

set_option synthInstance.maxHeartbeats 1600000 in

theorem D1_gamma1 :
    (∃ x : qExpFunctionFieldC (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma1 M),
        Transcendental (IsLocalRing.ResidueField A) x ∧
          FiniteDimensional
            (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              ({x} : Set (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma1 M))))
            (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma1 M))) ∧
      ReductionInputsQExpModL A (CongruenceSubgroup.Gamma1 M) := by
  have h := exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd M ⊥ hℓM A hA
  rw [xHFunctionFieldC, GammaH_bot] at h
  exact h

set_option synthInstance.maxHeartbeats 1600000 in

theorem D2_gamma1 [CharP (IsLocalRing.ResidueField A) ℓ]
    (h : ReductionInputsQExpModL A (CongruenceSubgroup.Gamma1 M))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) (z : JOne M) :
    reductionQExpModL A (CongruenceSubgroup.Gamma1 M) (σ • z) =
      qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma1 M) ℓ
        (reductionQExpModL A (CongruenceSubgroup.Gamma1 M) z) := by
  have key : ∀ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ), Γ = CohCarrier.GammaH M ⊥ →
      ∀ (hΓ : ReductionInputsQExpModL A Γ)
        (w : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))),
        reductionQExpModL A Γ (σ • w) =
          qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A) Γ ℓ (reductionQExpModL A Γ w) := by
    rintro Γ rfl hΓ w
    exact reductionQExpModL_gammaH_smul_of_isFrobeniusAt M ⊥ hℓM A hA hΓ σ hσ w
  exact key (CongruenceSubgroup.Gamma1 M) (GammaH_bot M).symm h z

set_option synthInstance.maxHeartbeats 1600000 in

theorem D4_gamma1 (h : ReductionInputsQExpModL A (CongruenceSubgroup.Gamma1 M))
    (m : ℕ) (hm : ¬ ℓ ∣ m) (z : JOne M) (hmz : m • z = 0)
    (hz : reductionQExpModL A (CongruenceSubgroup.Gamma1 M) z = 0) : z = 0 := by
  have key : ∀ Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ), Γ = CohCarrier.GammaH M ⊥ →
      ∀ (hΓ : ReductionInputsQExpModL A Γ)
        (w : Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))),
        m • w = 0 → reductionQExpModL A Γ w = 0 → w = 0 := by
    rintro Γ rfl hΓ w hmw hw
    exact eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero M ⊥ hℓM A hA hΓ m hm w hmw hw
  exact key (CongruenceSubgroup.Gamma1 M) (GammaH_bot M).symm h z hmz hz

end Transport

theorem map_quadratic_eq_zero {J Jb : Type*} [AddCommGroup J] [AddCommGroup Jb]
    (red : J →+ Jb) (s T Dm : J → J) (Fr V : Jb → Jb) (ℓ : ℕ)
    (hcomm : ∀ w, s (Dm w) = Dm (s w))
    (hs : ∀ w, red (s w) = Fr (red w))
    (hT : ∀ w, red (T w) = Fr (red (Dm w)) + V (red w))
    (hE : ∀ y, V (Fr y) = ℓ • y) (z : J) :
    red (Dm (s (s z)) - T (s z) + ℓ • z) = 0 := by
  rw [map_add, map_sub, map_nsmul, ← hcomm, hs, hT, hs, hE]
  abel

set_option synthInstance.maxHeartbeats 1600000 in

theorem torsion_key (M : ℕ) [NeZero M] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) (hℓM : ¬ ℓ ∣ M)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ)
    (z : JOne M) (m : ℕ) (hm : ¬ ℓ ∣ m) (hz : m • z = 0) :
    diamondOneBar M ℓ (σ • σ • z) - heckeOperatorOneBar M ⟨ℓ, hℓ⟩ (σ • z) + ℓ • z = 0 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP (IsLocalRing.ResidueField A) ℓ := A.charP_residueField_of_liesOverPrime_def hℓ hA

  obtain ⟨hcurve, hred⟩ := D1_gamma1 M A hℓM hA

  refine D4_gamma1 M A hℓM hA hred m hm _ ?_ ?_
  ·
    have h0 : σ • (0 : JOne M) = 0 := smul_zero (A := JOne M) σ
    have h1 : m • diamondOneBar M ℓ (σ • σ • z) = 0 := by
      rw [← map_nsmul, smul_comm, smul_comm m σ z, hz, h0, h0, map_zero]
    have h2 : m • heckeOperatorOneBar M ⟨ℓ, hℓ⟩ (σ • z) = 0 := by
      rw [← map_nsmul, smul_comm, hz, h0, map_zero]
    have h3 : m • (ℓ • z) = 0 := by
      rw [smul_comm, hz, smul_zero]
    rw [nsmul_add, nsmul_sub, h1, h2, h3, sub_zero, add_zero]
  ·
    exact map_quadratic_eq_zero (reductionQExpModL A (CongruenceSubgroup.Gamma1 M)) (σ • ·)
      (heckeOperatorOneBar M ⟨ℓ, hℓ⟩) (diamondOneBar M ℓ)
      (qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma1 M) ℓ)
      (qExpFrobeniusPullbackModL (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma1 M) ℓ) ℓ
      (fun w => smul_diamondOneBar M ℓ σ w)
      (fun w => D2_gamma1 M A hℓM hA hred σ hσ w)
      (fun w => reductionQExpModL_gamma1_heckeOperatorOneBar M hℓM A hA (heckeDiamondInputsAll M) hred w)
      (fun y => qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental
        (IsLocalRing.ResidueField A) (CongruenceSubgroup.Gamma1 M) hcurve y) z

end ModularCurve.A2JOneFrobQuad

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_frobeniusQuadratic_tateModule_jOne.ModularCurve in
theorem solution (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓMp : ¬ ℓ ∣ M * p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ)
    (x : TateModule p (ModularCurve.JOne M)) :
    letI := ModularCurve.heckeModuleOneBar M
    TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne (ModularCurve.diamondGen ℓ)
        (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
          (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x))
      - TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne
          (ModularCurve.heckeGenOne ⟨ℓ, hℓ⟩)
          (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
      + ℓ • x = 0 := by
  letI := ModularCurve.heckeModuleOneBar M
  have hℓM : ¬ ℓ ∣ M := fun h => hℓMp (dvd_mul_of_dvd_left h p)
  have hℓp : ¬ ℓ ∣ p := fun h => hℓMp (dvd_mul_of_dvd_right h M)

  refine Subtype.ext (funext fun n => ?_)
  change (diamondGen ℓ : HeckeAlgOne) • (σ • σ • (x : ℕ → JOne M) n)
      - (heckeGenOne ⟨ℓ, hℓ⟩ : HeckeAlgOne) • (σ • (x : ℕ → JOne M) n) + ℓ • (x : ℕ → JOne M) n = 0

  rw [heckeModuleOneBar_heckeGenOne_smul hcomm, heckeModuleOneBar_diamondGen_smul hcomm]

  have hz : (p ^ n : ℕ) • (x : ℕ → JOne M) n = 0 := by
    rw [← natCast_zsmul]
    exact TateModule.torsion x n
  have hℓpn : ¬ ℓ ∣ p ^ n := fun h => hℓp (hℓ.dvd_of_dvd_pow h)
  exact A2JOneFrobQuad.torsion_key M hℓ A hA hℓM σ hσ _ (p ^ n) hℓpn hz

end S_ModularCurve_frobeniusQuadratic_tateModule_jOne
end P2MW
export P2MW.S_ModularCurve_frobeniusQuadratic_tateModule_jOne (solution)
