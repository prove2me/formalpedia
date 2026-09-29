-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a442171c-8bfc-5359-a22f-c3f6b17c04f0

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_JacJ1_ChartAlgebra
import Definitions.Def_CohCarrier_Level
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_exists_algHom_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_injective_isIntegrallyClosed
import Theorems.Thm_ModularCurve_exists_gaussIntegral_lift_isIntegral_of_isIntegral_qExpFunctionFieldC_residueField_of_not_dvd
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
import Theorems.Thm_ModularCurve_chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isDomain_tensorProduct_chartAlg_of_finrank_le_finrank_adjoin_range
import Theorems.Thm_ModularCurve_exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime
import Theorems.Thm_CohCarrier_exists_eq_gammaH_of_gamma1_le_of_le_gamma0
import Theorems.Thm_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one"
p2m_attr_erase "simp" "ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun"
p2m_attr_erase "simp" "KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option maxHeartbeats 6400000

open scoped MatrixGroups TensorProduct
p2m_open "AlgebraicCurve~genus ModularCurve P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing.ModularCurve IsLocalRing"

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace FibreIsoAux

theorem mem_of_isIntegral_of_mul_mem {T : Type*} [Field T] (R : Subring T) [IsIntegrallyClosed R]
    (x : T) (r₁ r₂ : R) (hr₁ : r₁ ≠ 0) (hx : (r₁ : T) * x = r₂) (hint : IsIntegral R x) : x ∈ R := by
  classical
  let K := FractionRing R
  have hinj : Function.Injective (algebraMap R T) := Subtype.val_injective
  let lift : K →+* T := IsFractionRing.lift hinj
  have hlift : ∀ r : R, lift (algebraMap R K r) = (r : T) := fun r => IsFractionRing.lift_algebraMap hinj r
  have hliftinj : Function.Injective lift := lift.injective

  let z : K := algebraMap R K r₂ / algebraMap R K r₁
  have hr₁K : algebraMap R K r₁ ≠ 0 :=
    fun h => hr₁ ((IsFractionRing.injective R K) (by rw [h, map_zero]))
  have hz : lift z = x := by
    have hr₁T : (r₁ : T) ≠ 0 := fun h => hr₁ (Subtype.ext h)
    rw [map_div₀, hlift, hlift]
    field_simp
    rw [← hx, mul_comm]

  have hzint : IsIntegral R z := by
    obtain ⟨p, hp, hpx⟩ := hint
    refine ⟨p, hp, ?_⟩
    apply hliftinj
    rw [Polynomial.hom_eval₂, hz, map_zero]
    have : lift.comp (algebraMap R K) = algebraMap R T := RingHom.ext hlift
    rw [this]
    exact hpx
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hzint
  have : (r : T) = x := by rw [← hlift r, hr, hz]
  rw [← this]
  exact r.2

end FibreIsoAux

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC jNum constantCoeff_jNum jq coeffMap coeffMap_single coeffMap_id coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC map_jqModC exists_algHom_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_injective_isIntegrallyClosed exists_gaussIntegral_lift_isIntegral_of_isIntegral_qExpFunctionFieldC_residueField_of_not_dvd exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq"
namespace FisoK
p2m_open "ModularCurve"

variable (Γ : Subgroup SL(2, ℤ)) (ℓ : ℕ) [Fact ℓ.Prime]
variable (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "Qb" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FN" => ↥(qExpFunctionFieldC ℚ Γ)
set_option quotPrecheck false in
local notation "TT" => ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))
set_option quotPrecheck false in
local notation "kA" => ResidueField ↥A

omit [Fact ℓ.Prime] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A] in

abbrev constantsHom' : ↥A →+* TT :=
  (algebraMap (AlgebraicClosure ℚ) TT).comp A.subtype

omit [Fact ℓ.Prime] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A] in
@[scoped simp] theorem coe_constantsHom' (a : ↥A) : (constantsHom' Γ A a : LaurentSeries Qb) = algebraMap Qb (LaurentSeries Qb) (a : Qb) := rfl

section Generic

variable (S : Subalgebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥(qExpFunctionFieldC ℚ Γ))

def AS : Type := ↥A ⊗[ℤℓ] S

scoped instance : CommRing (AS Γ ℓ A S) := Algebra.TensorProduct.instCommRing
scoped instance : Algebra ↥A (AS Γ ℓ A S) := Algebra.TensorProduct.leftAlgebra

def asEquiv : (↥A ⊗[ℤℓ] S) ≃ₐ[↥A] AS Γ ℓ A S := AlgEquiv.refl

def e3 : kA ⊗[ℤℓ] S ≃ₐ[↥A] (AS Γ ℓ A S) ⧸ (maximalIdeal ↥A).map (algebraMap ↥A (AS Γ ℓ A S)) :=
  Algebra.TensorProduct.quotientTensorEquiv (R := ℤℓ) ↥A S ↥A (maximalIdeal ↥A)

theorem e3_tmul (a : ↥A) (b : S) :
    e3 Γ ℓ A S (residue ↥A a ⊗ₜ b) = Ideal.Quotient.mk _ (asEquiv Γ ℓ A S (a ⊗ₜ b)) :=
  Algebra.TensorProduct.quotientTensorEquiv_apply_tmul (R := ℤℓ) ↥A S ↥A (maximalIdeal ↥A) a b

theorem isDomain_quot (h : IsDomain (kA ⊗[ℤℓ] S)) :
    IsDomain ((AS Γ ℓ A S) ⧸ (maximalIdeal ↥A).map (algebraMap ↥A (AS Γ ℓ A S))) :=
  MulEquiv.isDomain (kA ⊗[ℤℓ] S) (e3 Γ ℓ A S).toMulEquiv.symm

variable [Algebra ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))]

theorem b2 (L : Type) [Field L]
    (ψ : AS Γ ℓ A S →ₐ[↥A] TT) (hinj : Function.Injective ψ)
    (B : Subring TT) (hψB : ∀ t, ψ t ∈ B) (hBψ : ∀ x ∈ B, ∃ t, ψ t = x)
    (π : ↥B →+* L)
    (hker : RingHom.ker π =
      Ideal.span ((fun a : ↥A => (⟨ψ (algebraMap ↥A _ a), hψB _⟩ : ↥B)) '' (maximalIdeal ↥A : Set ↥A))) :
    ∃ Pr : AS Γ ℓ A S →+* L, (∀ t, Pr t = π ⟨ψ t, hψB t⟩) ∧ Pr.range = π.range ∧
      RingHom.ker Pr = (maximalIdeal ↥A).map (algebraMap ↥A (AS Γ ℓ A S)) := by
  classical

  let ψB : AS Γ ℓ A S →+* ↥B := (ψ.toRingHom).codRestrict B hψB
  have hbij : Function.Bijective ψB :=
    ⟨fun x y h => hinj (congrArg Subtype.val h), fun x => by
      obtain ⟨t, ht⟩ := hBψ x x.2
      exact ⟨t, Subtype.ext ht⟩⟩
  let ρψ : AS Γ ℓ A S ≃+* ↥B := RingEquiv.ofBijective ψB hbij
  have hρψ : ∀ t, (ρψ t : TT) = ψ t := fun t => rfl
  let Pr : AS Γ ℓ A S →+* L := π.comp ρψ.toRingHom
  refine ⟨Pr, fun t => rfl, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨ρψ t, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨ρψ.symm x, ?_⟩
      change π (ρψ (ρψ.symm x)) = π x
      rw [RingEquiv.apply_symm_apply]
  · have h1 : RingHom.ker Pr = (RingHom.ker π).comap ρψ := by
      ext t
      rfl
    rw [h1, hker, ← Ideal.map_symm, Ideal.map_span]
    have himg : (ρψ.symm : ↥B → AS Γ ℓ A S) ''
        ((fun a : ↥A => (⟨ψ (algebraMap ↥A _ a), hψB _⟩ : ↥B)) '' (maximalIdeal ↥A : Set ↥A)) =
        (algebraMap ↥A (AS Γ ℓ A S)) '' (maximalIdeal ↥A : Set ↥A) := by
      rw [Set.image_image]
      refine Set.image_congr fun a _ => ?_
      change ρψ.symm _ = algebraMap ↥A (AS Γ ℓ A S) a
      apply ρψ.injective
      rw [RingEquiv.apply_symm_apply]
      rfl
    rw [himg]
    rfl

omit [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A] in

theorem exists_denom (s : Finset Qb) : ∃ d : ↥A, d ≠ 0 ∧ ∀ q ∈ s, (d : Qb) * q ∈ A := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, fun q hq => absurd hq (by simp)⟩
  | insert q s hqs ih =>
    obtain ⟨d, hd0, hd⟩ := ih
    rcases A.mem_or_inv_mem q with hq | hq
    · refine ⟨d, hd0, fun r hr => ?_⟩
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact A.mul_mem _ _ d.2 hq
      · exact hd r hr
    · by_cases hq0 : q = 0
      · refine ⟨d, hd0, fun r hr => ?_⟩
        rcases Finset.mem_insert.mp hr with rfl | hr
        · rw [hq0, mul_zero]; exact A.zero_mem
        · exact hd r hr
      · refine ⟨⟨(d : Qb) * q⁻¹, A.mul_mem _ _ d.2 hq⟩, ?_, fun r hr => ?_⟩
        · intro h
          have h' : (d : Qb) * q⁻¹ = 0 := congrArg Subtype.val h
          rcases mul_eq_zero.mp h' with h1 | h1
          · exact hd0 (Subtype.ext h1)
          · exact hq0 (inv_eq_zero.mp h1)
        · rcases Finset.mem_insert.mp hr with rfl | hr
          · change (d : Qb) * r⁻¹ * r ∈ A
            rw [inv_mul_cancel_right₀ hq0]
            exact d.2
          · change (d : Qb) * q⁻¹ * r ∈ A
            rw [mul_assoc, mul_comm q⁻¹, ← mul_assoc]
            exact A.mul_mem _ _ (hd r hr) hq

def embS (b : S) : TT :=
  ⟨coeffEmb Qb ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange Qb (b : ↥(qExpFunctionFieldC ℚ Γ)).2⟩

omit [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A] in
@[scoped simp] theorem coe_embS (b : S) :
    (embS Γ ℓ S b : LaurentSeries Qb) = coeffEmb Qb ((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) := rfl

theorem b1 (ψ : AS Γ ℓ A S →ₐ[↥A] TT) (hIC : IsIntegrallyClosed ↥ψ.range)
    (hψ : ∀ (a : ↥A) (b : S), ψ (asEquiv Γ ℓ A S (a ⊗ₜ b)) = algebraMap ↥A TT a * embS Γ ℓ S b)
    (hcT : ∀ a : ↥A, algebraMap ↥A TT a = constantsHom' Γ A a)
    (g : TT)
    (base : Subring TT) (hbase : base ≤ (Algebra.adjoin Qb ({g} : Set TT)).toSubring)
    (hbase' : ∀ x ∈ base, ∃ t, ψ t = x)
    (B : Subring TT)
    (hBint : ∀ b : ↥B, ∃ p : Polynomial ↥base, p.Monic ∧ Polynomial.eval₂ base.subtype (b : TT) p = 0)
    (hSB : ∀ b : S, embS Γ ℓ S b ∈ B) (hconstB : ∀ a : ↥A, constantsHom' Γ A a ∈ B)
    (hspan : (CurveModel.chartRing Qb ({g} : Set TT)).toSubmodule ≤
      Submodule.span Qb (Set.range (embS Γ ℓ S))) :
    ∀ x : TT, x ∈ B ↔ ∃ t, ψ t = x := by
  classical
  have hconst : ∀ a : ↥A, algebraMap ↥A TT a = algebraMap Qb TT (a : Qb) := fun a => by
    rw [hcT]; rfl
  intro x
  constructor
  · intro hxB

    obtain ⟨p, hp, hpx⟩ := hBint ⟨x, hxB⟩
    let incl : ↥base →+* ↥(Algebra.adjoin Qb ({g} : Set TT)) :=
      { toFun := fun y => ⟨y, hbase y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    have hint : IsIntegral (Algebra.adjoin Qb ({g} : Set TT)) x := by
      refine ⟨p.map incl, hp.map incl, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hpx
    have hxchart : x ∈ CurveModel.chartRing Qb ({g} : Set TT) := hint

    have hxspan : x ∈ Submodule.span Qb (Set.range (embS Γ ℓ S)) := hspan hxchart
    obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hxspan

    obtain ⟨d, hd0, hd⟩ := exists_denom A (c.support.image c)
    have hdc : ∀ b ∈ c.support, (d : Qb) * c b ∈ A := fun b hb => hd _ (Finset.mem_image_of_mem c hb)

    have hy : ∃ t, ψ t = algebraMap ↥A TT d * x := by
      refine ⟨asEquiv Γ ℓ A S (∑ b ∈ c.support.attach,
        (⟨(d : Qb) * c b.1, hdc b.1 b.2⟩ : ↥A) ⊗ₜ (b.1 : S)), ?_⟩
      have e1 : ψ (asEquiv Γ ℓ A S (∑ b ∈ c.support.attach,
          (⟨(d : Qb) * c b.1, hdc b.1 b.2⟩ : ↥A) ⊗ₜ (b.1 : S))) =
          ∑ b ∈ c.support.attach, algebraMap ↥A TT d * (c b.1 • embS Γ ℓ S b.1) := by
        rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [hψ, Algebra.smul_def, ← mul_assoc, hconst, hconst]
        congr 1
        change algebraMap Qb TT ((d : Qb) * c b.1) = _
        rw [map_mul]
      have e2 : algebraMap ↥A TT d * x =
          ∑ b ∈ c.support.attach, algebraMap ↥A TT d * (c b.1 • embS Γ ℓ S b.1) := by
        rw [← hc, Finsupp.sum, Finset.mul_sum]
        exact (Finset.sum_attach c.support (fun b => algebraMap ↥A TT d * (c b • embS Γ ℓ S b))).symm
      exact e1.trans e2.symm

    let R : Subring TT := ψ.range.toSubring
    haveI : IsIntegrallyClosed ↥R := hIC
    have hd_mem : algebraMap ↥A TT d ∈ R := ⟨algebraMap ↥A _ d, ψ.commutes d⟩
    obtain ⟨t, ht⟩ := hy
    have hy_mem : algebraMap ↥A TT d * x ∈ R := ⟨t, ht⟩
    have hr₁ : (⟨algebraMap ↥A TT d, hd_mem⟩ : ↥R) ≠ 0 := by
      intro h
      have h' : algebraMap ↥A TT d = 0 := congrArg Subtype.val h
      rw [hconst] at h'
      exact hd0 (Subtype.ext ((algebraMap Qb TT).injective (h'.trans (map_zero _).symm)))
    let incl' : ↥base →+* ↥R :=
      { toFun := fun y => ⟨y, by obtain ⟨t, ht⟩ := hbase' y y.2; exact ⟨t, ht⟩⟩,
        map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
    have hintR : IsIntegral ↥R x := by
      refine ⟨p.map incl', hp.map incl', ?_⟩
      rw [Polynomial.eval₂_map]
      exact hpx
    have hxR : x ∈ R := FibreIsoAux.mem_of_isIntegral_of_mul_mem R x ⟨algebraMap ↥A TT d, hd_mem⟩
      ⟨algebraMap ↥A TT d * x, hy_mem⟩ hr₁ rfl hintR
    exact hxR
  · rintro ⟨t, rfl⟩
    change ψ t ∈ B
    induction t using TensorProduct.induction_on with
    | zero =>
      convert B.zero_mem
      exact map_zero ψ
    | tmul a b =>
      have := hψ a b
      change ψ (a ⊗ₜ b) = _ at this
      rw [this, hcT]
      exact B.mul_mem (hconstB a) (hSB b)
    | add x y hx hy =>
      convert B.add_mem hx hy using 1
      exact map_add ψ x y

theorem b1' (ψ : AS Γ ℓ A S →ₐ[↥A] TT) (hIC : IsIntegrallyClosed ↥ψ.range)
    (hψ : ∀ (a : ↥A) (b : S), ψ (asEquiv Γ ℓ A S (a ⊗ₜ b)) = algebraMap ↥A TT a * embS Γ ℓ S b)
    (hcT : ∀ a : ↥A, algebraMap ↥A TT a = constantsHom' Γ A a)
    (g : TT)
    (base : Subring TT) (hbase : base ≤ (Algebra.adjoin Qb ({g} : Set TT)).toSubring)
    (hbase' : ∀ x ∈ base, ∃ t, ψ t = x)
    (hspan : (CurveModel.chartRing Qb ({g} : Set TT)).toSubmodule ≤
      Submodule.span Qb (Set.range (embS Γ ℓ S)))
    (x : TT) (hx : ∃ p : Polynomial ↥base, p.Monic ∧ Polynomial.eval₂ base.subtype x p = 0) :
    ∃ t, ψ t = x := by
  classical
  have hconst : ∀ a : ↥A, algebraMap ↥A TT a = algebraMap Qb TT (a : Qb) := fun a => by
    rw [hcT]; rfl
  obtain ⟨p, hp, hpx⟩ := hx
  let incl : ↥base →+* ↥(Algebra.adjoin Qb ({g} : Set TT)) :=
    { toFun := fun y => ⟨y, hbase y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hint : IsIntegral (Algebra.adjoin Qb ({g} : Set TT)) x := by
    refine ⟨p.map incl, hp.map incl, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpx
  have hxchart : x ∈ CurveModel.chartRing Qb ({g} : Set TT) := hint
  have hxspan : x ∈ Submodule.span Qb (Set.range (embS Γ ℓ S)) := hspan hxchart
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hxspan
  obtain ⟨d, hd0, hd⟩ := exists_denom A (c.support.image c)
  have hdc : ∀ b ∈ c.support, (d : Qb) * c b ∈ A := fun b hb => hd _ (Finset.mem_image_of_mem c hb)
  have hy : ∃ t, ψ t = algebraMap ↥A TT d * x := by
    refine ⟨asEquiv Γ ℓ A S (∑ b ∈ c.support.attach,
      (⟨(d : Qb) * c b.1, hdc b.1 b.2⟩ : ↥A) ⊗ₜ (b.1 : S)), ?_⟩
    have e1 : ψ (asEquiv Γ ℓ A S (∑ b ∈ c.support.attach,
        (⟨(d : Qb) * c b.1, hdc b.1 b.2⟩ : ↥A) ⊗ₜ (b.1 : S))) =
        ∑ b ∈ c.support.attach, algebraMap ↥A TT d * (c b.1 • embS Γ ℓ S b.1) := by
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hψ, Algebra.smul_def, ← mul_assoc, hconst, hconst]
      congr 1
      change algebraMap Qb TT ((d : Qb) * c b.1) = _
      rw [map_mul]
    have e2 : algebraMap ↥A TT d * x =
        ∑ b ∈ c.support.attach, algebraMap ↥A TT d * (c b.1 • embS Γ ℓ S b.1) := by
      rw [← hc, Finsupp.sum, Finset.mul_sum]
      exact (Finset.sum_attach c.support (fun b => algebraMap ↥A TT d * (c b • embS Γ ℓ S b))).symm
    exact e1.trans e2.symm
  let R : Subring TT := ψ.range.toSubring
  haveI : IsIntegrallyClosed ↥R := hIC
  have hd_mem : algebraMap ↥A TT d ∈ R := ⟨algebraMap ↥A _ d, ψ.commutes d⟩
  obtain ⟨t, ht⟩ := hy
  have hy_mem : algebraMap ↥A TT d * x ∈ R := ⟨t, ht⟩
  have hr₁ : (⟨algebraMap ↥A TT d, hd_mem⟩ : ↥R) ≠ 0 := by
    intro h
    have h' : algebraMap ↥A TT d = 0 := congrArg Subtype.val h
    rw [hconst] at h'
    exact hd0 (Subtype.ext ((algebraMap Qb TT).injective (h'.trans (map_zero _).symm)))
  let incl' : ↥base →+* ↥R :=
    { toFun := fun y => ⟨y, by obtain ⟨t, ht⟩ := hbase' y y.2; exact ⟨t, ht⟩⟩,
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hintR : IsIntegral ↥R x := by
    refine ⟨p.map incl', hp.map incl', ?_⟩
    rw [Polynomial.eval₂_map]
    exact hpx
  have hxR : x ∈ R := FibreIsoAux.mem_of_isIntegral_of_mul_mem R x ⟨algebraMap ↥A TT d, hd_mem⟩
    ⟨algebraMap ↥A TT d * x, hy_mem⟩ hr₁ rfl hintR
  exact hxR

theorem b4 (B base : Subring TT) (hbaseB : base ≤ B) (g : TT)
    (hbase_le : base ≤ Subring.closure (Set.range (constantsHom' Γ A) ∪ {g}))
    (hgen : Set.range (constantsHom' Γ A) ∪ {g} ⊆ (base : Set TT))
    (hBint : ∀ b : ↥B, ∃ p : Polynomial ↥base, p.Monic ∧ Polynomial.eval₂ base.subtype (b : TT) p = 0)
    (Lk : Type) [Field Lk] [Algebra kA Lk] (π : ↥B →+* Lk) (h : Lk)
    (hgB : g ∈ B) (hπg : π ⟨g, hgB⟩ = h)
    (hcB : ∀ a : ↥A, constantsHom' Γ A a ∈ B)
    (hπc : ∀ a : ↥A, π ⟨constantsHom' Γ A a, hcB a⟩ = algebraMap kA Lk (residue ↥A a))
    (hIC : ∀ y : Lk, (∃ p : Polynomial ↥π.range, p.Monic ∧ Polynomial.eval₂ π.range.subtype y p = 0) →
      y ∈ π.range) :
    ∀ y : Lk, y ∈ π.range ↔ IsIntegral (Algebra.adjoin kA ({h} : Set Lk)) y := by
  classical
  set R₀ := Algebra.adjoin kA ({h} : Set Lk) with hR₀
  have hsB : ∀ y ∈ Subring.closure (Set.range (constantsHom' Γ A) ∪ {g}), y ∈ B :=
    fun y hy => hbaseB (Subring.closure_le.mpr hgen hy)

  have hland : ∀ (y : TT) (hy : y ∈ Subring.closure (Set.range (constantsHom' Γ A) ∪ {g}))
      (hyB : y ∈ B), π ⟨y, hyB⟩ ∈ R₀ := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem y hy =>
      intro hyB
      rcases hy with ⟨a, rfl⟩ | hy
      · rw [show π ⟨constantsHom' Γ A a, hyB⟩ = π ⟨constantsHom' Γ A a, hcB a⟩ from rfl, hπc]
        exact Subalgebra.algebraMap_mem _ _
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        rw [show π ⟨y, hyB⟩ = π ⟨y, hgB⟩ from rfl, hπg]
        exact Algebra.subset_adjoin rfl
    | zero => intro hyB; rw [show (⟨0, hyB⟩ : ↥B) = 0 from rfl, map_zero]; exact zero_mem _
    | one => intro hyB; rw [show (⟨1, hyB⟩ : ↥B) = 1 from rfl, map_one]; exact one_mem _
    | add x z hx hz ihx ihz =>
      intro hB
      rw [show (⟨x + z, hB⟩ : ↥B) = ⟨x, hsB x hx⟩ + ⟨z, hsB z hz⟩ from rfl, map_add]
      exact add_mem (ihx _) (ihz _)
    | neg x hx ihx =>
      intro hB
      rw [show (⟨-x, hB⟩ : ↥B) = -⟨x, hsB x hx⟩ from rfl, map_neg]
      exact neg_mem (ihx _)
    | mul x z hx hz ihx ihz =>
      intro hB
      rw [show (⟨x * z, hB⟩ : ↥B) = ⟨x, hsB x hx⟩ * ⟨z, hsB z hz⟩ from rfl, map_mul]
      exact mul_mem (ihx _) (ihz _)

  let inclB : ↥base →+* ↥B :=
    { toFun := fun x => ⟨x, hbaseB x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  let φ : ↥base →+* ↥R₀ :=
    (π.comp inclB).codRestrict R₀ (fun x => hland x (hbase_le x.2) (hbaseB x.2))
  intro y
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨p, hp, hpb⟩ := hBint b
    have hrelB : Polynomial.eval₂ inclB b p = 0 := by
      apply Subtype.val_injective
      change B.subtype (Polynomial.eval₂ inclB b p) = ((0 : ↥B) : TT)
      rw [Polynomial.hom_eval₂]
      exact hpb
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥R₀ Lk).comp φ = π.comp inclB := RingHom.ext fun _ => rfl
    rw [hcomp, ← Polynomial.hom_eval₂, hrelB, map_zero]
  · intro hy

    have hconst : ∀ x : kA, algebraMap kA Lk x ∈ π.range := by
      intro x
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
      exact ⟨⟨constantsHom' Γ A a, hcB a⟩, hπc a⟩
    let πS : Subalgebra kA Lk :=
      { π.range with algebraMap_mem' := hconst }
    have hle : R₀ ≤ πS := Algebra.adjoin_le (by rintro _ rfl; exact ⟨⟨g, hgB⟩, hπg⟩)
    let ι : ↥R₀ →+* ↥π.range :=
      { toFun := fun x => ⟨x, hle x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    obtain ⟨p, hp, hpy⟩ := hy
    refine hIC y ⟨p.map ι, hp.map ι, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : π.range.subtype.comp ι = algebraMap ↥R₀ Lk := RingHom.ext fun _ => rfl
    rw [hcomp]
    exact hpy

theorem isIntegral_adjoin_singleton_iff_of_algEquiv {L₁ L₂ : Type} [Field L₁] [Field L₂]
    [Algebra kA L₁] [Algebra kA L₂] (e : L₁ ≃ₐ[kA] L₂) (s : L₁) (x : L₂) :
    IsIntegral (Algebra.adjoin kA ({e s} : Set L₂)) x ↔
      IsIntegral (Algebra.adjoin kA ({s} : Set L₁)) (e.symm x) := by

  have hmap : ∀ z : L₁, z ∈ Algebra.adjoin kA ({s} : Set L₁) → e z ∈ Algebra.adjoin kA ({e s} : Set L₂) := by
    intro z hz
    have : Algebra.adjoin kA ({e s} : Set L₂) = (Algebra.adjoin kA ({s} : Set L₁)).map e.toAlgHom := by
      rw [AlgHom.map_adjoin]
      simp
    rw [this]
    exact ⟨z, hz, rfl⟩
  have hmap' : ∀ z : L₂, z ∈ Algebra.adjoin kA ({e s} : Set L₂) → e.symm z ∈ Algebra.adjoin kA ({s} : Set L₁) := by
    intro z hz
    have : Algebra.adjoin kA ({s} : Set L₁) = (Algebra.adjoin kA ({e s} : Set L₂)).map e.symm.toAlgHom := by
      rw [AlgHom.map_adjoin]
      simp
    rw [this]
    exact ⟨z, hz, rfl⟩
  let φ : ↥(Algebra.adjoin kA ({s} : Set L₁)) →+* ↥(Algebra.adjoin kA ({e s} : Set L₂)) :=
    (e.toAlgHom.toRingHom.comp (Algebra.adjoin kA ({s} : Set L₁)).val.toRingHom).codRestrict _
      (fun z => hmap z z.2)
  let φ' : ↥(Algebra.adjoin kA ({e s} : Set L₂)) →+* ↥(Algebra.adjoin kA ({s} : Set L₁)) :=
    (e.symm.toAlgHom.toRingHom.comp (Algebra.adjoin kA ({e s} : Set L₂)).val.toRingHom).codRestrict _
      (fun z => hmap' z z.2)
  constructor
  · rintro ⟨p, hp, hpx⟩
    refine ⟨p.map φ', hp.map φ', ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥(Algebra.adjoin kA ({s} : Set L₁)) L₁).comp φ' =
        e.symm.toAlgHom.toRingHom.comp (algebraMap ↥(Algebra.adjoin kA ({e s} : Set L₂)) L₂) :=
      RingHom.ext fun _ => rfl
    rw [hcomp, show e.symm x = e.symm.toAlgHom.toRingHom x from rfl, ← Polynomial.hom_eval₂, hpx, map_zero]
  · rintro ⟨p, hp, hpx⟩
    refine ⟨p.map φ, hp.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥(Algebra.adjoin kA ({e s} : Set L₂)) L₂).comp φ =
        e.toAlgHom.toRingHom.comp (algebraMap ↥(Algebra.adjoin kA ({s} : Set L₁)) L₁) :=
      RingHom.ext fun _ => rfl
    rw [hcomp, show x = e.toAlgHom.toRingHom (e.symm x) from (e.apply_symm_apply x).symm,
      ← Polynomial.hom_eval₂, hpx, map_zero]

set_option maxHeartbeats 32000000 in

theorem assemble
    (ψ : AS Γ ℓ A S →ₐ[↥A] TT) (hinj : Function.Injective ψ) (hICψ : IsIntegrallyClosed ↥ψ.range)
    (hψ : ∀ (a : ↥A) (b : S), ψ (asEquiv Γ ℓ A S (a ⊗ₜ b)) = algebraMap ↥A TT a * embS Γ ℓ S b)
    (hcT : ∀ a : ↥A, algebraMap ↥A TT a = constantsHom' Γ A a)
    (B base : Subring TT) (hbaseB : base ≤ B) (g : TT) (b₀ : S) (hb₀ : embS Γ ℓ S b₀ = g)
    (hbase_le : base ≤ Subring.closure (Set.range (constantsHom' Γ A) ∪ {g}))
    (hgen : Set.range (constantsHom' Γ A) ∪ {g} ⊆ (base : Set TT))
    (hbase_adj : base ≤ (Algebra.adjoin Qb ({g} : Set TT)).toSubring)
    (hBint : ∀ b : ↥B, ∃ p : Polynomial ↥base, p.Monic ∧ Polynomial.eval₂ base.subtype (b : TT) p = 0)
    (hSB : ∀ b : S, embS Γ ℓ S b ∈ B) (hconstB : ∀ a : ↥A, constantsHom' Γ A a ∈ B)
    (hspan : (CurveModel.chartRing Qb ({g} : Set TT)).toSubmodule ≤
      Submodule.span Qb (Set.range (embS Γ ℓ S)))
    (π : ↥B →+* ↥(qExpFunctionFieldC kA Γ)) (h : ↥(qExpFunctionFieldC kA Γ))
    (hgB : g ∈ B) (hπg : π ⟨g, hgB⟩ = h)
    (hπc : ∀ a : ↥A, π ⟨constantsHom' Γ A a, hconstB a⟩ =
      algebraMap kA ↥(qExpFunctionFieldC kA Γ) (residue ↥A a))
    (hker : RingHom.ker π =
      Ideal.span ((fun a : ↥A => (⟨constantsHom' Γ A a, hconstB a⟩ : ↥B)) '' (maximalIdeal ↥A : Set ↥A)))
    (hICπ : ∀ y : ↥(qExpFunctionFieldC kA Γ),
      (∃ p : Polynomial ↥π.range, p.Monic ∧ Polynomial.eval₂ π.range.subtype y p = 0) → y ∈ π.range)
    (hEq : qExpFunctionFieldC kA Γ = qExpFunctionFieldC kA Γ)
    (hF : ↥(qExpFunctionFieldC kA Γ))
    (hhF : (IntermediateField.equivOfEq hEq).symm h = hF) :
    ∃ eq : kA ⊗[ℤℓ] S ≃ₐ[kA] ↥(CurveModel.chartRing kA ({hF} : Set ↥(qExpFunctionFieldC kA Γ))),
      (eq ((1 : kA) ⊗ₜ[ℤℓ] b₀)).1 = hF ∧
      ∀ (b : S) (hb : ψ (asEquiv Γ ℓ A S ((1 : ↥A) ⊗ₜ b)) ∈ B),
        (eq ((1 : kA) ⊗ₜ[ℤℓ] b)).1 = (IntermediateField.equivOfEq hEq).symm (π ⟨ψ (asEquiv Γ ℓ A S ((1 : ↥A) ⊗ₜ b)), hb⟩) := by
  classical

  letI iC : Algebra kA ↥(qExpFunctionFieldC kA Γ) := inferInstance
  letI iF : Algebra kA ↥(qExpFunctionFieldC kA Γ) := inferInstance
  letI iKS : Algebra kA (kA ⊗[ℤℓ] S) := inferInstance
  set e : ↥(qExpFunctionFieldC kA Γ) ≃ₐ[kA] ↥(qExpFunctionFieldC kA Γ) :=
    (IntermediateField.equivOfEq hEq).symm with he
  have hg : ∃ t, ψ t = g := ⟨asEquiv Γ ℓ A S ((1 : ↥A) ⊗ₜ b₀), by rw [hψ, map_one, one_mul, hb₀]⟩

  have hbase' : ∀ x ∈ base, ∃ t, ψ t = x := by
    intro x hx
    have hcl : Subring.closure (Set.range (constantsHom' Γ A) ∪ {g}) ≤ ψ.range.toSubring := by
      rw [Subring.closure_le]
      rintro y (⟨a, rfl⟩ | hy)
      · exact ⟨algebraMap ↥A _ a, by change ψ (algebraMap ↥A _ a) = _; rw [ψ.commutes, hcT]⟩
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hg
    exact hcl (hbase_le hx)
  have hB : ∀ x : TT, x ∈ B ↔ ∃ t, ψ t = x :=
    b1 Γ ℓ A S ψ hICψ hψ hcT g base hbase_adj hbase' B hBint hSB hconstB hspan

  have hker' : RingHom.ker π = Ideal.span ((fun a : ↥A =>
      (⟨ψ (algebraMap ↥A _ a), (hB _).mpr ⟨_, rfl⟩⟩ : ↥B)) '' (maximalIdeal ↥A : Set ↥A)) := by
    rw [hker]
    congr 2
    funext a
    apply Subtype.ext
    change constantsHom' Γ A a = ψ (algebraMap ↥A _ a)
    rw [ψ.commutes, hcT]
  obtain ⟨Pr, hPr, hrange, hkerPr⟩ :=
    b2 Γ ℓ A S ↥(qExpFunctionFieldC kA Γ) ψ hinj B (fun t => (hB _).mpr ⟨t, rfl⟩)
      (fun x hx => (hB x).mp hx) π hker'

  have hb4 : ∀ y : ↥(qExpFunctionFieldC kA Γ),
      y ∈ π.range ↔ IsIntegral (Algebra.adjoin kA ({h} : Set ↥(qExpFunctionFieldC kA Γ))) y :=
    b4 Γ A B base hbaseB g hbase_le hgen hBint ↥(qExpFunctionFieldC kA Γ) π h hgB hπg hconstB hπc hICπ

  let E1 : kA ⊗[ℤℓ] S ≃+* AS Γ ℓ A S ⧸ (maximalIdeal ↥A).map (algebraMap ↥A (AS Γ ℓ A S)) :=
    (e3 Γ ℓ A S).toRingEquiv
  let E2 : (AS Γ ℓ A S ⧸ (maximalIdeal ↥A).map (algebraMap ↥A (AS Γ ℓ A S))) ≃+* ↥Pr.range :=
    (Ideal.quotEquivOfEq hkerPr.symm).trans (RingHom.quotientKerEquivRange Pr)
  have hE2 : ∀ t, (E2 (Ideal.Quotient.mk _ t) : ↥(qExpFunctionFieldC kA Γ)) = Pr t := fun t => rfl
  let E3 : ↥Pr.range ≃+* ↥π.range := RingEquiv.subringCongr hrange
  have hmem : ∀ y : ↥(qExpFunctionFieldC kA Γ), y ∈ π.range ↔
      e y ∈ CurveModel.chartRing kA ({hF} : Set ↥(qExpFunctionFieldC kA Γ)) := by
    intro y
    rw [hb4, CurveModel.mem_chartRing_iff, ← hhF]
    exact ((isIntegral_adjoin_singleton_iff_of_algEquiv A e h (e y)).trans
      (by rw [AlgEquiv.symm_apply_apply])).symm
  let E4 : ↥π.range ≃+* ↥(CurveModel.chartRing kA ({hF} : Set ↥(qExpFunctionFieldC kA Γ))) :=
    { toFun := fun y => ⟨e y.1, (hmem y.1).mp y.2⟩
      invFun := fun x => ⟨e.symm x.1, (hmem _).mpr (by rw [AlgEquiv.apply_symm_apply]; exact x.2)⟩
      left_inv := fun y => Subtype.ext (e.symm_apply_apply y.1)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.1)
      map_mul' := fun x y => Subtype.ext (map_mul e x.1 y.1)
      map_add' := fun x y => Subtype.ext (map_add e x.1 y.1) }
  let E : kA ⊗[ℤℓ] S ≃+* ↥(CurveModel.chartRing kA ({hF} : Set ↥(qExpFunctionFieldC kA Γ))) :=
    E1.trans (E2.trans (E3.trans E4))
  have hE : ∀ (a : ↥A) (b : S),
      ((E (residue ↥A a ⊗ₜ b)).1 : ↥(qExpFunctionFieldC kA Γ)) =
        e (π ⟨ψ (asEquiv Γ ℓ A S (a ⊗ₜ b)), (hB _).mpr ⟨_, rfl⟩⟩) := by
    intro a b
    change e ((E3 (E2 (E1 (residue ↥A a ⊗ₜ b)))).1) = _
    congr 1
    change ((E2 (e3 Γ ℓ A S (residue ↥A a ⊗ₜ b)) : ↥Pr.range) : ↥(qExpFunctionFieldC kA Γ)) = _
    rw [e3_tmul, hE2, hPr]

  have key : ∀ a : ↥A, E (algebraMap kA (kA ⊗[ℤℓ] S) (residue ↥A a)) =
      algebraMap kA ↥(CurveModel.chartRing kA ({hF} : Set ↥(qExpFunctionFieldC kA Γ))) (residue ↥A a) := by
    intro a
    apply Subtype.ext
    have h0 : algebraMap kA (kA ⊗[ℤℓ] S) (residue ↥A a) = residue ↥A a ⊗ₜ (1 : S) := rfl
    have hL : ((E (algebraMap kA (kA ⊗[ℤℓ] S) (residue ↥A a))).1 : ↥(qExpFunctionFieldC kA Γ)) =
        (E (residue ↥A a ⊗ₜ (1 : S))).1 :=
      congrArg (fun t => ((E t).1 : ↥(qExpFunctionFieldC kA Γ))) h0
    refine hL.trans ?_
    rw [hE]
    have h1 : ψ (asEquiv Γ ℓ A S (a ⊗ₜ (1 : S))) = constantsHom' Γ A a := by
      rw [hψ, hcT]
      have : embS Γ ℓ S 1 = 1 := Subtype.ext (by simp [embS])
      rw [this, mul_one]
    have h2 : π ⟨ψ (asEquiv Γ ℓ A S (a ⊗ₜ (1 : S))), (hB _).mpr ⟨_, rfl⟩⟩ =
        algebraMap kA ↥(qExpFunctionFieldC kA Γ) (residue ↥A a) := by
      rw [← hπc a]
      congr 1
      exact Subtype.ext h1
    rw [h2, AlgEquiv.commutes]
    rfl
  have hcomm : ∀ x : kA, E (algebraMap kA (kA ⊗[ℤℓ] S) x) =
      algebraMap kA ↥(CurveModel.chartRing kA ({hF} : Set ↥(qExpFunctionFieldC kA Γ))) x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact key a
  refine ⟨AlgEquiv.ofRingEquiv (f := E) hcomm, ?_, ?_⟩
  ·
    change ((E ((1 : kA) ⊗ₜ b₀)).1 : ↥(qExpFunctionFieldC kA Γ)) = hF
    rw [show (1 : kA) = residue ↥A 1 from (map_one _).symm, hE, ← hhF]
    congr 1
    rw [← hπg]
    congr 1
    apply Subtype.ext
    change ψ (asEquiv Γ ℓ A S (1 ⊗ₜ b₀)) = g
    rw [hψ, map_one, one_mul, hb₀]
  ·
    intro b hb
    change ((E ((1 : kA) ⊗ₜ b)).1 : ↥(qExpFunctionFieldC kA Γ)) = _
    rw [show (1 : kA) = residue ↥A 1 from (map_one _).symm, hE]

end Generic

end ModularCurve.FisoK
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing.ModularCurve P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing.ModularCurve.FisoK"
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing.ModularCurve"

namespace FisoShared

p2m_open "IsLocalRing ModularCurve P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing.ModularCurve AlgebraicCurve~genus"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem exists_mem_integers_residue_eq_of_isIntegral
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (R : AlgebraicCurve.RegularProlongation A
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))
      ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
    (hRint : ∀ f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)),
      f ∈ R.integers ↔ ∃ x y : LaurentSeries ↥A, coeffMap (residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hRpin : ∀ (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) (hf : f ∈ R.integers)
      (x y : LaurentSeries ↥A), coeffMap (residue ↥A) y ≠ 0 →
      (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
      ((R.residue ⟨f, hf⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A)) *
          coeffMap (residue ↥A) y = coeffMap (residue ↥A) x) :
    (∀ h : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ),
      (∃ P : Polynomial (Polynomial (ResidueField ↥A)), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)))
          (jqModC (ResidueField ↥A))) (h : LaurentSeries (ResidueField ↥A)) P = 0) →
      ∃ (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) (hf : f ∈ R.integers),
        R.residue ⟨f, hf⟩ = h ∧
        ∃ P : Polynomial (Polynomial ↥A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
            (jqModC (AlgebraicClosure ℚ))) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
    (∀ h : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ),
      (∃ P : Polynomial (Polynomial (ResidueField ↥A)), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)))
          (jqModC (ResidueField ↥A))⁻¹) (h : LaurentSeries (ResidueField ↥A)) P = 0) →
      ∃ (f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) (hf : f ∈ R.integers),
        R.residue ⟨f, hf⟩ = h ∧
        ∃ P : Polynomial (Polynomial ↥A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype)
            (jqModC (AlgebraicClosure ℚ))⁻¹) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) := by
  obtain ⟨hFin, hInf⟩ :=
    ModularCurve.exists_gaussIntegral_lift_isIntegral_of_isIntegral_qExpFunctionFieldC_residueField_of_not_dvd
      M Γ hΓ₁ hΓ₀ p hpM A hA
  refine ⟨fun h hh => ?_, fun h hh => ?_⟩
  · obtain ⟨f, x, y, hy0, hfy, hxh, P, hP, hPf⟩ := hFin (h : LaurentSeries (ResidueField ↥A)) h.2 hh
    have hf : f ∈ R.integers := (hRint f).mpr ⟨x, y, hy0, hfy⟩
    refine ⟨f, hf, ?_, P, hP, hPf⟩
    apply Subtype.ext
    have h1 := hRpin f hf x y hy0 hfy
    rw [hxh] at h1
    exact mul_right_cancel₀ hy0 h1
  · obtain ⟨f, x, y, hy0, hfy, hxh, P, hP, hPf⟩ := hInf (h : LaurentSeries (ResidueField ↥A)) h.2 hh
    have hf : f ∈ R.integers := (hRint f).mpr ⟨x, y, hy0, hfy⟩
    refine ⟨f, hf, ?_, P, hP, hPf⟩
    apply Subtype.ext
    have h1 := hRpin f hf x y hy0 hfy
    rw [hxh] at h1
    exact mul_right_cancel₀ hy0 h1

end FisoShared
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing.ModularCurve P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing.ModularCurve.FisoK"

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC jNum constantCoeff_jNum jq coeffMap coeffMap_single coeffMap_id coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC map_jqModC exists_algHom_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_injective_isIntegrallyClosed exists_gaussIntegral_lift_isIntegral_of_isIntegral_qExpFunctionFieldC_residueField_of_not_dvd exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq"
namespace IgusaFiso
p2m_open "ModularCurve"

theorem span_natCast_isPrime (p : ℕ) [Fact p.Prime] : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp Fact.out)

theorem ringHom_ext_ratLocalizedAt (p : ℕ) [Fact p.Prime] {S : Type*} [CommRing S]
    (f g : ↥(GaloisRep.ratLocalizedAt p) →+* S) : f = g := by
  haveI := span_natCast_isPrime p
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
  exact IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (Subsingleton.elim _ _)

theorem exists_ringHom_valuationSubring (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) :
    ∃ ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A,
      A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) := by
  haveI := span_natCast_isPrime p
  haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out

  have hunit : ∀ y : (Ideal.span {(p : ℤ)}).primeCompl, IsUnit (algebraMap ℤ ↥A y) := by
    rintro ⟨n, hn⟩
    have hn' : ¬ (p : ℤ) ∣ n := fun h => hn (Ideal.mem_span_singleton.mpr h)
    obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp Fact.out)).mpr hn'
    by_contra hnu
    have hnM : (algebraMap ℤ ↥A n) ∈ maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hpM : (algebraMap ℤ ↥A (p : ℤ)) ∈ maximalIdeal ↥A := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]
      have : ((algebraMap ℤ ↥A (p : ℤ) : ↥A) : AlgebraicClosure ℚ) = ((p : ℕ) : AlgebraicClosure ℚ) := by simp
      rw [this]; exact hA
    have h1 : (1 : ↥A) ∈ maximalIdeal ↥A := by
      have := Ideal.add_mem _ (Ideal.mul_mem_left _ (algebraMap ℤ ↥A a) hpM)
        (Ideal.mul_mem_left _ (algebraMap ℤ ↥A b) hnM)
      rwa [← map_mul, ← map_mul, ← map_add, hab, map_one] at this
    exact (IsLocalRing.maximalIdeal.isMaximal ↥A).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  refine ⟨IsLocalization.lift (M := (Ideal.span {(p : ℤ)}).primeCompl) hunit, ?_⟩
  apply ringHom_ext_ratLocalizedAt p

theorem coeffEmb_rat (y : LaurentSeries ℚ) : coeffEmb ℚ y = y := by
  change coeffMap (algebraMap ℚ ℚ) y = y
  rw [coeffMap_congr (RingHom.ext fun _ => rfl : algebraMap ℚ ℚ = RingHom.id ℚ) y, coeffMap_id]

theorem laurentBaseChange_rat (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) :
    laurentBaseChange ℚ F₀ = F₀ := by
  have himg : (⇑(coeffEmb ℚ) '' (F₀ : Set (LaurentSeries ℚ))) = (F₀ : Set (LaurentSeries ℚ)) := by
    ext y; constructor
    · rintro ⟨z, hz, rfl⟩; rw [coeffEmb_rat]; exact hz
    · intro hy; exact ⟨y, hy, coeffEmb_rat y⟩
  change IntermediateField.adjoin ℚ (⇑(coeffEmb ℚ) '' (F₀ : Set (LaurentSeries ℚ))) = F₀
  rw [himg]
  exact le_antisymm (IntermediateField.adjoin_le_iff.mpr le_rfl) (fun y hy => IntermediateField.subset_adjoin ℚ _ hy)

theorem gammaH_mono (M : ℕ) [NeZero M] {H H' : Subgroup (ZMod M)ˣ} (h : H ≤ H') :
    CohCarrier.GammaH M H ≤ CohCarrier.GammaH M H' := by
  intro γ hγ
  obtain ⟨h0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  exact CohCarrier.mem_GammaH_iff.mpr ⟨h0, h hH⟩

theorem eq_one_or_eq_neg_one_of_mem_zpowers {G : Type*} [Group G] [HasDistribNeg G] {z : G}
    (hz : z ∈ Subgroup.zpowers (-1 : G)) : z = 1 ∨ z = -1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hsq : (-1 : G) * (-1) = 1 := by rw [neg_mul_neg, one_mul]
  have hinv : (-1 : G)⁻¹ = -1 := inv_eq_of_mul_eq_one_right hsq
  cases k with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, zpow_natCast]
    exact neg_one_pow_eq_or G n
  | negSucc n =>
    rw [zpow_negSucc]
    rcases neg_one_pow_eq_or G (n + 1) with h | h
    · left; rw [h, inv_one]
    · right; rw [h, hinv]

theorem mem_or_neg_mem_gammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1))) :
    γ ∈ CohCarrier.GammaH M H ∨ -γ ∈ CohCarrier.GammaH M H := by
  obtain ⟨h0, hH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  obtain ⟨u, hu, z, hz, huz⟩ := Subgroup.mem_sup.mp hH
  have h0' : -γ ∈ CongruenceSubgroup.Gamma0 M := by
    rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
    simp [h0]
  have hneg : CohCarrier.gamma0Units M ⟨-γ, h0'⟩ = -CohCarrier.gamma0Units M ⟨γ, h0⟩ := by
    ext; simp [CohCarrier.val_gamma0Units, CongruenceSubgroup.Gamma0Map]
  rcases eq_one_or_eq_neg_one_of_mem_zpowers hz with rfl | rfl
  · left
    rw [mul_one] at huz
    exact CohCarrier.mem_GammaH_iff.mpr ⟨h0, huz ▸ hu⟩
  · right
    refine CohCarrier.mem_GammaH_iff.mpr ⟨h0', ?_⟩
    rw [hneg, ← huz, mul_neg_one, neg_neg]
    exact hu

end ModularCurve.IgusaFiso
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing.ModularCurve P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing.ModularCurve.FisoK"
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing.ModularCurve P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing.ModularCurve.FisoK"

namespace FisoShared

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing.ModularCurve"

theorem isUnit_jqModC (A : Type*) [CommRing A] : IsUnit (jqModC A) := by
  rw [jqModC]
  refine IsUnit.mul ?_ ?_
  · refine IsUnit.of_mul_eq_one (HahnSeries.single (1 : ℤ) (1 : A)) ?_
    rw [HahnSeries.single_mul_single, one_mul, show (-1 : ℤ) + 1 = 0 by norm_num, HahnSeries.single_zero_one]
  · have hc : PowerSeries.constantCoeff (jNum.map (Int.castRingHom A)) = 1 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum, map_one]
    have hu : IsUnit (jNum.map (Int.castRingHom A)) :=
      IsUnit.of_mul_eq_one _ (PowerSeries.mul_invOfUnit _ 1 (by rw [hc, Units.val_one]))
    exact hu.map (HahnSeries.ofPowerSeries ℤ A)

theorem exists_mul_jqModC_eq_one (A : Type*) [CommRing A] : ∃ y : LaurentSeries A, y * jqModC A = 1 :=
  (isUnit_jqModC A).exists_left_inv

theorem coeffMap_eq_jqModC_inv {A K : Type*} [CommRing A] [Field K] (f : A →+* K)
    {y : LaurentSeries A} (hy : y * jqModC A = 1) : coeffMap f y = (jqModC K)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← map_jqModC f]
  change coeffMap f y * coeffMap f (jqModC A) = 1
  rw [← map_mul, hy, map_one]

end FisoShared
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing.ModularCurve P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing.ModularCurve.FisoK"

open ModularCurve.IgusaFiso in
set_option maxHeartbeats 25600000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M)
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : ↥(GaloisRep.ratLocalizedAt p) →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))
    (x : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
    (hx : (x : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A)) :
    letI := ((residue ↥A).comp ρ).toAlgebra
    (∃ eFin : ResidueField ↥A ⊗[↥(GaloisRep.ratLocalizedAt p)]
          ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j) ≃ₐ[ResidueField ↥A]
        ↥(CurveModel.chartRing (ResidueField ↥A) ({(x : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))} :
          Set ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))),
      (eFin ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)]
        TwoChartIntegralModel.jChartFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)).1 = x ∧
      ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))
        (y : LaurentSeries ↥A),
        coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)) →
        (((eFin ((1 : ResidueField ↥A) ⊗ₜ[↥(GaloisRep.ratLocalizedAt p)] b)).1 :
            ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A)) =
          coeffMap (residue ↥A) y) := by
  classical
  obtain ⟨H, rfl⟩ := CohCarrier.exists_eq_gammaH_of_gamma1_le_of_le_gamma0 M Γ hΓ₁ hΓ₀
  letI algκ : Algebra ↥(GaloisRep.ratLocalizedAt p) (ResidueField ↥A) := ((residue ↥A).comp ρ).toAlgebra
  show ∃ eFin, _
  haveI : IsPrincipalIdealRing ↥(GaloisRep.ratLocalizedAt p) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt p
  haveI : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le hΓ₁
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := hΓ₁ (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])

  have hK : qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) = laurentBaseChange ℚ (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := (laurentBaseChange_rat _).symm
  have hj' : ((j : LaurentSeries ℚ)) = coeffEmb ℚ jq := by rw [hj, coeffEmb_rat]; rfl
  have hTow : @IsScalarTower ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) _
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))).toSMul _ := by
    refine @IsScalarTower.of_algebraMap_eq ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) _ _ _ _
      (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) _ (fun x => ?_)
    first
    | exact rfl
    | (apply Subtype.ext
       change ((algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :
           LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) (x : ℚ)
       have hC : (HahnSeries.C : ℚ →+* LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) := by ext a : 1; simp
       rw [← hC]; rfl)
  have htj : Transcendental ↥(GaloisRep.ratLocalizedAt p) j :=
    @ModularCurve.transcendental_of_coe_eq_coeffEmb_jq ℚ _ _ (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ↥(GaloisRep.ratLocalizedAt p) _ _ _ _ _
      hTow j hj'
  have hAlg : (SubalgebraClass.toAlgebra (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) : Algebra ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) =
      DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by
    have h := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CohCarrier.GammaH M H) hT ℚ
      (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) hK j hj'
    exact hAlg ▸ h
  haveI := hFD
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin ℚ ({j} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) :=
    inferInstance
  obtain ⟨hFTf, hFTi⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf
    ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j htj hFD hsep
  haveI := hFTf; haveI := hFTi

  obtain ⟨x', hx', hxtr', -, -⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField (AlgebraicClosure ℚ) A
      (CohCarrier.GammaH M H) hT
  have hxtr : Transcendental (ResidueField ↥A) x := by
    have hxx : x' = x := Subtype.ext (hx'.trans hx.symm)
    rw [← hxx]; exact hxtr'
  obtain ⟨V, hRV, ρV, hpV, hjV, hρ0, hρR, hρj, hadj, -, -⟩ :=
    ModularCurve.exists_valuationSubring_ringHom_laurentSeries_qExpFunctionFieldC_of_liesOverPrime
      (CohCarrier.GammaH M H) hT p j hj A hA ρ hρ x hx

  have hL := ModularCurve.index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField M H hpM A hA x hx
  have hdegE : ∀ (E : IntermediateField (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)))
      (hE : E = qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)) (t : ↥E)
      (ht : (t : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A)),
      (CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1))).index ≤
        Module.finrank ↥(IntermediateField.adjoin (ResidueField ↥A) ({t} : Set ↥E)) ↥E ∧ Transcendental (ResidueField ↥A) t := by
    intro E hE; subst hE; intro t ht
    have htx : t = x := Subtype.ext (ht.trans hx.symm)
    subst htx
    exact ⟨hL, hxtr⟩
  have hjmem : (j : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ∈ V := by
    have h := (hjV Polynomial.X (fun hdvd => ?_)).1
    · simpa using h
    · have hc := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hdvd 1
      rw [Polynomial.coeff_X_one] at hc
      exact (GaloisRep.irreducible_natCast_ratLocalizedAt p Fact.out).not_isUnit (isUnit_of_dvd_one hc)
  let jV : ↥V := ⟨j, hjmem⟩
  let t₀ : ↥(IntermediateField.adjoin (ResidueField ↥A) (Set.range ρV)) :=
    ⟨ρV jV, IntermediateField.subset_adjoin _ _ ⟨jV, rfl⟩⟩
  have ht₀ : ((t₀ : ↥(IntermediateField.adjoin (ResidueField ↥A) (Set.range ρV))) : LaurentSeries (ResidueField ↥A)) =
      jqModC (ResidueField ↥A) := hρj jV rfl
  obtain ⟨hL', htr'⟩ := hdegE _ hadj t₀ ht₀

  have h53 := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index ℚ (CohCarrier.GammaH M H) hT
      (CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1))) (gammaH_mono M le_sup_left) (mem_or_neg_mem_gammaH M H)

  generalize hK'' : laurentBaseChange ℚ (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) = K at h53
  have hKF : K = qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) := hK''.symm.trans hK.symm
  subst hKF
  have hup₁ := h53 j hj
  have hup : Module.finrank ↥(IntermediateField.adjoin ℚ ({j} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))
      ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ≤ (CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1))).index := by
    first
    | exact hup₁
    | exact hAlg ▸ hup₁

  have hprime : Prime ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) :=
    (GaloisRep.irreducible_natCast_ratLocalizedAt p Fact.out).prime
  have hk0 : algebraMap ↥(GaloisRep.ratLocalizedAt p) (ResidueField ↥A) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero _ p
  obtain ⟨hdF, hdI, hntM⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.isDomain_tensorProduct_chartAlg_of_finrank_le_finrank_adjoin_range
      ↥(GaloisRep.ratLocalizedAt p) ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j htj hFD hsep
      ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) hprime V hRV hpV hjV
      (ResidueField ↥A) hk0 (LaurentSeries (ResidueField ↥A)) ρV hρ0 hρR jV rfl t₀ rfl htr'
      (hup.trans hL')
  haveI := hdF; haveI := hdI

  obtain ⟨Rg, hRgint, hRgres, hRgpin⟩ :=
    ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq (AlgebraicClosure ℚ) A (CohCarrier.GammaH M H) hT

  letI iρ : Algebra ↥(GaloisRep.ratLocalizedAt p) ↥A := ρ.toAlgebra
  letI iAT : Algebra ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))).comp
      A.subtype).toAlgebra
  have hcT : ∀ a : ↥A, algebraMap ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) a =
      FisoK.constantsHom' (CohCarrier.GammaH M H) A a := fun a => rfl

  set S : Subalgebra ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) :=
    TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j with hSdef
  set g : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    FisoK.embS (CohCarrier.GammaH M H) p S (TwoChartIntegralModel.jChartFin _ _ j) with hgdef
  have hgcoe : (g : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((j : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) := rfl

  obtain ⟨⟨ψ, hψf, hinj, -, hICψ⟩, -⟩ :=
    ModularCurve.exists_algHom_tensor_chartAlg_twoChartIntegralModel_qExpFunctionFieldC_injective_isIntegrallyClosed
      M (CohCarrier.GammaH M H) hΓ₁ hΓ₀ p hpM j hj A hA ρ hρ
  have hψ : ∀ (a : ↥A) (b : ↥S), ψ (FisoK.asEquiv (CohCarrier.GammaH M H) p A S (a ⊗ₜ b)) =
      algebraMap ↥A _ a * FisoK.embS (CohCarrier.GammaH M H) p S b := by
    intro a b
    apply Subtype.ext
    exact hψf a b

  set B : Subring ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := ψ.range.toSubring with hBdef
  have hB : ∀ y, y ∈ B ↔ ∃ t, ψ t = y := fun y => AlgHom.mem_range ψ
  set baseA : Subalgebra ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    Algebra.adjoin ↥A {g} with hbaseAdef
  set base : Subring ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) := baseA.toSubring with hbasedef
  have hconstB : ∀ a : ↥A, FisoK.constantsHom' (CohCarrier.GammaH M H) A a ∈ B := fun a =>
    (hB _).mpr ⟨algebraMap ↥A _ a, by rw [AlgHom.commutes, hcT]⟩
  have hSB : ∀ b : ↥S, FisoK.embS (CohCarrier.GammaH M H) p S b ∈ B := fun b =>
    (hB _).mpr ⟨FisoK.asEquiv (CohCarrier.GammaH M H) p A S ((1 : ↥A) ⊗ₜ b), by rw [hψ, map_one, one_mul]⟩
  have hgB : g ∈ B := hSB _
  have hgen : Set.range (FisoK.constantsHom' (CohCarrier.GammaH M H) A) ∪ {g} ⊆ (base : Set _) := by
    rintro y (⟨a, rfl⟩ | hy)
    · rw [← hcT]; exact Subalgebra.algebraMap_mem baseA a
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact Algebra.subset_adjoin rfl
  have hbase_le : base ≤ Subring.closure (Set.range (FisoK.constantsHom' (CohCarrier.GammaH M H) A) ∪ {g}) := by
    let C : Subalgebra ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
      { Subring.closure (Set.range (FisoK.constantsHom' (CohCarrier.GammaH M H) A) ∪ {g}) with
        algebraMap_mem' := fun a => Subring.subset_closure (Or.inl ⟨a, (hcT a).symm⟩) }
    have : baseA ≤ C := Algebra.adjoin_le (fun y hy => Subring.subset_closure (Or.inr hy))
    exact this
  have hbase_adj : base ≤ (Algebra.adjoin (AlgebraicClosure ℚ) ({g} : Set _)).toSubring := by
    refine le_trans hbase_le ?_
    rw [Subring.closure_le]
    rintro y (⟨a, rfl⟩ | hy)
    · exact Subalgebra.algebraMap_mem _ (a : AlgebraicClosure ℚ)
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact Algebra.subset_adjoin rfl
  have hbaseB : base ≤ B := by
    refine le_trans hbase_le ?_
    rw [Subring.closure_le]
    rintro y (⟨a, rfl⟩ | hy)
    · exact hconstB a
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact hgB

  let embF : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) →+* ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    { toFun := fun z => ⟨coeffEmb (AlgebraicClosure ℚ) (z : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun z w => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun z w => Subtype.ext (by simp) }
  have hembF : ∀ z, (embF z : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (z : LaurentSeries ℚ) := fun z => rfl
  have hembF_S : ∀ b : ↥S, embF (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = FisoK.embS (CohCarrier.GammaH M H) p S b :=
    fun b => Subtype.ext rfl
  have hembF_j : embF j = g := Subtype.ext rfl
  have hembF_alg : ∀ r : ↥(GaloisRep.ratLocalizedAt p),
      embF (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) r) =
        algebraMap ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) (ρ r) := by
    intro r
    apply Subtype.ext
    rw [hcT]
    change coeffEmb (AlgebraicClosure ℚ) ((algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) r : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (A.subtype (ρ r))
    have h1 : ((algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) r : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) =
        algebraMap ℚ (LaurentSeries ℚ) (r : ℚ) := by
      first
      | rfl
      | (have hC : (HahnSeries.C : ℚ →+* LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) := by ext a : 1; simp
         rw [← hC]; rfl)
    have h2 : A.subtype (ρ r) = algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) := by
      have := congrArg (fun φ : ↥(GaloisRep.ratLocalizedAt p) →+* AlgebraicClosure ℚ => φ r) hρ
      first | simpa using this | (simp at this; exact this) | exact this
    rw [h1, h2, algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single]
    change coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (HahnSeries.single 0 (r : ℚ)) = _
    rw [coeffMap_single]
  have hadj_map : ∀ z ∈ Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({j} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))),
      embF z ∈ baseA := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz => rw [Set.mem_singleton_iff] at hz; subst hz; rw [hembF_j]; exact Algebra.subset_adjoin rfl
    | algebraMap r => rw [hembF_alg]; exact Subalgebra.algebraMap_mem _ _
    | add z w _ _ hz hw => rw [map_add]; exact add_mem hz hw
    | mul z w _ _ hz hw => rw [map_mul]; exact mul_mem hz hw
  let θ : ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({j} : Set ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) →+* ↥baseA :=
    (embF.comp (Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({j} : Set _)).val.toRingHom).codRestrict baseA.toSubring
      (fun z => hadj_map z z.2)
  have hθ : (algebraMap ↥baseA ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))).comp θ =
      embF.comp (algebraMap ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({j} : Set _)) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    RingHom.ext fun _ => rfl
  have hembInt : ∀ b : ↥S, IsIntegral ↥baseA (FisoK.embS (CohCarrier.GammaH M H) p S b) := by
    intro b
    have hb : IsIntegral ↥(Algebra.adjoin ↥(GaloisRep.ratLocalizedAt p) ({j} : Set _)) (b : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
      (TwoChartIntegralModel.mem_chartAlg_iff ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))).mp b.2
    obtain ⟨q, hqm, hqb⟩ := hb
    refine ⟨q.map θ, hqm.map θ, ?_⟩
    rw [Polynomial.eval₂_map, hθ, ← hembF_S, ← Polynomial.hom_eval₂, hqb, map_zero]
  have hBint : ∀ b : ↥B, ∃ q : Polynomial ↥base, q.Monic ∧ Polynomial.eval₂ base.subtype (b : _) q = 0 := by

    have haux : ∀ t, IsIntegral ↥baseA (ψ t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact isIntegral_zero
      | tmul a c =>
        have : ψ (a ⊗ₜ c) = algebraMap ↥A _ a * FisoK.embS (CohCarrier.GammaH M H) p S c := hψ a c
        rw [this]
        exact (isIntegral_algebraMap (R := ↥baseA) (x := (⟨algebraMap ↥A _ a, Subalgebra.algebraMap_mem baseA a⟩ : ↥baseA))).mul (hembInt c)
      | add z w hz hw => rw [map_add]; exact hz.add hw
    intro b
    suffices h : IsIntegral ↥baseA (b : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) by
      exact h
    obtain ⟨t, ht⟩ := (hB _).mp b.2
    rw [← ht]
    exact haux t

  have hspan := (ModularCurve.chartRing_laurentBaseChange_le_span_coeffEmb_chartAlg (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) p j g hgcoe).1

  have hyj : coeffMap A.subtype (jqModC ↥A) ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by
    have : coeffMap A.subtype (jqModC ↥A) = (g : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [hgcoe, hj]; change (jqModC ↥A).map A.subtype = (jqModC ℚ).map _; rw [map_jqModC, map_jqModC]
    rw [this]; exact g.2
  have hgeq : (⟨coeffMap A.subtype (jqModC ↥A), hyj⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) = g := by
    apply Subtype.ext; rw [hgcoe, hj]; change (jqModC ↥A).map A.subtype = (jqModC ℚ).map _; rw [map_jqModC, map_jqModC]
  obtain ⟨hgO, hgres⟩ := hRgres (jqModC ↥A) hyj
  have hgO' : g ∈ Rg.integers := hgeq ▸ hgO
  have hbaseO : base ≤ Rg.integers.toSubring := by
    refine le_trans hbase_le ?_
    rw [Subring.closure_le]
    rintro y (⟨a, rfl⟩ | hy)
    · exact (Rg.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2
    · rw [Set.mem_singleton_iff] at hy; subst hy; exact hgO'

  have hembO : ∀ b : ↥S, FisoK.embS (CohCarrier.GammaH M H) p S b ∈ Rg.integers := by
    intro b
    have hint : IsIntegral ↥Rg.integers (FisoK.embS (CohCarrier.GammaH M H) p S b) := by
      obtain ⟨q, hqm, hqb⟩ := hembInt b
      let ι' : ↥baseA →+* ↥Rg.integers :=
        { toFun := fun z => ⟨z.1, hbaseO z.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
          map_zero' := rfl, map_add' := fun _ _ => rfl }
      refine ⟨q.map ι', hqm.map ι', ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : (algebraMap ↥Rg.integers ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))).comp ι' =
          algebraMap ↥baseA _ := RingHom.ext fun _ => rfl
      rw [hcomp]
      exact hqb
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    rw [← hz]
    exact z.2
  have hBO : B ≤ Rg.integers.toSubring := by
    suffices haux : ∀ t, ψ t ∈ Rg.integers.toSubring by
      intro y hy; obtain ⟨t, rfl⟩ := (hB _).mp hy; exact haux t
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul a c =>
      have : ψ (a ⊗ₜ c) = algebraMap ↥A _ a * FisoK.embS (CohCarrier.GammaH M H) p S c := hψ a c
      rw [this, hcT]
      exact mul_mem ((Rg.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2) (hembO c)
    | add z w hz hw => rw [map_add]; exact add_mem hz hw
  let π : ↥B →+* ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)) :=
    Rg.residue.comp (Subring.inclusion hBO)
  have hπ_apply : ∀ (y) (hy : y ∈ B), π ⟨y, hy⟩ = Rg.residue ⟨y, hBO hy⟩ := fun y hy => rfl
  have hπg : π ⟨g, hgB⟩ = x := by
    rw [hπ_apply]
    apply Subtype.ext
    rw [hx, ← map_jqModC (residue ↥A)]
    have : (⟨g, hBO hgB⟩ : ↥Rg.integers) = ⟨⟨coeffMap A.subtype (jqModC ↥A), hyj⟩, hgO⟩ := Subtype.ext hgeq.symm
    rw [this]
    exact hgres
  have hπc : ∀ a : ↥A, π ⟨FisoK.constantsHom' (CohCarrier.GammaH M H) A a, hconstB a⟩ =
      algebraMap (ResidueField ↥A) _ (residue ↥A a) := by
    intro a; rw [hπ_apply]; exact Rg.residue_algebraMap a
  have hker : RingHom.ker π = Ideal.span ((fun a : ↥A => (⟨FisoK.constantsHom' (CohCarrier.GammaH M H) A a, hconstB a⟩ : ↥B)) '' (maximalIdeal ↥A : Set ↥A)) := by
    classical
    refine le_antisymm ?hard ?easy
    case easy =>
      rw [Ideal.span_le]
      rintro _ ⟨a, ha, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, hπc a]
      have : residue ↥A a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
      rw [this, map_zero]
    case hard =>

      let ψB : FisoK.AS (CohCarrier.GammaH M H) p A S →+* ↥B := (ψ.toRingHom).codRestrict B (fun t => (hB _).mpr ⟨t, rfl⟩)
      have hψB : ∀ t, (ψB t : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) = ψ t := fun t => rfl
      have hbij : Function.Bijective ψB :=
        ⟨fun u v h => hinj (congrArg Subtype.val h), fun y => by
          obtain ⟨t, ht⟩ := (hB _).mp y.2
          exact ⟨t, Subtype.ext ht⟩⟩
      let eψ : FisoK.AS (CohCarrier.GammaH M H) p A S ≃+* ↥B := RingEquiv.ofBijective ψB hbij
      have heψ : ∀ t, eψ t = ψB t := fun t => rfl

      let J : Ideal (FisoK.AS (CohCarrier.GammaH M H) p A S) :=
        (maximalIdeal ↥A).map (algebraMap ↥A (FisoK.AS (CohCarrier.GammaH M H) p A S))
      haveI : IsScalarTower ↥(GaloisRep.ratLocalizedAt p) ↥A (ResidueField ↥A) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
      haveI : SMulCommClass ↥(GaloisRep.ratLocalizedAt p) ↥A (ResidueField ↥A) :=
        ⟨fun r a c => by rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, mul_left_comm]⟩
      haveI hdomQ : IsDomain (FisoK.AS (CohCarrier.GammaH M H) p A S ⧸ J) :=
        FisoK.isDomain_quot (CohCarrier.GammaH M H) p A S hdF

      let Pr : FisoK.AS (CohCarrier.GammaH M H) p A S →+* ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)) := π.comp ψB
      have hPrc : ∀ a : ↥A, Pr (algebraMap ↥A _ a) = algebraMap (ResidueField ↥A) _ (residue ↥A a) := by
        intro a
        change π (ψB (algebraMap ↥A _ a)) = _
        have : ψB (algebraMap ↥A _ a) = ⟨FisoK.constantsHom' (CohCarrier.GammaH M H) A a, hconstB a⟩ := by
          apply Subtype.ext; rw [hψB]; change ψ (algebraMap ↥A _ a) = _; rw [AlgHom.commutes, hcT]
        rw [this, hπc]
      have hJ : ∀ t ∈ J, Pr t = 0 := by
        intro t ht
        have : J ≤ RingHom.ker Pr := by
          rw [Ideal.map_le_iff_le_comap]
          intro a ha
          rw [Ideal.mem_comap, RingHom.mem_ker, hPrc]
          have : residue ↥A a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
          rw [this, map_zero]
        exact this ht
      let Prq : (FisoK.AS (CohCarrier.GammaH M H) p A S ⧸ J) →+* ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)) :=
        Ideal.Quotient.lift J Pr hJ
      have hPrq : ∀ t, Prq (Ideal.Quotient.mk J t) = Pr t := fun t => Ideal.Quotient.lift_mk J Pr hJ

      let cκ : ResidueField ↥A →+* (FisoK.AS (CohCarrier.GammaH M H) p A S ⧸ J) :=
        Ideal.Quotient.lift (maximalIdeal ↥A) ((Ideal.Quotient.mk J).comp (algebraMap ↥A _))
          (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))
      have hcκ : ∀ a : ↥A, cκ (residue ↥A a) = Ideal.Quotient.mk J (algebraMap ↥A _ a) := fun a =>
        Ideal.Quotient.lift_mk _ _ _
      let t₁ : FisoK.AS (CohCarrier.GammaH M H) p A S := FisoK.asEquiv (CohCarrier.GammaH M H) p A S ((1 : ↥A) ⊗ₜ (TwoChartIntegralModel.jChartFin _ _ j))
      have ht₁ : ψB t₁ = ⟨g, hgB⟩ := by apply Subtype.ext; rw [hψB]; change ψ _ = g; rw [hψ, map_one, one_mul]
      let φ : Polynomial (ResidueField ↥A) →+* (FisoK.AS (CohCarrier.GammaH M H) p A S ⧸ J) :=
        Polynomial.eval₂RingHom cκ (Ideal.Quotient.mk J t₁)

      have hcomp : Prq.comp φ = Polynomial.eval₂RingHom (algebraMap (ResidueField ↥A) _) x := by
        apply Polynomial.ringHom_ext
        · intro c
          obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
          change Prq (Polynomial.eval₂ cκ _ (Polynomial.C (residue ↥A a))) = Polynomial.eval₂ _ x (Polynomial.C _)
          rw [Polynomial.eval₂_C, Polynomial.eval₂_C, hcκ, hPrq, hPrc]
        · change Prq (Polynomial.eval₂ cκ _ Polynomial.X) = Polynomial.eval₂ _ x Polynomial.X
          rw [Polynomial.eval₂_X, Polynomial.eval₂_X, hPrq]
          change π (ψB t₁) = x
          rw [ht₁, hπg]
      have hinjev : Function.Injective (Polynomial.eval₂RingHom (algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H))) x) := by
        have h := transcendental_iff_injective.mp hxtr
        intro u v huv
        apply h
        change Polynomial.aeval x u = Polynomial.aeval x v
        rw [Polynomial.aeval_def, Polynomial.aeval_def]
        exact huv

      let τ : ↥B →+* (FisoK.AS (CohCarrier.GammaH M H) p A S ⧸ J) := (Ideal.Quotient.mk J).comp eψ.symm.toRingHom
      have hτψ : ∀ t, τ (ψB t) = Ideal.Quotient.mk J t := by
        intro t; change Ideal.Quotient.mk J (eψ.symm (eψ t)) = _; rw [RingEquiv.symm_apply_apply]
      have hτbase : ∀ y, y ∈ Subring.closure (Set.range (FisoK.constantsHom' (CohCarrier.GammaH M H) A) ∪ {g}) →
          ∀ (hy : y ∈ B), τ ⟨y, hy⟩ ∈ φ.range := by
        intro y hy'
        induction hy' using Subring.closure_induction with
        | mem z hz =>
          intro hzB
          rcases hz with ⟨a, rfl⟩ | hz
          · refine ⟨Polynomial.C (residue ↥A a), ?_⟩
            change Polynomial.eval₂ cκ _ (Polynomial.C _) = _
            rw [Polynomial.eval₂_C, hcκ, ← hτψ]
            congr 1
            apply Subtype.ext; rw [hψB]; change ψ (algebraMap ↥A _ a) = _; rw [AlgHom.commutes, hcT]
          · rw [Set.mem_singleton_iff] at hz; subst hz
            refine ⟨Polynomial.X, ?_⟩
            change Polynomial.eval₂ cκ _ Polynomial.X = _
            rw [Polynomial.eval₂_X, ← hτψ, ht₁]
        | zero => intro h0; rw [show (⟨0, h0⟩ : ↥B) = 0 from rfl, map_zero]; exact zero_mem _
        | one => intro h1; rw [show (⟨1, h1⟩ : ↥B) = 1 from rfl, map_one]; exact one_mem _
        | add u v hu hv ihu ihv =>
          intro huv
          rw [show (⟨u + v, huv⟩ : ↥B) = ⟨u, hbaseB (Subring.closure_le.mpr hgen hu)⟩ + ⟨v, hbaseB (Subring.closure_le.mpr hgen hv)⟩ from rfl, map_add]
          exact add_mem (ihu _) (ihv _)
        | neg u hu ihu =>
          intro hn
          rw [show (⟨-u, hn⟩ : ↥B) = -⟨u, hbaseB (Subring.closure_le.mpr hgen hu)⟩ from rfl, map_neg]
          exact neg_mem (ihu _)
        | mul u v hu hv ihu ihv =>
          intro huv
          rw [show (⟨u * v, huv⟩ : ↥B) = ⟨u, hbaseB (Subring.closure_le.mpr hgen hu)⟩ * ⟨v, hbaseB (Subring.closure_le.mpr hgen hv)⟩ from rfl, map_mul]
          exact mul_mem (ihu _) (ihv _)
      let τb : ↥base →+* ↥φ.range :=
        { toFun := fun z => ⟨τ ⟨z, hbaseB z.2⟩, hτbase z (hbase_le z.2) _⟩
          map_one' := Subtype.ext (by change τ _ = 1; exact map_one τ)
          map_mul' := fun a b => Subtype.ext (by change τ _ = τ _ * τ _; rw [← map_mul]; rfl)
          map_zero' := Subtype.ext (by change τ _ = 0; exact map_zero τ)
          map_add' := fun a b => Subtype.ext (by change τ _ = τ _ + τ _; rw [← map_add]; rfl) }
      haveI : Algebra.IsIntegral ↥φ.range (FisoK.AS (CohCarrier.GammaH M H) p A S ⧸ J) := by
        refine ⟨fun z => ?_⟩
        obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
        obtain ⟨q, hqm, hqb⟩ := hBint (ψB t)
        refine ⟨q.map τb, hqm.map τb, ?_⟩
        rw [Polynomial.eval₂_map, ← hτψ]
        have hc : (algebraMap ↥φ.range (FisoK.AS (CohCarrier.GammaH M H) p A S ⧸ J)).comp τb = τ.comp (Subring.inclusion hbaseB) :=
          RingHom.ext fun _ => rfl
        rw [hc, ← Polynomial.hom_eval₂]
        have : Polynomial.eval₂ (Subring.inclusion hbaseB) (ψB t) q = 0 := by
          apply Subtype.ext
          rw [show ((Polynomial.eval₂ (Subring.inclusion hbaseB) (ψB t) q : ↥B) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) =
            B.subtype (Polynomial.eval₂ (Subring.inclusion hbaseB) (ψB t) q) from rfl, Polynomial.hom_eval₂]
          exact hqb
        rw [this, map_zero]

      have hP : RingHom.ker Prq = ⊥ := by
        apply Ideal.eq_bot_of_comap_eq_bot (R := ↥φ.range)
        rw [eq_bot_iff]
        rintro ⟨z, ⟨q, rfl⟩⟩ hz
        rw [Ideal.mem_comap, RingHom.mem_ker] at hz
        change Prq (φ q) = 0 at hz
        have hq : q = 0 := hinjev (by rw [← hcomp]; change Prq (φ q) = Prq (φ 0); rw [hz, map_zero, map_zero])
        rw [Ideal.mem_bot]; apply Subtype.ext; change φ q = 0; rw [hq, map_zero]

      intro b hb
      rw [RingHom.mem_ker] at hb
      obtain ⟨t, rfl⟩ := hbij.2 b
      have ht : Ideal.Quotient.mk J t ∈ RingHom.ker Prq := by rw [RingHom.mem_ker, hPrq]; exact hb
      rw [hP, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at ht

      have : (J.map eψ.toRingHom : Ideal ↥B) = Ideal.span ((fun a : ↥A => (⟨FisoK.constantsHom' (CohCarrier.GammaH M H) A a, hconstB a⟩ : ↥B)) '' (maximalIdeal ↥A : Set ↥A)) := by
        rw [Ideal.map_map]
        unfold Ideal.map
        congr 1
        ext y
        simp only [Set.mem_image, SetLike.mem_coe, RingHom.coe_comp, Function.comp_apply]
        have heψa : ∀ a : ↥A, eψ.toRingHom (algebraMap ↥A (FisoK.AS (CohCarrier.GammaH M H) p A S) a) =
            (⟨FisoK.constantsHom' (CohCarrier.GammaH M H) A a, hconstB a⟩ : ↥B) := by
          intro a; apply Subtype.ext; change ψ (algebraMap ↥A _ a) = _; rw [AlgHom.commutes, hcT]
        constructor
        · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, (heψa a).symm⟩
        · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, heψa a⟩
      rw [← this]
      exact Ideal.mem_map_of_mem eψ.toRingHom ht
  have hICπ : ∀ y : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)),
      (∃ q : Polynomial ↥π.range, q.Monic ∧ Polynomial.eval₂ π.range.subtype y q = 0) → y ∈ π.range := by
    classical
    intro y hy

    let R₀ : Subalgebra (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)) :=
      Algebra.adjoin (ResidueField ↥A) {x}
    have hπcl : ∀ z, z ∈ Subring.closure (Set.range (FisoK.constantsHom' (CohCarrier.GammaH M H) A) ∪ {g}) →
        ∀ (hz : z ∈ B), π ⟨z, hz⟩ ∈ R₀ := by
      intro z hz'
      induction hz' using Subring.closure_induction with
      | mem w hw =>
        intro hwB
        rcases hw with ⟨a, rfl⟩ | hw
        · rw [show π ⟨_, hwB⟩ = π ⟨_, hconstB a⟩ from rfl, hπc]; exact Subalgebra.algebraMap_mem _ _
        · rw [Set.mem_singleton_iff] at hw; subst hw
          rw [show π ⟨_, hwB⟩ = π ⟨g, hgB⟩ from rfl, hπg]; exact Algebra.subset_adjoin rfl
      | zero => intro h0; rw [show (⟨0, h0⟩ : ↥B) = 0 from rfl, map_zero]; exact zero_mem _
      | one => intro h1; rw [show (⟨1, h1⟩ : ↥B) = 1 from rfl, map_one]; exact one_mem _
      | add u v hu hv ihu ihv =>
        intro huv
        rw [show (⟨u + v, huv⟩ : ↥B) = ⟨u, hbaseB (Subring.closure_le.mpr hgen hu)⟩ + ⟨v, hbaseB (Subring.closure_le.mpr hgen hv)⟩ from rfl, map_add]
        exact add_mem (ihu _) (ihv _)
      | neg u hu ihu =>
        intro hn
        rw [show (⟨-u, hn⟩ : ↥B) = -⟨u, hbaseB (Subring.closure_le.mpr hgen hu)⟩ from rfl, map_neg]
        exact neg_mem (ihu _)
      | mul u v hu hv ihu ihv =>
        intro huv
        rw [show (⟨u * v, huv⟩ : ↥B) = ⟨u, hbaseB (Subring.closure_le.mpr hgen hu)⟩ * ⟨v, hbaseB (Subring.closure_le.mpr hgen hv)⟩ from rfl, map_mul]
        exact mul_mem (ihu _) (ihv _)

    have hconstπ : ∀ c : ResidueField ↥A, algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)) c ∈ π.range := by
      intro c; obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c; exact ⟨⟨_, hconstB a⟩, hπc a⟩
    let πS : Subalgebra (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)) :=
      { π.range with algebraMap_mem' := hconstπ }
    have hle : R₀ ≤ πS := Algebra.adjoin_le (by rintro _ rfl; exact ⟨⟨g, hgB⟩, hπg⟩)
    let πb : ↥base →+* ↥R₀ :=
      { toFun := fun z => ⟨π ⟨z, hbaseB z.2⟩, hπcl z (hbase_le z.2) _⟩
        map_one' := Subtype.ext (by change π _ = 1; exact map_one π)
        map_mul' := fun a b => Subtype.ext (by change π _ = π _ * π _; rw [← map_mul]; rfl)
        map_zero' := Subtype.ext (by change π _ = 0; exact map_zero π)
        map_add' := fun a b => Subtype.ext (by change π _ = π _ + π _; rw [← map_add]; rfl) }
    have hπint : ∀ b : ↥B, IsIntegral ↥R₀ (π b) := by
      intro b
      obtain ⟨q, hqm, hqb⟩ := hBint b
      refine ⟨q.map πb, hqm.map πb, ?_⟩
      rw [Polynomial.eval₂_map]
      have hc : (algebraMap ↥R₀ ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H))).comp πb = π.comp (Subring.inclusion hbaseB) :=
        RingHom.ext fun _ => rfl
      rw [hc, ← Polynomial.hom_eval₂]
      have : Polynomial.eval₂ (Subring.inclusion hbaseB) b q = 0 := by
        apply Subtype.ext
        rw [show ((Polynomial.eval₂ (Subring.inclusion hbaseB) b q : ↥B) : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) =
          B.subtype (Polynomial.eval₂ (Subring.inclusion hbaseB) b q) from rfl, Polynomial.hom_eval₂]
        exact hqb
      rw [this, map_zero]
    letI : Algebra ↥R₀ ↥πS := (Subalgebra.inclusion hle).toRingHom.toAlgebra
    haveI : IsScalarTower ↥R₀ ↥πS ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : Algebra.IsIntegral ↥R₀ ↥πS := ⟨fun w => by
      obtain ⟨b, hb⟩ : ∃ b : ↥B, π b = (w : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H))) := w.2
      have h := hπint b
      rw [hb] at h
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥R₀ ↥πS ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H))) Subtype.val_injective).mp h⟩
    have hyS : IsIntegral ↥πS y := by obtain ⟨q, hqm, hqy⟩ := hy; exact ⟨q, hqm, hqy⟩
    have hyR : IsIntegral ↥R₀ y := isIntegral_trans y hyS

    have hyP : ∃ P : Polynomial (Polynomial (ResidueField ↥A)), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))) (jqModC (ResidueField ↥A)))
          (y : LaurentSeries (ResidueField ↥A)) P = 0 := by
      obtain ⟨q, hqm, hqy⟩ := hyR
      have hR₀ : R₀ = (Polynomial.aeval x).range := Algebra.adjoin_singleton_eq_range_aeval (ResidueField ↥A) x
      have hmem : ∀ q0 : Polynomial (ResidueField ↥A), Polynomial.aeval x q0 ∈ R₀ := fun q0 => by rw [hR₀]; exact ⟨q0, rfl⟩
      let σ : Polynomial (ResidueField ↥A) →+* ↥R₀ :=
        ((Polynomial.aeval x : Polynomial (ResidueField ↥A) →ₐ[ResidueField ↥A] _).toRingHom).codRestrict R₀.toSubring hmem
      have hσ : Function.Surjective σ := by
        rintro ⟨w, hw⟩
        have hw' : w ∈ (Polynomial.aeval x).range := hR₀ ▸ hw
        obtain ⟨q0, hq0⟩ := hw'
        exact ⟨q0, Subtype.ext hq0⟩
      obtain ⟨P, hPq, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic ((Polynomial.mem_lifts _).mpr (Polynomial.map_surjective σ hσ q)) hqm
      refine ⟨P, hPm, ?_⟩
      have h1 : Polynomial.eval₂ ((algebraMap ↥R₀ ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H))).comp σ) y P = 0 := by
        rw [← Polynomial.eval₂_map, hPq]; exact hqy
      have h2 : (algebraMap ↥R₀ ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H))).comp σ =
          (Polynomial.aeval x : Polynomial (ResidueField ↥A) →ₐ[ResidueField ↥A] _).toRingHom := RingHom.ext fun _ => rfl
      rw [h2] at h1
      have h3 := congrArg (fun z : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)) => (z : LaurentSeries (ResidueField ↥A))) h1
      simp only [ZeroMemClass.coe_zero] at h3
      rw [show ((Polynomial.eval₂ (Polynomial.aeval x : Polynomial (ResidueField ↥A) →ₐ[ResidueField ↥A] _).toRingHom y P :
            ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H))) : LaurentSeries (ResidueField ↥A)) =
          (qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)).val.toRingHom (Polynomial.eval₂ _ y P) from rfl,
        Polynomial.hom_eval₂] at h3
      have h4 : ((qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)).val.toRingHom).comp
          (Polynomial.aeval x : Polynomial (ResidueField ↥A) →ₐ[ResidueField ↥A] _).toRingHom =
          Polynomial.eval₂RingHom (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))) (jqModC (ResidueField ↥A)) := by
        apply Polynomial.ringHom_ext
        · intro c
          change ((Polynomial.aeval x (Polynomial.C c) : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H))) : LaurentSeries (ResidueField ↥A)) = _
          rw [Polynomial.aeval_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]; rfl
        · change ((Polynomial.aeval x Polynomial.X : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H))) : LaurentSeries (ResidueField ↥A)) = _
          rw [Polynomial.aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hx]
      rw [h4] at h3
      exact h3

    obtain ⟨f, hfO, hres, P', hP'm, hP'f⟩ :=
      (FisoShared.exists_mem_integers_residue_eq_of_isIntegral M (CohCarrier.GammaH M H) hΓ₁ hΓ₀ p hpM A hA Rg hRgint hRgpin).1 y hyP

    have hfint : IsIntegral ↥baseA f := by
      let θA : Polynomial ↥A →+* ↥baseA := (Polynomial.aeval (⟨g, Algebra.subset_adjoin rfl⟩ : ↥baseA)).toRingHom
      refine ⟨P'.map θA, hP'm.map θA, ?_⟩
      apply Subtype.ext
      rw [Polynomial.eval₂_map, ZeroMemClass.coe_zero,
        show ((Polynomial.eval₂ ((algebraMap ↥baseA _).comp θA) f P' : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) :
            LaurentSeries (AlgebraicClosure ℚ)) =
          (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))).val.toRingHom (Polynomial.eval₂ _ f P') from rfl,
        Polynomial.hom_eval₂]
      have h5 : ((laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))).val.toRingHom).comp
          ((algebraMap ↥baseA ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))).comp θA) =
          Polynomial.eval₂RingHom ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp A.subtype) (jqModC (AlgebraicClosure ℚ)) := by
        apply Polynomial.ringHom_ext
        · intro a
          change (((algebraMap ↥baseA ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (Polynomial.aeval _ (Polynomial.C a)) : _) : LaurentSeries (AlgebraicClosure ℚ)) = _
          rw [Polynomial.aeval_C, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
          change ((algebraMap ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) a : _) : LaurentSeries (AlgebraicClosure ℚ)) = _
          rw [hcT]; rfl
        · change (((algebraMap ↥baseA ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (Polynomial.aeval _ Polynomial.X) : _) : LaurentSeries (AlgebraicClosure ℚ)) = _
          rw [Polynomial.aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
          change (g : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)
          rw [hgcoe, hj]; exact map_jqModC _
      rw [h5]
      exact hP'f

    have hbase' : ∀ z ∈ base, ∃ t, ψ t = z := fun z hz => (hB z).mp (hbaseB hz)
    obtain ⟨t, ht⟩ := FisoK.b1' (CohCarrier.GammaH M H) p A S ψ hICψ hψ hcT g base hbase_adj hbase' hspan f
      (by obtain ⟨q, hqm, hqf⟩ := hfint; exact ⟨q, hqm, hqf⟩)
    have hfB : f ∈ B := (hB f).mpr ⟨t, ht⟩

    refine ⟨⟨f, hfB⟩, ?_⟩
    rw [hπ_apply]
    exact hres

  obtain ⟨eFin, hpin, hread⟩ := FisoK.assemble (CohCarrier.GammaH M H) p A S ψ hinj hICψ hψ hcT B base hbaseB g
    (TwoChartIntegralModel.jChartFin _ _ j) rfl hbase_le hgen hbase_adj hBint hSB hconstB hspan π x hgB hπg hπc hker hICπ rfl x
    (by rfl)
  refine ⟨eFin, hpin, ?_⟩
  intro b y hy
  have hb : ψ (FisoK.asEquiv (CohCarrier.GammaH M H) p A S ((1 : ↥A) ⊗ₜ b)) ∈ B := by rw [hψ, map_one, one_mul]; exact hSB b
  refine Eq.trans (congrArg (fun z : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)) => (z : LaurentSeries (ResidueField ↥A))) (hread b hb)) ?_

  have hymem : coeffMap A.subtype y ∈ laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by
    rw [hy]; exact (FisoK.embS (CohCarrier.GammaH M H) p S b).2
  obtain ⟨hyO, hyres⟩ := hRgres y hymem
  have heq : (⟨ψ (FisoK.asEquiv (CohCarrier.GammaH M H) p A S ((1 : ↥A) ⊗ₜ b)), hBO hb⟩ : ↥Rg.integers) =
      ⟨⟨coeffMap A.subtype y, hymem⟩, hyO⟩ := by
    apply Subtype.ext; apply Subtype.ext
    change ((ψ (FisoK.asEquiv (CohCarrier.GammaH M H) p A S ((1 : ↥A) ⊗ₜ b)) :
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffMap A.subtype y
    rw [hψ, map_one, one_mul]; exact hy.symm
  rw [IntermediateField.equivOfEq_rfl, AlgEquiv.refl_symm, AlgEquiv.coe_refl, id_eq, hπ_apply]
  exact (congrArg (fun z : ↥Rg.integers => ((Rg.residue z : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H))) : LaurentSeries (ResidueField ↥A))) heq).trans hyres

end
end S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_residueField_tensor_chartAlgFin_twoChartIntegralModel_qExpFunctionFieldC_chartRing (solution)
