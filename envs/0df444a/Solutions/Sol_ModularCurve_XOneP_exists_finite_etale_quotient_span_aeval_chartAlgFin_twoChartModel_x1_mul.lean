-- Prove2me | solution 1 for ModularCurve.XOneP.exists_finite_etale_quotient_span_aeval_chartAlgFin_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/bcb92c4a-fb59-59e3-a750-8594afc507dd

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1

import Theorems.Thm_Algebra_exists_etale_localizationAway_of_forall_isEtaleAt
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_pair_x1_mul
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_IsDiscreteValuationRing_maximalIdeal_eq_span_one_sub_of_isPrimitiveRoot
import Theorems.Thm_ModularCurve_XOneP_exists_modularUnit_mem_chartAlgFin_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries_of_not_dvd
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_XOneP_exists_forall_finite_quotient_span_aeval_and_finrank_le_chartAlgFin_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_isReduced_chartAlgFin_quotient_map_maximalIdeal_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_forall_isUnramifiedAt_quotient_span_aeval_of_comap_eq_bot_chartAlgFin_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_avoid_forall_formallyUnramified_quotient_gaussPrime_sup_span_aeval_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_modularUnit_notMem_and_mem_gaussPrime_chartAlgFin_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_and_coe_eq_atkinLehnerInvolutionFull_x1_mul
import Theorems.Thm_ModularCurve_XOneP_modularUnit_mem_and_notMem_farPrime_chartAlgFin_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_avoid_forall_formallyUnramified_quotient_farPrime_sup_span_aeval_twoChartModel_x1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_finite_etale_quotient_span_aeval_chartAlgFin_twoChartModel_x1_mul
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec"
p2m_attr_erase "simp" "ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun"
p2m_attr_erase "simp" "KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped Polynomial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
p2m_open "Polynomial AlgebraicGeometry.Polynomial IsLocalRing"

namespace ECL_N1asm

section TwoPrimes

variable {A : Type*} [CommRing A] {Pu Pz : Ideal A} [Pu.IsPrime] [Pz.IsPrime] {π x : A}

private theorem mem_span_of_mul_mem (hinf : Pu ⊓ Pz = Ideal.span {π}) (hxz : IsUnit (Ideal.Quotient.mk Pz x))
    (hxu : x ∉ Pu) {y : A} (h : x * y ∈ Ideal.span {π}) : y ∈ Ideal.span {π} := by
  rw [← hinf] at h ⊢
  refine ⟨(Ideal.IsPrime.mem_or_mem ‹Pu.IsPrime› h.1).resolve_left hxu, ?_⟩
  have h2 : Ideal.Quotient.mk Pz x * Ideal.Quotient.mk Pz y = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]; exact h.2
  show y ∈ Pz
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact (hxz.mul_right_eq_zero).1 h2

private theorem le_span_sup_span (hinf : Pu ⊓ Pz = Ideal.span {π}) (hxz : IsUnit (Ideal.Quotient.mk Pz x)) :
    Pu ≤ Ideal.span {π} ⊔ Ideal.span {x} := by
  intro y hy
  obtain ⟨w, hw⟩ := hxz.exists_right_inv
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hz : x * z - 1 ∈ Pz := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hw, map_one, sub_self]
  have hprod : (x * z - 1) * y ∈ Ideal.span {π} := by
    rw [← hinf]
    exact ⟨Pu.mul_mem_left _ hy, Pz.mul_mem_right _ hz⟩
  have : y = x * (z * y) - (x * z - 1) * y := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨z * y, by ring⟩))
    (Ideal.mem_sup_left hprod)

private theorem pi_mem (hinf : Pu ⊓ Pz = Ideal.span {π}) : π ∈ Pu :=
  (hinf.symm ▸ Ideal.mem_span_singleton_self π : π ∈ Pu ⊓ Pz).1

private theorem span_sup_span_eq (hinf : Pu ⊓ Pz = Ideal.span {π}) (hxz : IsUnit (Ideal.Quotient.mk Pz x)) :
    Ideal.span {π} ⊔ Ideal.span {x} = Pu ⊔ Ideal.span {x} :=
  le_antisymm (sup_le_sup_right ((Ideal.span_singleton_le_iff_mem _).2 (pi_mem hinf)) _)
    (sup_le (le_span_sup_span hinf hxz) le_sup_right)

end TwoPrimes

section IntTransport

private theorem formallyUnramified_int_congr {X : Type*} [CommRing X] (i₁ i₂ : Algebra ℤ X)
    (h : @Algebra.FormallyUnramified ℤ X _ _ i₁) : @Algebra.FormallyUnramified ℤ X _ _ i₂ := by
  have := Subsingleton.elim i₁ i₂; subst this; exact h

private theorem formallyUnramified_int_of_ringEquiv {X Y : Type*} [CommRing X] [CommRing Y] {iX : Algebra ℤ X}
    {iY : Algebra ℤ Y} (e : X ≃+* Y) (h : @Algebra.FormallyUnramified ℤ X _ _ iX) :
    @Algebra.FormallyUnramified ℤ Y _ _ iY := by
  have h' : @Algebra.FormallyUnramified ℤ X _ _ (Ring.toIntAlgebra X) := formallyUnramified_int_congr _ _ h
  refine formallyUnramified_int_congr (Ring.toIntAlgebra Y) iY ?_
  exact @Algebra.FormallyUnramified.of_equiv ℤ _ X Y _ (Ring.toIntAlgebra X) _ (Ring.toIntAlgebra Y) h'
    (@AlgEquiv.ofRingEquiv ℤ X Y _ _ _ (Ring.toIntAlgebra X) (Ring.toIntAlgebra Y) e (fun n => by simp))

private def algEquivOfRingEquiv' {R₀ : Type*} [CommRing R₀] {X Y : Type*} [CommRing X] [CommRing Y] [Algebra R₀ X] [Algebra R₀ Y]
    (f : X ≃+* Y) (h : ∀ r, f (algebraMap R₀ X r) = algebraMap R₀ Y r) : X ≃ₐ[R₀] Y :=
  AlgEquiv.ofRingEquiv (f := f) h

end IntTransport

section Transfer

variable {R₀ : Type*} [CommRing R₀] {A : Type*} [CommRing A] [Algebra R₀ A]

private theorem etale_quotient_of_algEquiv (I J : Ideal A) (f : A ≃ₐ[R₀] A) (h : J = I.map (f : A →+* A))
    [Algebra.Etale R₀ (A ⧸ I)] : Algebra.Etale R₀ (A ⧸ J) :=
  Algebra.Etale.of_equiv (Ideal.quotientEquivAlg I J f h)

private theorem finite_quotient_of_algEquiv (I J : Ideal A) (f : A ≃ₐ[R₀] A) (h : J = I.map (f : A →+* A))
    [Module.Finite R₀ (A ⧸ I)] : Module.Finite R₀ (A ⧸ J) :=
  Module.Finite.equiv (Ideal.quotientEquivAlg I J f h).toLinearEquiv

private theorem free_quotient_of_algEquiv (I J : Ideal A) (f : A ≃ₐ[R₀] A) (h : J = I.map (f : A →+* A))
    [Module.Free R₀ (A ⧸ I)] : Module.Free R₀ (A ⧸ J) :=
  Module.Free.of_equiv (Ideal.quotientEquivAlg I J f h).toLinearEquiv

private theorem finrank_quotient_of_algEquiv (I J : Ideal A) (f : A ≃ₐ[R₀] A) (h : J = I.map (f : A →+* A)) :
    Module.finrank R₀ (A ⧸ J) = Module.finrank R₀ (A ⧸ I) :=
  (LinearEquiv.finrank_eq (Ideal.quotientEquivAlg I J f h).toLinearEquiv).symm

private def fibreQuotEquiv (𝔪 : Ideal R₀) (I K : Ideal A) (hK : 𝔪.map (algebraMap R₀ A) ⊔ I = K) :
    ((A ⧸ I) ⧸ 𝔪.map (algebraMap R₀ (A ⧸ I))) ≃+* A ⧸ K :=
  (Ideal.quotEquivOfEq (by rw [Ideal.map_map, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_eq])).trans
    ((DoubleQuot.quotQuotEquivQuotSup I (𝔪.map (algebraMap R₀ A))).trans (Ideal.quotEquivOfEq (by rw [sup_comm, hK])))

private theorem formallyUnramified_fibre (𝔪 : Ideal R₀) (I K : Ideal A) (hK : 𝔪.map (algebraMap R₀ A) ⊔ I = K)
    (h : Algebra.FormallyUnramified ℤ (A ⧸ K)) :
    Algebra.FormallyUnramified ℤ ((A ⧸ I) ⧸ 𝔪.map (algebraMap R₀ (A ⧸ I))) :=
  formallyUnramified_int_of_ringEquiv (fibreQuotEquiv 𝔪 I K hK).symm h

end Transfer

section EtaleUnit

private theorem etale_of_etale_localizationAway_of_isUnit {R₀ S : Type*} [CommRing R₀] [CommRing S] [Algebra R₀ S]
    (c : R₀) (hc : IsUnit c)
    (het : letI := (Localization.awayMap (algebraMap R₀ S) c).toAlgebra
      Algebra.Etale (Localization.Away c) (Localization.Away (algebraMap R₀ S c))) :
    Algebra.Etale R₀ S := by
  letI := (Localization.awayMap (algebraMap R₀ S) c).toAlgebra
  haveI := het
  haveI : Algebra.Etale R₀ (Localization.Away c) :=
    ⟨Algebra.FormallyEtale.of_isLocalization (M := Submonoid.powers c), IsLocalization.Away.finitePresentation c⟩
  haveI : IsScalarTower R₀ (Localization.Away c) (Localization.Away (algebraMap R₀ S c)) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_comp,
      ← IsScalarTower.algebraMap_eq]
  haveI : Algebra.Etale R₀ (Localization.Away (algebraMap R₀ S c)) :=
    Algebra.Etale.comp R₀ (Localization.Away c) _
  let eS : S ≃ₐ[S] Localization.Away (algebraMap R₀ S c) :=
    IsLocalization.atUnits S (Submonoid.powers (algebraMap R₀ S c))
      (by rintro _ ⟨n, rfl⟩; exact (hc.map _).pow n)
  exact Algebra.Etale.of_equiv (eS.symm.restrictScalars R₀)

end EtaleUnit

section EtaleLocal

universe u

private theorem exists_etale_localizationAway_of_forall_isUnramifiedAt
    {R₀ S : Type u} [CommRing R₀] [IsDomain R₀] [CommRing S] [Algebra R₀ S]
    [Module.Finite R₀ S] [Algebra.FinitePresentation R₀ S] [Module.Flat R₀ S]
    (hgen : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], 𝔮.comap (algebraMap R₀ S) = ⊥ → Algebra.IsUnramifiedAt R₀ 𝔮)
    (𝔪 : Ideal R₀) [𝔪.IsPrime]
    (hfib : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], 𝔮.comap (algebraMap R₀ S) = 𝔪 → Algebra.IsUnramifiedAt R₀ 𝔮) :
    ∃ c : R₀, c ≠ 0 ∧ c ∉ 𝔪 ∧
      letI := (Localization.awayMap (algebraMap R₀ S) c).toAlgebra
      Algebra.Etale (Localization.Away c) (Localization.Away (algebraMap R₀ S c)) := by
  classical
  obtain ⟨c, hc0, hcT, het⟩ := Algebra.exists_etale_localizationAway_of_forall_isEtaleAt (R := R₀) (S := S)
    (fun 𝔮 h𝔮P h𝔮 => by
      haveI := h𝔮P
      haveI : Algebra.IsUnramifiedAt R₀ 𝔮 := hgen 𝔮 h𝔮
      exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat 𝔮)
    {𝔪}
    (fun Pm hPm => by rw [Finset.mem_singleton] at hPm; subst hPm; infer_instance)
    (fun Pm hPm 𝔮 h𝔮P h𝔮 => by
      rw [Finset.mem_singleton] at hPm
      subst hPm
      haveI := h𝔮P
      haveI : Algebra.IsUnramifiedAt R₀ 𝔮 := hfib 𝔮 h𝔮
      exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat 𝔮)
  exact ⟨c, hc0, hcT _ (Finset.mem_singleton_self _), het⟩

end EtaleLocal

section FibreUnram

private theorem isLocalHom_of_field {K L : Type*} [Field K] [CommRing L] [Nontrivial L] (f : K →+* L) : IsLocalHom f :=
  ⟨fun a ha => by
    rcases eq_or_ne a 0 with rfl | h
    · rw [map_zero] at ha; exact (not_isUnit_zero ha).elim
    · exact isUnit_iff_ne_zero.2 h⟩

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]

set_option maxHeartbeats 3200000 in

private theorem isUnramifiedAt_of_fibre (𝔭 : Ideal R) [𝔭.IsMaximal]
    (hκ : PerfectField 𝔭.ResidueField)
    (hF : Algebra.FormallyUnramified ℤ (S ⧸ 𝔭.map (algebraMap R S)))
    (q : Ideal S) [q.IsPrime] [q.LiesOver 𝔭] : Algebra.IsUnramifiedAt R q := by
  classical
  letI := Localization.AtPrime.algebraOfLiesOver 𝔭 q
  have hess : Algebra.EssFiniteType R S := inferInstance
  rw [Algebra.isUnramifiedAt_iff_map_eq R 𝔭 q]
  constructor
  · haveI := hκ
    haveI : Module.Finite 𝔭.ResidueField q.ResidueField := inferInstance
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  · set I : Ideal S := 𝔭.map (algebraMap R S) with hI
    have hJI : 𝔭.map (algebraMap R (Localization.AtPrime q)) = I.map (algebraMap S (Localization.AtPrime q)) := by
      rw [hI, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    rw [hJI]
    set J : Ideal (Localization.AtPrime q) := I.map (algebraMap S (Localization.AtPrime q)) with hJ
    haveI : (maximalIdeal (Localization.AtPrime q)).LiesOver 𝔭 := Ideal.LiesOver.trans _ q 𝔭
    have hJle : J ≤ maximalIdeal (Localization.AtPrime q) := by
      rw [← hJI, Ideal.map_le_iff_le_comap]
      exact le_of_eq (Ideal.LiesOver.over (p := 𝔭) (P := maximalIdeal (Localization.AtPrime q)))
    have hJtop : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hJle
    haveI : Nontrivial (Localization.AtPrime q ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJtop
    haveI : IsLocalRing (Localization.AtPrime q ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
    haveI : Algebra.FormallyUnramified (S ⧸ I) (Localization.AtPrime q ⧸ J) :=
      Algebra.FormallyUnramified.of_isLocalization (Algebra.algebraMapSubmonoid (S ⧸ I) q.primeCompl)
    have hT1 := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := S ⧸ I) (A := Localization.AtPrime q ⧸ J)
      (Subsingleton.elim _ _)
    haveI := hT1
    haveI : Algebra.FormallyUnramified ℤ (Localization.AtPrime q ⧸ J) :=
      Algebra.FormallyUnramified.comp ℤ (S ⧸ I) _

    have hTR := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := R) (A := Localization.AtPrime q ⧸ J) (Subsingleton.elim _ _)
    haveI := hTR
    haveI : Algebra.FormallyUnramified R (Localization.AtPrime q ⧸ J) :=
      Algebra.FormallyUnramified.of_restrictScalars ℤ R _
    letI hkf : Field (R ⧸ 𝔭) := Ideal.Quotient.field 𝔭
    have hker : ∀ a ∈ 𝔭, algebraMap R (Localization.AtPrime q ⧸ J) a = 0 := by
      intro a ha
      rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime q) (Localization.AtPrime q ⧸ J),
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, hJ, hI,
        IsScalarTower.algebraMap_apply R S (Localization.AtPrime q)]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
    letI hkalg : Algebra (R ⧸ 𝔭) (Localization.AtPrime q ⧸ J) :=
      (Ideal.Quotient.lift 𝔭 (algebraMap R (Localization.AtPrime q ⧸ J)) hker).toAlgebra
    haveI : IsScalarTower R (R ⧸ 𝔭) (Localization.AtPrime q ⧸ J) :=
      IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => by
        rw [RingHom.comp_apply, Ideal.Quotient.algebraMap_eq, RingHom.algebraMap_toAlgebra, Ideal.Quotient.lift_mk])
    haveI : IsLocalHom (algebraMap (R ⧸ 𝔭) (Localization.AtPrime q ⧸ J)) := isLocalHom_of_field _
    haveI : Algebra.FormallyUnramified (R ⧸ 𝔭) (Localization.AtPrime q ⧸ J) :=
      Algebra.FormallyUnramified.of_restrictScalars R (R ⧸ 𝔭) _
    haveI : Algebra.EssFiniteType R (Localization.AtPrime q ⧸ J) := by
      have : Algebra.EssFiniteType R (Localization.AtPrime q) := Algebra.EssFiniteType.comp R S _
      exact Algebra.EssFiniteType.comp R (Localization.AtPrime q) _
    haveI : Algebra.EssFiniteType (R ⧸ 𝔭) (Localization.AtPrime q ⧸ J) := Algebra.EssFiniteType.of_comp R (R ⧸ 𝔭) _
    have hmax : maximalIdeal (Localization.AtPrime q ⧸ J) = ⊥ := by
      rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R ⧸ 𝔭) (S := Localization.AtPrime q ⧸ J),
        IsLocalRing.maximalIdeal_eq_bot (R := R ⧸ 𝔭), Ideal.map_bot]
    refine le_antisymm hJle ?_
    have hne : (maximalIdeal (Localization.AtPrime q)).map (Ideal.Quotient.mk J) ≠ ⊤ := by
      rw [Ne, Ideal.map_eq_top_iff_of_ker_le (Ideal.Quotient.mk J) (by rw [Ideal.mk_ker]; exact hJle)
        (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)]
      exact (maximalIdeal.isMaximal _).ne_top
    have hle : (maximalIdeal (Localization.AtPrime q)).map (Ideal.Quotient.mk J) ≤ ⊥ :=
      hmax ▸ IsLocalRing.le_maximalIdeal hne
    intro z hz
    have hz' : Ideal.Quotient.mk J z ∈ (⊥ : Ideal (Localization.AtPrime q ⧸ J)) := hle (Ideal.mem_map_of_mem _ hz)
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hz'
    exact hz'

end FibreUnram

section BaseA

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

private theorem eq_bot_or_eq_maximalIdeal_A (𝔭 : Ideal A) [𝔭.IsPrime] : 𝔭 = ⊥ ∨ 𝔭 = maximalIdeal A := by
  by_cases h : 𝔭 = ⊥
  · exact Or.inl h
  · exact Or.inr (IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance h))

private theorem comap_eq_bot_or_eq_maximalIdeal_A {S : Type*} [CommRing S] [Algebra A S]
    (𝔮 : Ideal S) [𝔮.IsPrime] : 𝔮.comap (algebraMap A S) = ⊥ ∨ 𝔮.comap (algebraMap A S) = maximalIdeal A :=
  eq_bot_or_eq_maximalIdeal_A _

private theorem flat_of_uniformizer_torsionFree (ϖ : A) (hϖ : Irreducible ϖ) (S : Type*) [CommRing S] [Algebra A S]
    (h : ∀ s : S, algebraMap A S ϖ * s = 0 → s = 0) : Module.Flat A S := by
  haveI : Module.IsTorsionFree A S := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => ?_
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
    have hn : ∀ (k : ℕ) (m : S), algebraMap A S ϖ ^ k * m = 0 → m = 0 := by
      intro k
      induction k with
      | zero => intro m hm; simpa using hm
      | succ k ih => intro m hm; apply ih; apply h; rw [← mul_assoc, ← pow_succ']; exact hm
    apply hn n
    have := congrArg (fun z => ((v⁻¹ : Aˣ) : A) • z) hrm
    simp only [smul_smul, Units.inv_mul_cancel_left, smul_zero] at this
    rwa [Algebra.smul_def, map_pow] at this
  infer_instance

private theorem charP_quotient_of_natCast_mem_A (p : ℕ) (hp : p.Prime) {B : Type*} [CommRing B] (I : Ideal B) (hI : I ≠ ⊤)
    (h : ((p : ℕ) : B) ∈ I) : CharP (B ⧸ I) p := by
  haveI : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  refine (CharP.charP_iff_prime_eq_zero hp).mpr ?_
  rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
  exact h

private theorem perfectField_residueField_A (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ maximalIdeal A) : PerfectField (ResidueField A) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : CharP (ResidueField A) p :=
    charP_quotient_of_natCast_mem_A p hp (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top hAp
  letI : Algebra (ZMod p) (ResidueField A) := ZMod.algebra _ _
  haveI : Algebra.IsAlgebraic (ZMod p) (ResidueField A) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x

    have halgZ : IsAlgebraic ℤ (algebraMap A L a) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr (Algebra.IsAlgebraic.isAlgebraic _)
    obtain ⟨g, hg0, hga⟩ := halgZ
    set h : ℤ[X] := g.primPart with hh
    have hhprim : h.IsPrimitive := isPrimitive_primPart g
    have hha : aeval (algebraMap A L a) h = 0 := by
      have hc : g.content ≠ 0 := fun hc => hg0 (content_eq_zero_iff.mp hc)
      have := hga
      rw [eq_C_content_mul_primPart g, map_mul, aeval_C] at this
      refine (mul_eq_zero.mp this).resolve_left ?_
      rw [eq_intCast, Int.cast_eq_zero]; exact hc

    have hhaA : aeval a h = 0 := by
      apply IsFractionRing.injective A L
      rw [map_zero, ← hha, aeval_algebraMap_apply]

    obtain ⟨n, hn⟩ : ∃ n, ¬ (p : ℤ) ∣ h.coeff n := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      have hdvd : C (p : ℤ) ∣ h := (C_dvd_iff_dvd_coeff _ _).mpr hall
      have hu := (isPrimitive_iff_isUnit_of_C_dvd.mp hhprim) _ hdvd
      rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
      exact hp.ne_one hu
    refine ⟨h.map (Int.castRingHom (ZMod p)), ?_, ?_⟩
    · intro hz
      apply hn
      have := congrArg (fun q => q.coeff n) hz
      simp only [coeff_map, coeff_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact this
    · have h1 : aeval (residue A a) (h.map (Int.castRingHom (ZMod p))) = aeval (residue A a) h := by
        rw [aeval_def, aeval_def, eval₂_map]
        congr 1
        exact RingHom.ext_int _ _
      have h2 : aeval (residue A a) h = residue A (aeval a h) := by
        rw [aeval_def, aeval_def, hom_eval₂]
        congr 1
      rw [h1, h2, hhaA, map_zero]
  exact Algebra.IsAlgebraic.perfectField (K := ZMod p)

end BaseA

section BaseA2

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

private theorem perfectField_residue_A (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ maximalIdeal A) : PerfectField (maximalIdeal A).ResidueField := by
  have hperf : PerfectField (ResidueField A) := perfectField_residueField_A p L hAp
  letI hF : Field (A ⧸ maximalIdeal A) := inferInstanceAs (Field (ResidueField A))
  haveI : PerfectField (A ⧸ maximalIdeal A) := hperf
  haveI : Algebra.IsAlgebraic (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField := by
    refine ⟨fun x => ?_⟩
    obtain ⟨y, rfl⟩ := (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A)).2 x
    exact isAlgebraic_algebraMap y
  exact Algebra.IsAlgebraic.perfectField (K := A ⧸ maximalIdeal A)

end BaseA2

section Core

variable {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {O : Type} [CommRing O] [IsDomain O] [Algebra A O]

set_option maxHeartbeats 6400000 in
private theorem core (p : ℕ) [Fact p.Prime] (hAp : (p : A) ∈ maximalIdeal A)
    (hperf : PerfectField (maximalIdeal A).ResidueField)
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ}) (hinj : Function.Injective (algebraMap A O))
    (v : O) (Pl Pd : Ideal O) [Pl.IsPrime] [Pd.IsPrime]
    (hinf : Pl ⊓ Pd = Ideal.span {algebraMap A O ϖ})
    (hvd : v ∈ Pd)
    (hvl : ∀ g : ℤ[X], g.Monic → 0 < g.natDegree → aeval v g ∉ Pl)
    (Kb : ℕ) (hFIN : ∀ g : ℤ[X], g.Monic → (g.map (Int.castRingHom (ZMod p))).coeff 0 ≠ 0 →
      Module.Finite A (O ⧸ Ideal.span {aeval v g}) ∧ Module.finrank A (O ⧸ Ideal.span {aeval v g}) ≤ Kb * g.natDegree)
    (c₀ : ℤ[X]) (hGEN : ∀ g : ℤ[X], g.Monic → Irreducible (g.map (Int.castRingHom ℚ)) → ¬ g ∣ c₀ →
      ∀ (Q : Ideal (O ⧸ Ideal.span {aeval v g})) [Q.IsPrime],
        Q.comap (algebraMap A (O ⧸ Ideal.span {aeval v g})) = ⊥ → Algebra.IsUnramifiedAt A Q)
    (avoid : (ZMod p)[X]) (hSPEC : ∀ h : ℤ[X], 0 < (h.map (Int.castRingHom (ZMod p))).natDegree →
      (h.map (Int.castRingHom (ZMod p))).Separable → IsCoprime (h.map (Int.castRingHom (ZMod p))) avoid →
        Nontrivial (O ⧸ (Pl ⊔ Ideal.span {aeval v h})) ∧ Algebra.FormallyUnramified ℤ (O ⧸ (Pl ⊔ Ideal.span {aeval v h})))
    (g : ℤ[X]) (hg : g.Monic) (hD : 1 ≤ g.natDegree) (hirr : Irreducible (g.map (Int.castRingHom (ZMod p))))
    (hcop : IsCoprime (g.map (Int.castRingHom (ZMod p))) (X * avoid)) (hndvd : ¬ g ∣ c₀) :
    Module.Finite A (O ⧸ Ideal.span {aeval v g}) ∧ Algebra.Etale A (O ⧸ Ideal.span {aeval v g}) ∧
      Module.Free A (O ⧸ Ideal.span {aeval v g}) ∧ 1 ≤ Module.finrank A (O ⧸ Ideal.span {aeval v g}) ∧
      Module.finrank A (O ⧸ Ideal.span {aeval v g}) ≤ Kb * g.natDegree := by
  classical
  have hp : p.Prime := Fact.out

  have hcopX : IsCoprime (g.map (Int.castRingHom (ZMod p))) X := hcop.of_mul_right_left
  have hcopA : IsCoprime (g.map (Int.castRingHom (ZMod p))) avoid := hcop.of_mul_right_right
  have hg0bar : (g.map (Int.castRingHom (ZMod p))).coeff 0 ≠ 0 := fun h =>
    Polynomial.not_isUnit_X (hcopX.isUnit_of_dvd' (Polynomial.X_dvd_iff.2 h) dvd_rfl)
  have hg0p : ¬ (p : ℤ) ∣ g.coeff 0 := by
    intro h; apply hg0bar
    rw [coeff_map, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h
  haveI : PerfectField (ZMod p) := PerfectField.ofFinite
  have hsep : (g.map (Int.castRingHom (ZMod p))).Separable := PerfectField.separable_of_irreducible hirr
  have hDbar : 0 < (g.map (Int.castRingHom (ZMod p))).natDegree := by rw [hg.natDegree_map]; exact hD

  obtain ⟨hfin, hrank⟩ := hFIN g hg hg0bar
  haveI := hfin

  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  set π : O := algebraMap A O ϖ with hπ
  have hπne : π ≠ 0 := fun h => hϖirr.ne_zero (hinj (by rw [map_zero]; exact h))
  have hπd : π ∈ Pd := (hinf.symm ▸ Ideal.mem_span_singleton_self π : π ∈ Pl ⊓ Pd).2
  have hpd : (p : O) ∈ Pd := by
    have h1 : (p : A) ∈ Ideal.span {ϖ} := hϖ ▸ hAp
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
    have : (p : O) = algebraMap A O c * π := by rw [hπ, ← map_mul, hc, map_natCast]
    rw [this]; exact Pd.mul_mem_left _ hπd

  have hcharPd : CharP (O ⧸ Pd) p := by
    haveI : Nontrivial (O ⧸ Pd) := Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
    have hp0 : ((p : ℕ) : O ⧸ Pd) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk Pd), Ideal.Quotient.eq_zero_iff_mem]; exact hpd
    have hdvd : ringChar (O ⧸ Pd) ∣ p := (ringChar.spec _ p).1 hp0
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | hp'
    · exact absurd h1 CharP.ringChar_ne_one
    · have := ringChar.charP (O ⧸ Pd); rwa [hp'] at this
  have hxz : IsUnit (Ideal.Quotient.mk Pd (aeval v g)) := by
    have h1 : Ideal.Quotient.mk Pd (aeval v g) = Ideal.Quotient.mk Pd (algebraMap ℤ O (g.coeff 0)) := by
      rw [← Ideal.Quotient.algebraMap_eq, ← aeval_algebraMap_apply, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 hvd, aeval_def, eval₂_at_zero]
      exact RingHom.congr_fun (Subsingleton.elim (algebraMap ℤ (O ⧸ Pd)) ((Ideal.Quotient.mk Pd).comp (algebraMap ℤ O))) _
    rw [h1]
    haveI := hcharPd
    have h2 : Ideal.Quotient.mk Pd (algebraMap ℤ O (g.coeff 0)) = ZMod.castHom (dvd_refl p) (O ⧸ Pd) (g.coeff 0 : ZMod p) := by
      rw [map_intCast]
      exact RingHom.congr_fun (Subsingleton.elim ((Ideal.Quotient.mk Pd).comp (algebraMap ℤ O)) (Int.castRingHom _)) _
    rw [h2]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hg0p

  have hxu : aeval v g ∉ Pl := hvl g hg hD

  have hnzd : ∀ y : O, aeval v g * y ∈ Ideal.span {π} → y ∈ Ideal.span {π} :=
    fun y hy => mem_span_of_mul_mem hinf hxz hxu hy
  have htf : ∀ b : O ⧸ Ideal.span {aeval v g}, algebraMap A (O ⧸ Ideal.span {aeval v g}) ϖ * b = 0 → b = 0 := by
    intro b hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [IsScalarTower.algebraMap_apply A O (O ⧸ Ideal.span {aeval v g}), Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hb
    obtain ⟨y, hy⟩ := hb
    have hyq : y ∈ Ideal.span {π} := hnzd y (Ideal.mem_span_singleton.2 ⟨a, hy.symm⟩)
    obtain ⟨y', rfl⟩ := Ideal.mem_span_singleton.1 hyq
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    refine ⟨y', mul_left_cancel₀ hπne ?_⟩
    rw [← hπ] at hy
    rw [hy]; ring
  haveI hflat : Module.Flat A (O ⧸ Ideal.span {aeval v g}) := flat_of_uniformizer_torsionFree ϖ hϖirr _ htf
  haveI hfree : Module.Free A (O ⧸ Ideal.span {aeval v g}) := Module.free_of_flat_of_isLocalRing

  have hirrZ : Irreducible g := hg.irreducible_of_irreducible_map (Int.castRingHom (ZMod p)) _ hirr
  have hirrQ : Irreducible (g.map (Int.castRingHom ℚ)) := (hg.irreducible_iff_irreducible_map_fraction_map).1 hirrZ
  obtain ⟨hnt, hFU⟩ := hSPEC g hDbar hsep hcopA
  have hIdeal : Ideal.span {π} ⊔ Ideal.span {aeval v g} = Pl ⊔ Ideal.span {aeval v g} := span_sup_span_eq hinf hxz
  have hK : (maximalIdeal A).map (algebraMap A O) ⊔ Ideal.span {aeval v g} = Pl ⊔ Ideal.span {aeval v g} := by
    rw [hϖ, Ideal.map_span, Set.image_singleton]; exact hIdeal
  have hF := formallyUnramified_fibre (maximalIdeal A) (Ideal.span {aeval v g}) _ hK hFU

  haveI : Algebra.FinitePresentation A (O ⧸ Ideal.span {aeval v g}) :=
    (Algebra.FinitePresentation.of_finiteType (R := A) (A := O ⧸ Ideal.span {aeval v g})).mp inferInstance
  obtain ⟨c, hc0, hcm, het⟩ := exists_etale_localizationAway_of_forall_isUnramifiedAt (R₀ := A) (S := O ⧸ Ideal.span {aeval v g})
    (fun 𝔮 _ h𝔮 => hGEN g hg hirrQ hndvd 𝔮 h𝔮)
    (maximalIdeal A)
    (fun 𝔮 h𝔮P h𝔮 => by
      haveI := h𝔮P
      haveI : 𝔮.LiesOver (maximalIdeal A) := ⟨h𝔮.symm⟩
      exact isUnramifiedAt_of_fibre (maximalIdeal A) hperf hF 𝔮)
  have hcu : IsUnit c := by
    by_contra hc
    exact hcm ((IsLocalRing.mem_maximalIdeal c).2 hc)
  have hEt : Algebra.Etale A (O ⧸ Ideal.span {aeval v g}) := etale_of_etale_localizationAway_of_isUnit c hcu het

  haveI : Nontrivial (O ⧸ Ideal.span {aeval v g}) :=
    (Ideal.Quotient.factor (le_sup_right : Ideal.span {aeval v g} ≤ Pl ⊔ Ideal.span {aeval v g})).domain_nontrivial
  have hpos : 0 < Module.finrank A (O ⧸ Ideal.span {aeval v g}) :=
    (Module.finrank_pos_iff_of_free A (O ⧸ Ideal.span {aeval v g})).2 inferInstance
  exact ⟨hfin, hEt, hfree, hpos, hrank⟩

end Core

end ECL_N1asm

set_option quotPrecheck false in
set_option hygiene false in
local notation "𝒪" => ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)

open ECL_N1asm in
set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
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
    (v : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hv : ((v : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p) ∨
      ((v : ↥K) : LaurentSeries L) = (p : LaurentSeries L) ^ 12 * (ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p))⁻¹) :
    ∃ (avoid : Polynomial (ZMod p)) (_ : avoid ≠ 0) (c₀ : Polynomial ℤ) (_ : c₀ ≠ 0) (Kb : ℕ),
      ∀ g : Polynomial ℤ, g.Monic → 1 ≤ g.natDegree → Irreducible (g.map (Int.castRingHom (ZMod p))) →
        IsCoprime (g.map (Int.castRingHom (ZMod p))) avoid → ¬ g ∣ c₀ →
          Module.Finite A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          Algebra.Etale A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          Module.Free A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          1 ≤ Module.finrank A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          Module.finrank A (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ Ideal.span {Polynomial.aeval v g}) ≤ Kb * g.natDegree := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  obtain ⟨z, hz⟩ := hζA
  have hϖ : maximalIdeal A = Ideal.span {1 - z} :=
    IsDiscreteValuationRing.maximalIdeal_eq_span_one_sub_of_isPrimitiveRoot p L ζ hζ A hAp z hz
  haveI : Module.Finite ℚ L := IsCyclotomicExtension.finite {p} ℚ L
  haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  have hperf : PerfectField (maximalIdeal A).ResidueField := ECL_N1asm.perfectField_residue_A p L hAp
  have hinjK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L)
  have hinj : Function.Injective (algebraMap A 𝒪) := by
    intro a b h
    apply hinjK
    have := congrArg (fun x : 𝒪 => (x : ↥K)) h
    simpa only [Subalgebra.coe_algebraMap] using this

  obtain ⟨w⟩ := ModularCurve.nonempty_integralWeightOneForm (IsLocalRing.ResidueField A) M (by omega)
  obtain ⟨W₀, W₁, h1, h2, h3, h4, h5, -, -⟩ :=
    ModularCurve.XOneP.exists_valuationSubring_pair_x1_mul p M hM hpM L ζ hζ K hK A hAp ⟨z, hz⟩ j hj w

  obtain ⟨σ, -, hσO, hσW, hσAL⟩ :=
    ModularCurve.XOneP.exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_and_coe_eq_atkinLehnerInvolutionFull_x1_mul
      p M hM hpM L ζ hζ K hK A hAp ⟨z, hz⟩ j hj
  obtain ⟨hσne, hσP⟩ := hσW W₀ h4
  have hcommA : ∀ a : A, σ (algebraMap A ↥K a) = algebraMap A ↥K a := fun a => by
    rw [IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes]
  have hnu : ∀ (B : ValuationSubring ↥K) (x : ↥K), x ∈ B.nonunits ↔ x ∈ B ∧ (x = 0 ∨ x⁻¹ ∉ B) := by
    intro B x
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    constructor
    · rintro ⟨hx, hm⟩
      refine ⟨hx, ?_⟩
      by_cases h0 : x = 0
      · exact Or.inl h0
      · right
        intro hinv
        apply (IsLocalRing.mem_maximalIdeal _).mp hm
        exact isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
    · rintro ⟨hx, h⟩
      refine ⟨hx, (IsLocalRing.mem_maximalIdeal _).mpr ?_⟩
      intro hu
      rcases h with h0 | hinv
      · subst h0
        have hz : (⟨0, hx⟩ : B) = 0 := rfl
        rw [hz] at hu
        exact not_isUnit_zero hu
      · obtain ⟨u, hu⟩ := hu.exists_right_inv
        apply hinv
        have hux : ((u : B) : ↥K) = x⁻¹ := by
          have := congrArg Subtype.val hu
          simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
          have h0 : x ≠ 0 := fun e => by rw [e, zero_mul] at this; exact zero_ne_one this
          exact (eq_inv_of_mul_eq_one_right this)
        rw [← hux]; exact u.2
  have hmemc : ∀ x : ↥K, x ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ↔ σ x ∈ W₀ := fun x => Iff.rfl
  have hnuc : ∀ x : ↥K, x ∈ (W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom).nonunits ↔ σ x ∈ W₀.nonunits := by
    intro x
    rw [hnu, hnu, hmemc, hmemc, map_inv₀, map_eq_zero_iff σ σ.injective]
  have hσW₁ : W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom = W₁ := by
    rcases h5 _ (fun a => by rw [hmemc, hcommA]; exact (h1 0).1 a)
        (fun a ha => by rw [hnuc, hcommA]; exact (h1 0).2 a ha) hσP with h | h
    · exact absurd h hσne
    · exact h
  have hW₁ : ∀ f : ↥K, f ∈ W₁ ↔ σ f ∈ W₀ := fun f => by rw [← hσW₁]; rfl
  have hσ𝒪 : ∀ b : ↥K, b ∈ ModularCurve.TwoChart.chartAlgFin A (↥K) j ↔ σ b ∈ ModularCurve.TwoChart.chartAlgFin A (↥K) j :=
    hσO

  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp.ne_zero⟩
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T]
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by
    subst hK
    exact ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CongruenceSubgroup.Gamma1 (M * p))
      hT L (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) rfl j hj
  haveI hsepK : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by
    haveI := hFD; exact Algebra.IsSeparable.of_integral _ _
  obtain ⟨hmin, hcen, -, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_span_iff_of_valuationSubring_pair A L (↥K) j htj hFD hsepK
      (1 - z) hϖ W₀ W₁ h1 h2 h3 h5
  obtain ⟨P₀, hP₀min, hP₀⟩ := hcen 0
  obtain ⟨P₁, hP₁min, hP₁⟩ := hcen 1
  set π : 𝒪 := algebraMap A 𝒪 (1 - z) with hπ
  change Ideal 𝒪 at P₀ P₁
  change P₀ ∈ (Ideal.span {π}).minimalPrimes at hP₀min
  change P₁ ∈ (Ideal.span {π}).minimalPrimes at hP₁min
  change ∀ b : 𝒪, b ∈ P₀ ↔ (b : ↥K) ∈ (![W₀, W₁] 0).nonunits at hP₀
  change ∀ b : 𝒪, b ∈ P₁ ↔ (b : ↥K) ∈ (![W₀, W₁] 1).nonunits at hP₁
  change ∀ 𝔭 ∈ (Ideal.span {π}).minimalPrimes,
    (∀ b : 𝒪, b ∈ 𝔭 ↔ (b : ↥K) ∈ W₀.nonunits) ∨ (∀ b : 𝒪, b ∈ 𝔭 ↔ (b : ↥K) ∈ W₁.nonunits) at hmin
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hP₀ hP₁
  haveI hP₀pr : P₀.IsPrime := hP₀min.1.1
  haveI hP₁pr : P₁.IsPrime := hP₁min.1.1
  have hmpeq : (Ideal.span {π}).minimalPrimes = {P₀, P₁} := by
    ext 𝔭
    constructor
    · intro h𝔭
      rcases hmin 𝔭 h𝔭 with h | h
      · left; ext b; rw [h b, hP₀ b]
      · right; ext b; rw [h b, hP₁ b]
    · rintro (rfl | rfl)
      · exact hP₀min
      · exact hP₁min
  have hmapspan : (maximalIdeal A).map (algebraMap A 𝒪) = Ideal.span {π} := by
    rw [hϖ, Ideal.map_span, Set.image_singleton]
  have hinf : P₀ ⊓ P₁ = Ideal.span {π} := by
    have hred := ModularCurve.XOneP.isReduced_chartAlgFin_quotient_map_maximalIdeal_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp ⟨z, hz⟩ j hj
    rw [hmapspan] at hred
    have hrad : (Ideal.span {π}).IsRadical := (Ideal.isRadical_iff_quotient_reduced _).2 hred
    have h : sInf (Ideal.span {π}).minimalPrimes = (Ideal.span {π}).radical := Ideal.sInf_minimalPrimes
    rw [hmpeq, hrad.radical] at h
    simpa [sInf_insert] using h

  obtain ⟨u, u', hu, hu', -⟩ :=
    ModularCurve.XOneP.exists_modularUnit_mem_chartAlgFin_twoChartModel_x1_mul p M hM hpM L ζ hζ K hK A hAp ⟨z, hz⟩ j hj
  have hmemq : ModularCurve.modularUnitSeries p ∈ ModularCurve.modularFunctionFieldFull (M * p) := by
    have hle : ModularCurve.modularFunctionFieldFull p ≤ ModularCurve.modularFunctionFieldFull (M * p) := by
      apply IntermediateField.adjoin.mono
      rintro x ⟨d, hd, hdq, rfl⟩
      exact ⟨d, hd, hdq.trans (dvd_mul_left p M), rfl⟩
    exact hle (ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull p)
  have hσu : σ (u : ↥K) = (u' : ↥K) := by
    have hfK : ModularCurve.coeffEmb L ((⟨ModularCurve.modularUnitSeries p, hmemq⟩ :
        ↥(ModularCurve.modularFunctionFieldFull (M * p))) : LaurentSeries ℚ) ∈ K := by
      show ModularCurve.coeffEmb L (ModularCurve.modularUnitSeries p) ∈ K
      rw [← hu]; exact (u : ↥K).2
    have e1 := hσAL ⟨ModularCurve.modularUnitSeries p, hmemq⟩ hfK
    rw [ModularCurve.coe_atkinLehnerInvolutionFull_modularUnitSeries_of_not_dvd M p hpM hmemq,
      ← HahnSeries.C_mul_eq_smul, map_pow, map_natCast] at e1
    have e2 : (⟨ModularCurve.coeffEmb L ((⟨ModularCurve.modularUnitSeries p, hmemq⟩ :
        ↥(ModularCurve.modularFunctionFieldFull (M * p))) : LaurentSeries ℚ), hfK⟩ : ↥K) = (u : ↥K) :=
      Subtype.ext hu.symm
    rw [e2] at e1
    apply Subtype.ext
    rw [e1, hu', map_mul, map_pow, map_natCast, map_inv₀]

  rcases hv with hv | hv
  ·
    have hvu : v = u := Subtype.ext (Subtype.ext (by rw [hv, hu]))
    subst hvu
    obtain ⟨-, -, hgu0⟩ :=
      ModularCurve.XOneP.modularUnit_notMem_and_mem_gaussPrime_chartAlgFin_twoChartModel_x1_mul
        p M hM hpM L ζ hζ K hK A hAp ⟨z, hz⟩ j hj v u' hu hu' W₀ h4 P₀ hP₀
    obtain ⟨hu1, -, -⟩ :=
      ModularCurve.XOneP.modularUnit_mem_and_notMem_farPrime_chartAlgFin_twoChartModel_x1_mul
        p M hM hpM L ζ hζ K hK A hAp ⟨z, hz⟩ j hj v u' hu hu' W₀ h4 σ hσu W₁ hW₁ P₁ hP₁
    obtain ⟨avoid, havoid, hSPEC⟩ :=
      ModularCurve.XOneP.exists_avoid_forall_formallyUnramified_quotient_gaussPrime_sup_span_aeval_twoChartModel_x1_mul
        p M hM hpM L ζ hζ K hK A hAp ⟨z, hz⟩ j hj v hu W₀ h4 P₀ hP₀
    obtain ⟨c₀, hc₀, hGEN⟩ :=
      ModularCurve.XOneP.exists_forall_isUnramifiedAt_quotient_span_aeval_of_comap_eq_bot_chartAlgFin_twoChartModel_x1_mul
        p M hM hpM L ζ hζ K hK A hAp ⟨z, hz⟩ j hj v (Or.inl hu)
    obtain ⟨Kb, hFIN⟩ :=
      ModularCurve.XOneP.exists_forall_finite_quotient_span_aeval_and_finrank_le_chartAlgFin_twoChartModel_x1_mul
        p M hM hpM L ζ hζ K hK A hAp ⟨z, hz⟩ j hj v (Or.inl hu)
    refine ⟨X * avoid, mul_ne_zero X_ne_zero havoid, c₀, hc₀, Kb, fun g hg hD hirr hcop hndvd => ?_⟩
    exact ECL_N1asm.core p hAp hperf (1 - z) hϖ hinj v P₀ P₁ hinf hu1 hgu0 Kb hFIN c₀ hGEN avoid hSPEC
      g hg hD hirr hcop hndvd
  ·
    have hvu : v = u' := Subtype.ext (Subtype.ext (by rw [hv, hu']))
    subst hvu
    obtain ⟨-, hu'0, -⟩ :=
      ModularCurve.XOneP.modularUnit_notMem_and_mem_gaussPrime_chartAlgFin_twoChartModel_x1_mul
        p M hM hpM L ζ hζ K hK A hAp ⟨z, hz⟩ j hj u v hu hu' W₀ h4 P₀ hP₀
    obtain ⟨-, -, hgu'1⟩ :=
      ModularCurve.XOneP.modularUnit_mem_and_notMem_farPrime_chartAlgFin_twoChartModel_x1_mul
        p M hM hpM L ζ hζ K hK A hAp ⟨z, hz⟩ j hj u v hu hu' W₀ h4 σ hσu W₁ hW₁ P₁ hP₁
    obtain ⟨avoid, havoid, hSPEC⟩ :=
      ModularCurve.XOneP.exists_avoid_forall_formallyUnramified_quotient_farPrime_sup_span_aeval_twoChartModel_x1_mul
        p M hM hpM L ζ hζ K hK A hAp ⟨z, hz⟩ j hj u v hu hu' W₀ h4 σ hσu hσ𝒪 W₁ hW₁ P₁ hP₁
    obtain ⟨c₀, hc₀, hGEN⟩ :=
      ModularCurve.XOneP.exists_forall_isUnramifiedAt_quotient_span_aeval_of_comap_eq_bot_chartAlgFin_twoChartModel_x1_mul
        p M hM hpM L ζ hζ K hK A hAp ⟨z, hz⟩ j hj v (Or.inr hu')
    obtain ⟨Kb, hFIN⟩ :=
      ModularCurve.XOneP.exists_forall_finite_quotient_span_aeval_and_finrank_le_chartAlgFin_twoChartModel_x1_mul
        p M hM hpM L ζ hζ K hK A hAp ⟨z, hz⟩ j hj v (Or.inr hu')
    have hinf' : P₁ ⊓ P₀ = Ideal.span {π} := by rw [inf_comm]; exact hinf
    refine ⟨X * avoid, mul_ne_zero X_ne_zero havoid, c₀, hc₀, Kb, fun g hg hD hirr hcop hndvd => ?_⟩
    exact ECL_N1asm.core p hAp hperf (1 - z) hϖ hinj v P₁ P₀ hinf' hu'0 hgu'1 Kb hFIN c₀ hGEN avoid hSPEC
      g hg hD hirr hcop hndvd

end

end S_ModularCurve_XOneP_exists_finite_etale_quotient_span_aeval_chartAlgFin_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_finite_etale_quotient_span_aeval_chartAlgFin_twoChartModel_x1_mul (solution)
