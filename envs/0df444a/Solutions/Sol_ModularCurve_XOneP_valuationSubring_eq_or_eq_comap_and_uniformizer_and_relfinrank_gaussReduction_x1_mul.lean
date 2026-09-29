-- Prove2me | solution 1 for ModularCurve.XOneP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/10df7194-79f7-5cbd-918b-30f5a648d927

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_XOneP_exists_gaussValuationSubring_x1_mul
import Theorems.Thm_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
import Theorems.Thm_ValuationSubring_exists_ideal_integralClosure_eq_valuationSubringAtPrime_and_inertiaDeg_eq_finrank
import Theorems.Thm_IsDiscreteValuationRing_primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_XOneP_relfinrank_laurentBaseChange_x1FunctionField_le_x1_mul
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_isKummerGenerator_hasseRootFn_and_relfinrank_igusaFunctionFieldX1C
import Theorems.Thm_ModularForm_exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq
import Theorems.Thm_ModularCurve_XOneP_exists_gaussReduction_eq_hasseRootFn_and_relfinrank_igusaFunctionFieldX1C_of_lt_five
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_exists_valuationSubring_adjoin_isDiscreteValuationRing_mem_iff_of_laurentBaseChange_x1FunctionField
import Theorems.Thm_ModularCurve_exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_pow_adjoin_jqModC_eq
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_XOneP_finrank_adjoin_j_eq_relfinrank_adjoin_jqModC_x1FunctionFieldC_of_x1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq"
p2m_attr_erase "simp" "CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP"
p2m_attr_erase "simp" "ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

open CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm

noncomputable section

namespace S1cAux

theorem exists_reductionField
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hA : ∀ a : A, algebraMap A ↥K a ∈ W₀)
    (hnu : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0)) :
    ∃ R₀ : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)),
      ∀ z : LaurentSeries (IsLocalRing.ResidueField A), z ∈ R₀ ↔
        ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z := by
  classical
  obtain ⟨red, hred, hker⟩ :=
    ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
      L K A W₀ hW₀ hnu

  have hconst : ∀ a : A, red ⟨algebraMap A ↥K a, hA a⟩ =
      algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))
        (IsLocalRing.residue A a) := by
    intro a
    have h1 : (1 : PowerSeries A).map (IsLocalRing.residue A) ≠ 0 := by rw [map_one]; exact one_ne_zero
    have hpres : ((⟨algebraMap A ↥K a, hA a⟩ : ↥W₀) : ↥K) = algebraMap A ↥K a := rfl
    have h2 : ((algebraMap A ↥K a : ↥K) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ L ((1 : PowerSeries A).map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L ((PowerSeries.C a).map (algebraMap A L)) := by
      rw [map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C,
        IsScalarTower.algebraMap_apply A L ↥K]
      show algebraMap L (LaurentSeries L) (algebraMap A L a) = _
      rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
    rw [hred _ (PowerSeries.C a) 1 h1 (by rw [hpres]; exact h2), PowerSeries.map_C, map_one, map_one,
      div_one, HahnSeries.ofPowerSeries_C, algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  let R₀ : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) :=
    { carrier := Set.range red
      mul_mem' := by
        rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
        exact ⟨f * g, map_mul red f g⟩
      one_mem' := ⟨1, map_one red⟩
      add_mem' := by
        rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
        exact ⟨f + g, map_add red f g⟩
      zero_mem' := ⟨0, map_zero red⟩
      algebraMap_mem' := by
        intro c
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
        exact ⟨_, hconst a⟩
      inv_mem' := by
        rintro _ ⟨f, rfl⟩
        by_cases hz : red f = 0
        · rw [hz, inv_zero]; exact ⟨0, map_zero red⟩
        · have hf : f ∉ IsLocalRing.maximalIdeal ↥W₀ := by
            rw [← hker]; exact hz
          have hu : IsUnit f := by
            by_contra h
            exact hf ((IsLocalRing.mem_maximalIdeal f).mpr h)
          obtain ⟨u, rfl⟩ := hu
          exact ⟨↑u⁻¹, map_units_inv red u⟩ }
  refine ⟨R₀, fun z => ⟨?_, ?_⟩⟩
  · rintro ⟨f, rfl⟩
    obtain ⟨x, y, hy, hxy⟩ := (hW₀ (f : ↥K)).mp f.2
    exact ⟨f, x, y, hy, hxy, (hred f x y hy hxy).symm⟩
  · rintro ⟨f, x, y, hy, hxy, rfl⟩
    have hf : f ∈ W₀ := (hW₀ f).mpr ⟨x, y, hy, hxy⟩
    exact ⟨⟨f, hf⟩, hred ⟨f, hf⟩ x y hy hxy⟩

theorem exists_red_and_reductionField
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hA : ∀ a : A, algebraMap A ↥K a ∈ W₀)
    (hnu : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0)) :
    ∃ (red : ↥W₀ →+* LaurentSeries (IsLocalRing.ResidueField A))
      (R₀ : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))),
      (∀ (f : ↥W₀) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        ((f : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        red f = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))) ∧
      RingHom.ker red = IsLocalRing.maximalIdeal ↥W₀ ∧
      (∀ a : A, red ⟨algebraMap A ↥K a, hA a⟩ =
        algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))
          (IsLocalRing.residue A a)) ∧
      (∀ z : LaurentSeries (IsLocalRing.ResidueField A), z ∈ R₀ ↔ ∃ w : ↥W₀, red w = z) ∧
      (∀ z : LaurentSeries (IsLocalRing.ResidueField A), z ∈ R₀ ↔
        ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z) := by
  classical
  obtain ⟨red, hred, hker⟩ :=
    ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
      L K A W₀ hW₀ hnu

  have hconst : ∀ a : A, red ⟨algebraMap A ↥K a, hA a⟩ =
      algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A))
        (IsLocalRing.residue A a) := by
    intro a
    have h1 : (1 : PowerSeries A).map (IsLocalRing.residue A) ≠ 0 := by rw [map_one]; exact one_ne_zero
    have hpres : ((⟨algebraMap A ↥K a, hA a⟩ : ↥W₀) : ↥K) = algebraMap A ↥K a := rfl
    have h2 : ((algebraMap A ↥K a : ↥K) : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ L ((1 : PowerSeries A).map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L ((PowerSeries.C a).map (algebraMap A L)) := by
      rw [map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C,
        IsScalarTower.algebraMap_apply A L ↥K]
      show algebraMap L (LaurentSeries L) (algebraMap A L a) = _
      rw [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
    rw [hred _ (PowerSeries.C a) 1 h1 (by rw [hpres]; exact h2), PowerSeries.map_C, map_one, map_one,
      div_one, HahnSeries.ofPowerSeries_C, algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  let R₀ : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) :=
    { carrier := Set.range red
      mul_mem' := by
        rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
        exact ⟨f * g, map_mul red f g⟩
      one_mem' := ⟨1, map_one red⟩
      add_mem' := by
        rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
        exact ⟨f + g, map_add red f g⟩
      zero_mem' := ⟨0, map_zero red⟩
      algebraMap_mem' := by
        intro c
        obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
        exact ⟨_, hconst a⟩
      inv_mem' := by
        rintro _ ⟨f, rfl⟩
        by_cases hz : red f = 0
        · rw [hz, inv_zero]; exact ⟨0, map_zero red⟩
        · have hf : f ∉ IsLocalRing.maximalIdeal ↥W₀ := by
            rw [← hker]; exact hz
          have hu : IsUnit f := by
            by_contra h
            exact hf ((IsLocalRing.mem_maximalIdeal f).mpr h)
          obtain ⟨u, rfl⟩ := hu
          exact ⟨↑u⁻¹, map_units_inv red u⟩ }
  refine ⟨red, R₀, hred, hker, hconst, fun z => Iff.rfl, fun z => ⟨?_, ?_⟩⟩
  · rintro ⟨f, rfl⟩
    obtain ⟨x, y, hy, hxy⟩ := (hW₀ (f : ↥K)).mp f.2
    exact ⟨f, x, y, hy, hxy, (hred f x y hy hxy).symm⟩
  · rintro ⟨f, x, y, hy, hxy, rfl⟩
    have hf : f ∈ W₀ := (hW₀ f).mpr ⟨x, y, hy, hxy⟩
    exact ⟨⟨f, hf⟩, hred ⟨f, hf⟩ x y hy hxy⟩

theorem coeffEmb_intSeriesC (L : Type*) [Field L] [CharZero L] (q : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ q) = HahnSeries.ofPowerSeries ℤ L (q.map (Int.castRingHom L)) := by
  ext n
  rw [coeffEmb_coeff, intSeriesC, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs
  · simp
  · simp

theorem map_intCast_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (q : PowerSeries ℤ) :
    (q.map (Int.castRingHom A)).map φ = q.map (Int.castRingHom B) := by
  have h : φ.comp (Int.castRingHom A) = Int.castRingHom B := RingHom.ext_int _ _
  rw [← h, PowerSeries.map_comp, RingHom.comp_apply]

theorem one_mem_strictPeriods_Gamma1 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, ?_, ?_⟩
  · exact (by rw [Gamma1_mem]; simp [ModularGroup.coe_T] : ModularGroup.T ∈ Gamma1 N)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]

theorem exists_ratio_presentation
    (p : ℕ) (M : ℕ) [NeZero (M * p)]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = laurentBaseChange L (x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    {k : ℤ} (f g : ModularForm ((Gamma1 (M * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC (IsLocalRing.ResidueField A) pg ≠ 0) :
    ∃ F : ↥K,
      (pg.map (Int.castRingHom A)).map (IsLocalRing.residue A) ≠ 0 ∧
      (F : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L ((pg.map (Int.castRingHom A)).map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L ((pf.map (Int.castRingHom A)).map (algebraMap A L)) ∧
      HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) ((pf.map (Int.castRingHom A)).map (IsLocalRing.residue A)) /
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) ((pg.map (Int.castRingHom A)).map (IsLocalRing.residue A))
        = intSeriesC (IsLocalRing.ResidueField A) pf / intSeriesC (IsLocalRing.ResidueField A) pg := by
  have hpg0 : pg ≠ 0 := by
    rintro rfl; exact hg0 (by rw [intSeriesC_zero])
  have hgQ : intSeriesC ℚ pg ≠ 0 := by
    intro h
    apply hpg0
    apply PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective
    rw [map_zero]
    exact HahnSeries.ofPowerSeries_injective (h.trans (map_zero (HahnSeries.ofPowerSeries ℤ ℚ)).symm)
  have hmem : intSeriesC ℚ pf / intSeriesC ℚ pg ∈ x1FunctionField (M * p) :=
    div_mem_qExpFunctionFieldC f g hf hg hgQ
  have hFK : coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ K := by
    rw [hK]; exact coeffEmb_mem_laurentBaseChange L hmem
  refine ⟨⟨_, hFK⟩, ?_, ?_, ?_⟩
  · rw [map_intCast_map]; exact fun h => hg0 (by rw [intSeriesC, h, map_zero])
  · rw [map_intCast_map, map_intCast_map]
    show coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) * _ = _
    rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
    have hne : HahnSeries.ofPowerSeries ℤ L (pg.map (Int.castRingHom L)) ≠ 0 := by
      intro h
      apply hpg0
      apply PowerSeries.map_injective (Int.castRingHom L) Int.cast_injective
      rw [map_zero]
      exact HahnSeries.ofPowerSeries_injective (h.trans (map_zero (HahnSeries.ofPowerSeries ℤ L)).symm)
    rw [div_mul_cancel₀ _ hne]
  · rw [map_intCast_map, map_intCast_map]; rfl

end S1cAux

end

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 32000000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CongruenceSubgroup ModularCurve IsDedekindDomain
open scoped MatrixGroups ModularForm

theorem CountAux_finrank_adjoin_simple_eq_relfinrank {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (K : IntermediateField F Ω) (x : ↥K) :
    Module.finrank ↥(IntermediateField.adjoin F ({x} : Set ↥K)) ↥K =
      IntermediateField.relfinrank (IntermediateField.adjoin F ({(x : Ω)} : Set Ω)) K := by
  have h : IntermediateField.adjoin F ({x} : Set ↥K) =
      (IntermediateField.adjoin F ({(x : Ω)} : Set Ω)).comap K.val := by
    ext y
    show y ∈ IntermediateField.adjoin F ({x} : Set ↥K) ↔
      K.val y ∈ IntermediateField.adjoin F ({(x : Ω)} : Set Ω)
    rw [← IntermediateField.lift_adjoin_simple (K := K) (α := x)]
    exact (IntermediateField.mem_lift y).symm
  rw [h, IntermediateField.finrank_comap, IntermediateField.fieldRange_val]

theorem BaseUniqAux_T_mem (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T]

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
    (w : ModularCurve.IntegralWeightOneForm (IsLocalRing.ResidueField A) M)
    [NeZero p]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (σ : ↥K ≃ₐ[L] ↥K)
    (hσj : ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq))
    (hσW : W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ≠ W₀)
    (hσj' : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom ∧
      (Polynomial.aeval j P)⁻¹ ∈ W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) :

    (∀ V : ValuationSubring ↥K,
      (∀ a : A, algebraMap A ↥K a ∈ V) → (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits) →
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) ∧

    (∀ V : ValuationSubring ↥K,
      (∀ a : A, algebraMap A ↥K a ∈ V) → (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits) →
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
      ∀ f : ↥K, f ∈ V.nonunits → ∃ g : ↥K, g ∈ V ∧ f = algebraMap A ↥K ϖ * g) ∧

    (∀ R₀ : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)),
      (∀ z : LaurentSeries (IsLocalRing.ResidueField A), z ∈ R₀ ↔
        ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z) →
      IntermediateField.relfinrank (ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) R₀ = p - 1) ∧

    IntermediateField.relfinrank (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)) K
      = p ^ 2 - 1 := by
  classical
  haveI hp : Fact p.Prime := inferInstance
  haveI : NeZero (M * p) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne p)⟩

  obtain ⟨W₀', hW₀', hW₀A, hW₀m, hW₀j, hW₀nu⟩ :=
    ModularCurve.XOneP.exists_gaussValuationSubring_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj
  have hWW : W₀ = W₀' := by ext f; rw [hW₀ f, hW₀' f]
  subst hWW
  clear hW₀'

  set Ej : IntermediateField L ↥K := IntermediateField.adjoin L ({j} : Set ↥K) with hEj
  haveI hFD : FiniteDimensional ↥Ej ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 (M * p)) (BaseUniqAux_T_mem (M * p)) L K (by rw [hK]; rfl) j hj
  haveI : Algebra.IsSeparable ↥Ej ↥K := by
    haveI : Algebra.IsAlgebraic ↥Ej ↥K := Algebra.IsAlgebraic.of_finite _ _
    haveI : CharZero ↥Ej := charZero_of_injective_algebraMap (algebraMap L _).injective
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField

  obtain ⟨OE, hDVR, hOEW₀, hOEpoly, hOEnu, hOEϖ⟩ :=
    ModularCurve.exists_valuationSubring_adjoin_isDiscreteValuationRing_mem_iff_of_laurentBaseChange_x1FunctionField
      (M * p) L K hK A j hj W₀ hW₀
  haveI := hDVR
  letI instOK : Algebra ↥OE ↥K := ((algebraMap ↥Ej ↥K).comp (algebraMap ↥OE ↥Ej)).toAlgebra
  haveI : IsScalarTower ↥OE ↥Ej ↥K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hOK : ∀ x : ↥OE, algebraMap ↥OE ↥K x = ((x : ↥Ej) : ↥K) := fun _ => rfl
  have hOKinj : Function.Injective (algebraMap ↥OE ↥K) := by
    intro a b h
    rw [hOK, hOK] at h
    exact Subtype.ext (Subtype.ext h)
  haveI : FaithfulSMul ↥OE ↥K := (faithfulSMul_iff_algebraMap_injective _ _).mpr hOKinj
  haveI : IsDedekindDomain ↥(integralClosure ↥OE ↥K) := integralClosure.isDedekindDomain ↥OE ↥Ej ↥K
  haveI : Module.Finite ↥OE ↥(integralClosure ↥OE ↥K) := IsIntegralClosure.finite ↥OE ↥Ej ↥K _
  haveI : IsFractionRing ↥(integralClosure ↥OE ↥K) ↥K :=
    IsIntegralClosure.isFractionRing_of_finite_extension ↥OE ↥Ej ↥K _

  have hAKinj : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L)
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hϖ𝔪 : ϖ ∈ IsLocalRing.maximalIdeal A := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ
  have hdomV : ∀ V : ValuationSubring ↥K, (∀ a : A, algebraMap A ↥K a ∈ V) →
      (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits) →
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
      V ≠ ⊤ ∧ (∀ x : ↥OE, algebraMap ↥OE ↥K x ∈ V) ∧
        (∀ x ∈ IsLocalRing.maximalIdeal ↥OE, algebraMap ↥OE ↥K x ∈ V.nonunits) := by
    intro V hVA hVm hVj
    have hϖV : algebraMap A ↥K ϖ ∈ V.nonunits := hVm ϖ hϖ𝔪
    have hϖ0 : algebraMap A ↥K ϖ ≠ 0 := (map_ne_zero_iff _ hAKinj).mpr hϖirr.ne_zero

    let SV : Subalgebra A ↥K := { V.toSubring with algebraMap_mem' := hVA }
    have hjV : j ∈ SV := by
      have h := (hVj Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)).1
      rwa [Polynomial.aeval_X] at h
    have hAjV : ∀ P : Polynomial A, Polynomial.aeval j P ∈ V := by
      intro P
      have h1 : Algebra.adjoin A {j} ≤ SV := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hjV)
      exact h1 (Polynomial.aeval_mem_adjoin_singleton A j)
    have hQ0 : ∀ Q : Polynomial A, Q.map (IsLocalRing.residue A) ≠ 0 → Polynomial.aeval j Q ≠ 0 := by
      intro Q hQ h0
      apply hQ
      rw [(transcendental_iff.mp htj) Q h0, Polynomial.map_zero]
    refine ⟨?_, ?_, ?_⟩
    · intro hT
      rcases (ValuationSubring.mem_nonunits_iff_or V).mp hϖV with h0 | hninv
      · exact hϖ0 h0
      · exact hninv (by rw [hT]; exact Subring.mem_top _)
    · intro x
      obtain ⟨P, Q, hQ, hxQ⟩ := (hOEpoly (x : ↥Ej)).mp x.2
      have hx : algebraMap ↥OE ↥K x = Polynomial.aeval j P * (Polynomial.aeval j Q)⁻¹ := by
        rw [hOK, eq_mul_inv_iff_mul_eq₀ (hQ0 Q hQ), hxQ]
      rw [hx]
      exact mul_mem (hAjV P) (hVj Q hQ).2
    · intro x hx
      obtain ⟨P, Q, hQ, hxQ⟩ := (hOEpoly (x : ↥Ej)).mp x.2
      have hxnu : (x : ↥Ej) ∈ OE.nonunits := (ValuationSubring.coe_mem_nonunits_iff).mpr hx
      have hP0 : P.map (IsLocalRing.residue A) = 0 := (hOEnu (x : ↥Ej) P Q hQ hxQ).mp hxnu
      have hdvd : Polynomial.C ϖ ∣ P := by
        rw [Polynomial.C_dvd_iff_dvd_coeff]
        intro n
        have hc : IsLocalRing.residue A (P.coeff n) = 0 := by
          have := congrArg (fun R => Polynomial.coeff R n) hP0
          simpa [Polynomial.coeff_map] using this
        rw [IsLocalRing.residue_eq_zero_iff, hϖ] at hc
        exact Ideal.mem_span_singleton.mp hc
      obtain ⟨P', rfl⟩ := hdvd
      have hx' : algebraMap ↥OE ↥K x =
          algebraMap A ↥K ϖ * (Polynomial.aeval j P' * (Polynomial.aeval j Q)⁻¹) := by
        rw [hOK, ← mul_assoc, eq_mul_inv_iff_mul_eq₀ (hQ0 Q hQ), hxQ, map_mul, Polynomial.aeval_C]
      rw [hx', ValuationSubring.mem_nonunits_iff, map_mul]
      have h1 : V.valuation (algebraMap A ↥K ϖ) < 1 := (ValuationSubring.mem_nonunits_iff V).mp hϖV
      have h2 : V.valuation (Polynomial.aeval j P' * (Polynomial.aeval j Q)⁻¹) ≤ 1 :=
        (V.valuation_le_one_iff _).mpr (mul_mem (hAjV P') (hVj Q hQ).2)
      calc V.valuation (algebraMap A ↥K ϖ) * V.valuation (Polynomial.aeval j P' * (Polynomial.aeval j Q)⁻¹)
          ≤ V.valuation (algebraMap A ↥K ϖ) * 1 := mul_le_mul_right h2 _
        _ = V.valuation (algebraMap A ↥K ϖ) := mul_one _
        _ < 1 := h1

  obtain ⟨red₀, R₀, hred₀, hker₀, hconst₀, hR₀rng, hR₀⟩ :=
    S1cAux.exists_red_and_reductionField L K A W₀ hW₀ hW₀A hW₀nu

  obtain ⟨hW₀top, hOW₀, hmW₀⟩ := hdomV W₀ hW₀A hW₀m hW₀j

  have hAjW₀ : ∀ (u : ↥K), u ∈ W₀ → ∀ P : Polynomial A, Polynomial.aeval u P ∈ W₀ := by
    intro u hu P
    let SW : Subalgebra A ↥K := { W₀.toSubring with algebraMap_mem' := hW₀A }
    have h1 : Algebra.adjoin A {u} ≤ SW := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hu)
    exact h1 (Polynomial.aeval_mem_adjoin_singleton A u)
  let φA : A →+* ↥W₀ := (algebraMap A ↥K).codRestrict W₀.toSubring hW₀A
  have hevalW : ∀ (u : ↥W₀) (P : Polynomial A),
      ((Polynomial.eval₂ φA u P : ↥W₀) : ↥K) = Polynomial.aeval (u : ↥K) P := by
    intro u P
    rw [show ((Polynomial.eval₂ φA u P : ↥W₀) : ↥K) = W₀.subtype (Polynomial.eval₂ φA u P) from rfl,
      Polynomial.hom_eval₂, Polynomial.aeval_def]
    congr 1
  have hredeval : ∀ (u : ↥W₀) (P : Polynomial A),
      red₀ (Polynomial.eval₂ φA u P) = Polynomial.aeval (red₀ u) (P.map (IsLocalRing.residue A)) := by
    intro u P
    rw [Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
    congr 1
    exact RingHom.ext (fun a => hconst₀ a)
  have hredaeval : ∀ (u : ↥K) (hu : u ∈ W₀) (P : Polynomial A),
      red₀ ⟨Polynomial.aeval u P, hAjW₀ u hu P⟩ =
        Polynomial.aeval (red₀ ⟨u, hu⟩) (P.map (IsLocalRing.residue A)) := by
    intro u hu P
    rw [← hredeval ⟨u, hu⟩ P]
    congr 1
    apply Subtype.ext
    rw [hevalW]

  have hredquot : ∀ (u : ↥K) (hu : u ∈ W₀) (t : LaurentSeries (IsLocalRing.ResidueField A)), red₀ ⟨u, hu⟩ = t →
      Transcendental (IsLocalRing.ResidueField A) t → ∀ (e : ↥K) (he : e ∈ W₀) (P Q : Polynomial A),
      Q.map (IsLocalRing.residue A) ≠ 0 → e * Polynomial.aeval u Q = Polynomial.aeval u P →
      red₀ ⟨e, he⟩ = Polynomial.aeval t (P.map (IsLocalRing.residue A)) /
        Polynomial.aeval t (Q.map (IsLocalRing.residue A)) := by
    intro u hu t ht htr e he P Q hQ hePQ
    have hQt : Polynomial.aeval t (Q.map (IsLocalRing.residue A)) ≠ 0 := fun h0 =>
      hQ ((transcendental_iff.mp htr) _ h0)
    rw [eq_div_iff hQt, ← ht, ← hredaeval u hu Q, ← hredaeval u hu P, ← map_mul]
    congr 1
    exact Subtype.ext hePQ
  have hmem_adjoin_quot : ∀ (t : LaurentSeries (IsLocalRing.ResidueField A)) (P Q : Polynomial A),
      Polynomial.aeval t (P.map (IsLocalRing.residue A)) / Polynomial.aeval t (Q.map (IsLocalRing.residue A)) ∈
        IntermediateField.adjoin (IsLocalRing.ResidueField A) ({t} : Set (LaurentSeries (IsLocalRing.ResidueField A))) := by
    intro t P Q
    have hmem : ∀ R : Polynomial (IsLocalRing.ResidueField A), Polynomial.aeval t R ∈
        IntermediateField.adjoin (IsLocalRing.ResidueField A) ({t} : Set (LaurentSeries (IsLocalRing.ResidueField A))) := fun R =>
      (IntermediateField.algebra_adjoin_le_adjoin (IsLocalRing.ResidueField A) _) (Polynomial.aeval_mem_adjoin_singleton (IsLocalRing.ResidueField A) t)
    exact div_mem (hmem _) (hmem _)

  have hOEofPQ : ∀ P Q : Polynomial A, Q.map (IsLocalRing.residue A) ≠ 0 →
      ∃ x : ↥OE, ((x : ↥Ej) : ↥K) * Polynomial.aeval j Q = Polynomial.aeval j P := by
    intro P Q hQ
    have hQj : Polynomial.aeval j Q ≠ 0 := fun h0 => hQ (by rw [(transcendental_iff.mp htj) Q h0, Polynomial.map_zero])
    have hmemE : ∀ R : Polynomial A, Polynomial.aeval j R ∈ Ej := by
      intro R
      rw [hEj]
      have : Polynomial.aeval j R = Polynomial.aeval j (R.map (algebraMap A L)) := by
        rw [Polynomial.aeval_map_algebraMap]
      rw [this]
      exact (IntermediateField.algebra_adjoin_le_adjoin L _) (Polynomial.aeval_mem_adjoin_singleton L j)
    let e : ↥Ej := ⟨Polynomial.aeval j P * (Polynomial.aeval j Q)⁻¹, mul_mem (hmemE P) (inv_mem (hmemE Q))⟩
    have he : (e : ↥K) * Polynomial.aeval j Q = Polynomial.aeval j P := inv_mul_cancel_right₀ hQj _
    exact ⟨⟨e, (hOEpoly e).mpr ⟨P, Q, hQ, he⟩⟩, he⟩

  have hliftP : ∀ r : Polynomial (IsLocalRing.ResidueField A), ∃ R : Polynomial A, R.map (IsLocalRing.residue A) = r :=
    fun r => Polynomial.map_surjective _ IsLocalRing.residue_surjective r

  set jb : LaurentSeries (IsLocalRing.ResidueField A) := ModularCurve.jqModC (IsLocalRing.ResidueField A) with hjb
  set Kj : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) :=
    IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jb} : Set (LaurentSeries (IsLocalRing.ResidueField A))) with hKjdef

  have hjW₀ : j ∈ W₀ := by
    have h := (hW₀j Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)).1
    rwa [Polynomial.aeval_X] at h
  obtain ⟨⟨xj, yj, hyj, hxyj, hredj⟩, ⟨xjp, yjp, hyjp, hxyjp, hredjp⟩⟩ :=
    ModularCurve.exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand p L A hAp
  have hred₀j : red₀ ⟨j, hjW₀⟩ = jb := by
    rw [hjb, ← hredj]
    exact hred₀ ⟨j, hjW₀⟩ xj yj hyj (by rw [show (((⟨j, hjW₀⟩ : ↥W₀) : ↥K) : LaurentSeries L) = (j : LaurentSeries L) from rfl, hj]; exact hxyj)
  have hjbtr : Transcendental (IsLocalRing.ResidueField A) jb := by rw [hjb]; exact ModularCurve.transcendental_jqModC (IsLocalRing.ResidueField A)
  have hKj : ∀ z, z ∈ Kj ↔ ∃ x : ↥OE, red₀ ⟨algebraMap ↥OE ↥K x, hOW₀ x⟩ = z := by
    intro z
    constructor
    · intro hz
      rw [hKjdef] at hz
      obtain ⟨r, s₀, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff (IsLocalRing.ResidueField A) z).mp hz
      obtain ⟨R, hR⟩ := hliftP r
      obtain ⟨S, hS⟩ := hliftP s₀
      by_cases hs : s₀ = 0
      · refine ⟨0, ?_⟩
        rw [hs, Polynomial.aeval_zero, div_zero]
        have : (⟨algebraMap ↥OE ↥K 0, hOW₀ 0⟩ : ↥W₀) = 0 := Subtype.ext (map_zero _)
        rw [this, map_zero]
      · have hS0 : S.map (IsLocalRing.residue A) ≠ 0 := by rw [hS]; exact hs
        obtain ⟨x, hx⟩ := hOEofPQ R S hS0
        refine ⟨x, ?_⟩
        rw [← hR, ← hS]
        exact hredquot j hjW₀ jb hred₀j hjbtr _ (hOW₀ x) R S hS0 hx
    · rintro ⟨x, rfl⟩
      obtain ⟨P, Q, hQ, hxQ⟩ := (hOEpoly (x : ↥Ej)).mp x.2
      rw [hredquot j hjW₀ jb hred₀j hjbtr _ (hOW₀ x) P Q hQ hxQ, hKjdef]
      exact hmem_adjoin_quot jb P Q
  obtain ⟨𝔓₀, h𝔓₀p, h𝔓₀0, hmem𝔓₀, hover₀, hW₀eq, hle₀, hf₀⟩ :=
    ValuationSubring.exists_ideal_integralClosure_eq_valuationSubringAtPrime_and_inertiaDeg_eq_finrank
      (O := ↥OE) (F := ↥K) W₀ hOW₀ hmW₀ red₀ hker₀ Kj R₀ hKj hR₀rng

  set W₁ : ValuationSubring ↥K := W₀.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom with hW₁def
  have hmemW₁ : ∀ f : ↥K, f ∈ W₁ ↔ σ f ∈ W₀ := fun f => ValuationSubring.mem_comap
  let σW : ↥W₁ →+* ↥W₀ :=
    ((σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom.comp W₁.subtype).codRestrict W₀.toSubring
      (fun w => (hmemW₁ w.1).mp w.2)
  have hσWcoe : ∀ w : ↥W₁, ((σW w : ↥W₀) : ↥K) = σ (w : ↥K) := fun _ => rfl
  have hσWsurj : Function.Surjective σW := by
    intro w
    refine ⟨⟨σ.symm (w : ↥K), (hmemW₁ _).mpr (by rw [AlgEquiv.apply_symm_apply]; exact w.2)⟩, ?_⟩
    apply Subtype.ext
    rw [hσWcoe]
    exact AlgEquiv.apply_symm_apply σ _
  let red₁ : ↥W₁ →+* LaurentSeries (IsLocalRing.ResidueField A) := red₀.comp σW
  have hnuW₁ : ∀ f : ↥K, f ∈ W₁.nonunits ↔ σ f ∈ W₀.nonunits := by
    intro f
    rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
      map_eq_zero_iff σ σ.injective, ← map_inv₀, hmemW₁]
  have hker₁ : RingHom.ker red₁ = IsLocalRing.maximalIdeal ↥W₁ := by
    ext w
    rw [RingHom.mem_ker, ← ValuationSubring.coe_mem_nonunits_iff, hnuW₁, ← hσWcoe,
      ValuationSubring.coe_mem_nonunits_iff, ← hker₀, RingHom.mem_ker]
    rfl
  have hσA : ∀ a : A, σ (algebraMap A ↥K a) = algebraMap A ↥K a := by
    intro a
    rw [IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes]
  have hW₁A : ∀ a : A, algebraMap A ↥K a ∈ W₁ := fun a => (hmemW₁ _).mpr (by rw [hσA]; exact hW₀A a)
  have hW₁m : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ W₁.nonunits :=
    fun a ha => (hnuW₁ _).mpr (by rw [hσA]; exact hW₀m a ha)
  obtain ⟨hW₁top, hOW₁, hmW₁⟩ := hdomV W₁ hW₁A hW₁m hσj'
  set Kjp : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) :=
    IntermediateField.adjoin (IsLocalRing.ResidueField A) ({jb ^ p} : Set (LaurentSeries (IsLocalRing.ResidueField A))) with hKjpdef

  have hσjW₀ : σ j ∈ W₀ := by
    have h := (hσj' Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)).1
    rw [Polynomial.aeval_X] at h
    exact (hmemW₁ j).mp h
  have hred₀σj : red₀ ⟨σ j, hσjW₀⟩ = jb ^ p := by
    rw [hjb, ← hredjp]
    exact hred₀ ⟨σ j, hσjW₀⟩ xjp yjp hyjp
      (by rw [show (((⟨σ j, hσjW₀⟩ : ↥W₀) : ↥K) : LaurentSeries L) = ((σ j : ↥K) : LaurentSeries L) from rfl, hσj]; exact hxyjp)
  have hjbptr : Transcendental (IsLocalRing.ResidueField A) (jb ^ p) := hjbtr.pow hp.out.pos
  have hσaeval : ∀ P : Polynomial A, σ (Polynomial.aeval j P) = Polynomial.aeval (σ j) P := by
    intro P
    exact (Polynomial.aeval_algHom_apply (σ.toAlgHom.restrictScalars A) j P).symm
  have hred₁x : ∀ x : ↥OE, red₁ ⟨algebraMap ↥OE ↥K x, hOW₁ x⟩ =
      red₀ ⟨σ (algebraMap ↥OE ↥K x), (hmemW₁ _).mp (hOW₁ x)⟩ := fun _ => rfl
  have hKjp : ∀ z, z ∈ Kjp ↔ ∃ x : ↥OE, red₁ ⟨algebraMap ↥OE ↥K x, hOW₁ x⟩ = z := by
    intro z
    constructor
    · intro hz
      rw [hKjpdef] at hz
      obtain ⟨r, s₀, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff (IsLocalRing.ResidueField A) z).mp hz
      obtain ⟨R, hR⟩ := hliftP r
      obtain ⟨S, hS⟩ := hliftP s₀
      by_cases hs : s₀ = 0
      · refine ⟨0, ?_⟩
        rw [hs, Polynomial.aeval_zero, div_zero]
        have : (⟨algebraMap ↥OE ↥K 0, hOW₁ 0⟩ : ↥W₁) = 0 := Subtype.ext (map_zero _)
        rw [this, map_zero]
      · have hS0 : S.map (IsLocalRing.residue A) ≠ 0 := by rw [hS]; exact hs
        obtain ⟨x, hx⟩ := hOEofPQ R S hS0
        refine ⟨x, ?_⟩
        rw [← hR, ← hS, hred₁x]
        refine hredquot (σ j) hσjW₀ (jb ^ p) hred₀σj hjbptr _ _ R S hS0 ?_
        rw [hOK, ← hσaeval, ← hσaeval, ← map_mul, hx]
    · rintro ⟨x, rfl⟩
      obtain ⟨P, Q, hQ, hxQ⟩ := (hOEpoly (x : ↥Ej)).mp x.2
      rw [hred₁x, hredquot (σ j) hσjW₀ (jb ^ p) hred₀σj hjbptr _ _ P Q hQ
        (by rw [hOK, ← hσaeval, ← hσaeval, ← map_mul, hxQ]), hKjpdef]
      exact hmem_adjoin_quot (jb ^ p) P Q
  have hR₀rng₁ : ∀ z, z ∈ R₀ ↔ ∃ w : ↥W₁, red₁ w = z := by
    intro z
    rw [hR₀rng z]
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨w', rfl⟩ := hσWsurj w
      exact ⟨w', rfl⟩
    · rintro ⟨w, rfl⟩
      exact ⟨σW w, rfl⟩
  obtain ⟨𝔓₁, h𝔓₁p, h𝔓₁0, hmem𝔓₁, hover₁, hW₁eq, hle₁, hf₁⟩ :=
    ValuationSubring.exists_ideal_integralClosure_eq_valuationSubringAtPrime_and_inertiaDeg_eq_finrank
      (O := ↥OE) (F := ↥K) W₁ hOW₁ hmW₁ red₁ hker₁ Kjp R₀ hKjp hR₀rng₁

  have hW01 : W₀ ≠ W₁ := fun h => hσW h.symm
  have h𝔓ne : 𝔓₀ ≠ 𝔓₁ := by
    intro h
    apply hW01
    rw [hW₀eq, hW₁eq]
    congr 1
    exact HeightOneSpectrum.ext h

  have hpκ : (p : (IsLocalRing.ResidueField A)) = 0 := by
    rw [← map_natCast (algebraMap A (IsLocalRing.ResidueField A)) p]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hAp
  haveI : CharP (IsLocalRing.ResidueField A) p := (CharP.charP_iff_prime_eq_zero hp.out).mpr hpκ

  obtain ⟨K₀, hK₀def⟩ : ∃ K₀ : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)), K₀ = x1FunctionFieldC (IsLocalRing.ResidueField A) M := ⟨_, rfl⟩
  obtain ⟨Ig, hIgdef⟩ : ∃ Ig : IntermediateField (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)), Ig = igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w := ⟨_, rfl⟩
  have hKjK₀ : Kj ≤ K₀ := by
    rw [hKjdef, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, hjb, hK₀def, x1FunctionFieldC,
      qExpFunctionFieldC]
    exact IntermediateField.subset_adjoin _ _ (ModularCurve.jqModC_mem_intFormRatiosC (IsLocalRing.ResidueField A) _)
  have hZκ : (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)).comp (Int.castRingHom (ZMod p)) =
      Int.castRingHom (IsLocalRing.ResidueField A) := RingHom.ext_int _ _
  have hmapκ : ∀ q : PowerSeries ℤ, q.map (Int.castRingHom (IsLocalRing.ResidueField A)) =
      (q.map (Int.castRingHom (ZMod p))).map (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)) := by
    intro q; rw [← hZκ, PowerSeries.map_comp, RingHom.comp_apply]

  have hleM : ((Gamma1 (M * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (Gamma1_le_of_dvd (dvd_mul_right M p))
  have hlep : ((Gamma1 (M * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma1 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono (Gamma1_le_of_dvd (dvd_mul_left p M))
  have hK₀R₀' : x1FunctionFieldC (IsLocalRing.ResidueField A) M ≤ R₀ := by
    rw [x1FunctionFieldC, qExpFunctionFieldC, IntermediateField.adjoin_le_iff]
    rintro _ ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
    obtain ⟨F, hy, hpres, hred⟩ :=
      S1cAux.exists_ratio_presentation p M L K hK A (restrictForm hleM f) (restrictForm hleM g)
        pf pg hf hg hg0
    exact (hR₀ _).mpr ⟨F, _, _, hy, hpres, hred⟩

  have hinputs :
      (∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = w.hasseRootFn) ∧
      IntermediateField.relfinrank (x1FunctionFieldC (IsLocalRing.ResidueField A) M) (igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w) = p - 1 := by
    by_cases hp5 : 5 ≤ p
    · refine ⟨?_, (ModularCurve.isKummerGenerator_hasseRootFn_and_relfinrank_igusaFunctionFieldX1C
          p hp5 (IsLocalRing.ResidueField A) M hM hpM w).2⟩
      obtain ⟨k, G, H, pG, pH, hG, hH, hH0, hGH⟩ :=
        ModularForm.exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq p hp5
      have hκH : intSeriesC (IsLocalRing.ResidueField A) pH ≠ 0 := by
        intro h0
        apply hH0
        apply PowerSeries.map_injective (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A))
          (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)).injective
        rw [map_zero, ← hmapκ]
        exact HahnSeries.ofPowerSeries_injective
          (h0.trans (map_zero (HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A))).symm)
      have hGH' : intSeriesC (IsLocalRing.ResidueField A) pG = intSeriesC (IsLocalRing.ResidueField A) pH := by
        rw [intSeriesC, intSeriesC, hmapκ, hmapκ pH, hGH]

      have hden : IsIntegralQExp
          (⇑((restrictForm hlep H).mul (restrictForm hleM w.form))) (pH * w.series) := by
        rw [IsIntegralQExp, map_mul, ModularForm.coe_mul]
        have h1 : (pH.map (Int.castRingHom ℂ)) = UpperHalfPlane.qExpansion 1 (⇑(restrictForm hlep H)) := hH
        have h2 : (w.series.map (Int.castRingHom ℂ)) =
            UpperHalfPlane.qExpansion 1 (⇑(restrictForm hleM w.form)) := w.isIntegralQExp
        rw [h1, h2]
        exact (ModularForm.qExpansion_mul_coe one_pos (S1cAux.one_mem_strictPeriods_Gamma1 (M * p)) _ _).symm
      have hden0 : intSeriesC (IsLocalRing.ResidueField A) (pH * w.series) ≠ 0 := by
        rw [intSeriesC_mul]; exact mul_ne_zero hκH w.intSeriesC_ne_zero
      obtain ⟨F, hy, hpres, hred⟩ :=
        S1cAux.exists_ratio_presentation p M L K hK A (restrictForm hlep G)
          ((restrictForm hlep H).mul (restrictForm hleM w.form)) pG (pH * w.series) hG hden hden0
      refine ⟨F, _, _, hy, hpres, ?_⟩
      rw [hred, intSeriesC_mul, hGH', IntegralWeightOneForm.hasseRootFn, div_mul_cancel_left₀ hκH]
    · exact ModularCurve.XOneP.exists_gaussReduction_eq_hasseRootFn_and_relfinrank_igusaFunctionFieldX1C_of_lt_five
        p M hM hpM L ζ hζ K hK A hAp hζA j hj w (not_le.mp hp5)
  obtain ⟨⟨F₁, x₁, y₁, hy₁, hp₁, hr₁⟩, hdegI⟩ := hinputs
  have haR₀ : w.hasseRootFn ∈ R₀ := (hR₀ _).mpr ⟨F₁, x₁, y₁, hy₁, hp₁, hr₁⟩

  have hIgR₀' : igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w ≤ R₀ := by
    rw [igusaFunctionFieldX1C, IgusaCover.igusaFunctionField, IntermediateField.adjoin_le_iff]
    rintro z (hz | hz)
    · exact hK₀R₀' hz
    · rw [Set.mem_singleton_iff] at hz
      rw [hz]; exact haR₀
  have hK₀R₀ : K₀ ≤ R₀ := by rw [hK₀def]; exact hK₀R₀'
  have hK₀Ig : K₀ ≤ Ig := by rw [hK₀def, hIgdef]; exact x1FunctionFieldC_le_igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w
  have hIgR₀ : Ig ≤ R₀ := by rw [hIgdef]; exact hIgR₀'
  have hdegIg : IntermediateField.relfinrank K₀ Ig = p - 1 := by rw [hK₀def, hIgdef]; exact hdegI
  have hKjpKj : Kjp ≤ Kj := by
    rw [hKjpdef, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact pow_mem (IntermediateField.subset_adjoin _ _ (Set.mem_singleton jb)) p
  have hdegFrob : IntermediateField.relfinrank Kjp Kj = p := by
    rw [hKjpdef, hKjdef, hjb]
    exact ModularCurve.relfinrank_adjoin_jqModC_pow_adjoin_jqModC_eq (IsLocalRing.ResidueField A) p
  obtain ⟨dM, hdMdef⟩ : ∃ dM : ℕ, dM = IntermediateField.relfinrank Kj K₀ := ⟨_, rfl⟩

  have hf₀' : (IsLocalRing.maximalIdeal ↥OE).inertiaDeg' 𝔓₀ = IntermediateField.relfinrank Kj R₀ := by
    rw [hf₀, IntermediateField.relfinrank_eq_finrank_of_le hle₀]
  have hf₁' : (IsLocalRing.maximalIdeal ↥OE).inertiaDeg' 𝔓₁ = IntermediateField.relfinrank Kjp R₀ := by
    rw [hf₁, IntermediateField.relfinrank_eq_finrank_of_le hle₁]
  have hf₀pos : 0 < (IsLocalRing.maximalIdeal ↥OE).inertiaDeg' 𝔓₀ := by
    haveI := hover₀
    exact Ideal.inertiaDeg'_pos (IsLocalRing.maximalIdeal ↥OE) 𝔓₀

  have htower₀ : IntermediateField.relfinrank Kj R₀ = dM * IntermediateField.relfinrank K₀ R₀ := by
    rw [hdMdef, IntermediateField.relfinrank_mul_relfinrank hKjK₀ hK₀R₀]
  have htowerIg : IntermediateField.relfinrank K₀ R₀ = (p - 1) * IntermediateField.relfinrank Ig R₀ := by
    rw [← hdegIg, IntermediateField.relfinrank_mul_relfinrank hK₀Ig hIgR₀]
  have htower₁ : IntermediateField.relfinrank Kjp R₀ = p * IntermediateField.relfinrank Kj R₀ := by
    rw [← hdegFrob, IntermediateField.relfinrank_mul_relfinrank hKjpKj (hKjK₀.trans hK₀R₀)]
  have hIgR₀pos : 0 < IntermediateField.relfinrank Ig R₀ := by
    have h := hf₀pos
    rw [hf₀', htower₀, htowerIg] at h
    exact Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero, mul_zero] at h; exact lt_irrefl 0 h)

  obtain ⟨KM, hKMdef⟩ : ∃ KM : IntermediateField L (LaurentSeries L), KM = laurentBaseChange L (x1FunctionField M) := ⟨_, rfl⟩
  have hKMK : KM ≤ K := by
    rw [hK, hKMdef]
    exact (IntermediateField.adjoin.mono L _ _
      (Set.image_mono (x1FunctionFieldC_le_of_dvd ℚ (dvd_mul_right M p))) :
      laurentBaseChange L (x1FunctionField M) ≤ laurentBaseChange L (x1FunctionField (M * p)))
  have hfinK : Module.finrank ↥Ej ↥K = IntermediateField.relfinrank KM K * dM := by

    have hjqmem : ModularCurve.jq ∈ x1FunctionField M := by
      rw [← ModularCurve.jqModC_rat, x1FunctionField, x1FunctionFieldC, qExpFunctionFieldC]
      exact IntermediateField.subset_adjoin _ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
    have hjKM : (j : LaurentSeries L) ∈ KM := by
      rw [hKMdef, hj]; exact coeffEmb_mem_laurentBaseChange L hjqmem
    letI instAKM : Algebra A ↥KM := ((algebraMap L ↥KM).comp (algebraMap A L)).toAlgebra
    haveI : IsScalarTower A L ↥KM := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let jM : ↥KM := ⟨(j : LaurentSeries L), hjKM⟩
    haveI : Fact (jM ≠ 0) := ⟨fun h => by
      have hval : (j : LaurentSeries L) = 0 := congrArg Subtype.val h
      exact (Fact.out : j ≠ 0) (Subtype.ext hval)⟩
    have hDEGM := ModularCurve.XOneP.finrank_adjoin_j_eq_relfinrank_adjoin_jqModC_x1FunctionFieldC_of_x1
      p M hM hpM L ζ hζ KM hKMdef A hAp hζA jM hj

    set E₀ : IntermediateField L (LaurentSeries L) :=
      IntermediateField.adjoin L ({(j : LaurentSeries L)} : Set (LaurentSeries L)) with hE₀
    have hE₀KM : E₀ ≤ KM := by
      rw [hE₀, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]; exact hjKM
    have h1 : Module.finrank ↥Ej ↥K = IntermediateField.relfinrank E₀ K := by
      rw [hEj, hE₀]; exact CountAux_finrank_adjoin_simple_eq_relfinrank K j
    have h2 : Module.finrank ↥(IntermediateField.adjoin L ({jM} : Set ↥KM)) ↥KM =
        IntermediateField.relfinrank E₀ KM := by
      rw [hE₀]; exact CountAux_finrank_adjoin_simple_eq_relfinrank KM jM
    rw [h1, ← IntermediateField.relfinrank_mul_relfinrank hE₀KM hKMK, ← h2, hDEGM, hdMdef, hKjdef, hjb,
      hK₀def, mul_comm]
  have hDEGLE : IntermediateField.relfinrank KM K ≤ p ^ 2 - 1 := by
    rw [hKMdef]
    exact ModularCurve.XOneP.relfinrank_laurentBaseChange_x1FunctionField_le_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj

  let 𝔓 : Fin 2 → Ideal ↥(integralClosure ↥OE ↥K) := ![𝔓₀, 𝔓₁]
  have hprime : ∀ i, (𝔓 i).IsPrime := by
    intro i; fin_cases i
    · exact h𝔓₀p
    · exact h𝔓₁p
  have h0' : ∀ i, 𝔓 i ≠ ⊥ := by
    intro i; fin_cases i
    · exact h𝔓₀0
    · exact h𝔓₁0
  have hover' : ∀ i, (𝔓 i).LiesOver (IsLocalRing.maximalIdeal ↥OE) := by
    intro i; fin_cases i
    · exact hover₀
    · exact hover₁
  have hinj : Function.Injective 𝔓 := by
    intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd h h𝔓ne
    · exact absurd h.symm h𝔓ne
    · rfl
  let d : Fin 2 → ℕ := ![(p - 1) * dM, p * ((p - 1) * dM)]
  have hsumd : ∑ i, d i = (p ^ 2 - 1) * dM := by
    rw [Fin.sum_univ_two]
    show (p - 1) * dM + p * ((p - 1) * dM) = (p ^ 2 - 1) * dM
    have hp1 : 1 ≤ p := hp.out.one_lt.le
    zify [hp1, Nat.one_le_pow 2 p hp.out.pos]
    ring
  have hd : ∀ i, d i ≤ (IsLocalRing.maximalIdeal ↥OE).inertiaDeg' (𝔓 i) := by
    intro i; fin_cases i
    · show (p - 1) * dM ≤ (IsLocalRing.maximalIdeal ↥OE).inertiaDeg' 𝔓₀
      rw [hf₀', htower₀, htowerIg]
      calc (p - 1) * dM = dM * ((p - 1) * 1) := by ring
        _ ≤ dM * ((p - 1) * IntermediateField.relfinrank Ig R₀) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hIgR₀pos)
    · show p * ((p - 1) * dM) ≤ (IsLocalRing.maximalIdeal ↥OE).inertiaDeg' 𝔓₁
      rw [hf₁', htower₁, htower₀, htowerIg]
      calc p * ((p - 1) * dM) = p * (dM * ((p - 1) * 1)) := by ring
        _ ≤ p * (dM * ((p - 1) * IntermediateField.relfinrank Ig R₀)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hIgR₀pos))
  have hsum : Module.finrank ↥Ej ↥K ≤ ∑ i, d i := by
    rw [hsumd, hfinK]
    exact Nat.mul_le_mul_right _ hDEGLE
  obtain ⟨-, -, hfdeg, hsumeq, hV, hϖ'⟩ :=
    IsDiscreteValuationRing.primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg
      (O := ↥OE) (F := ↥K) ↥Ej 𝔓 (hprime := hprime) h0' (hover := hover') hinj d hd hsum

  have hdMpos : 0 < dM := by
    have h := hf₀pos
    rw [hf₀', htower₀] at h
    exact Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at h; exact lt_irrefl 0 h)

  have hcomplete : ∀ V : ValuationSubring ↥K, (∀ a : A, algebraMap A ↥K a ∈ V) →
      (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits) →
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
      V = W₀ ∨ V = W₁ := by
    intro V hVA hVm hVj
    obtain ⟨hVtop, hVO, hVmO⟩ := hdomV V hVA hVm hVj
    obtain ⟨i, hi⟩ := hV V hVtop hVO hVmO
    fin_cases i
    · left; rw [hW₀eq]; exact hi
    · right; rw [hW₁eq]; exact hi
  refine ⟨hcomplete, ?_, ?_, ?_⟩
  ·
    intro V hVA hVm hVj f hf
    obtain ⟨hVtop, hVO, hVmO⟩ := hdomV V hVA hVm hVj
    obtain ⟨i, hi⟩ := hV V hVtop hVO hVmO
    obtain ⟨ϖO, hϖOK, hϖOirr⟩ := hOEϖ ϖ hϖirr
    subst hi
    have hfV : f ∈ HeightOneSpectrum.valuationSubringAtPrime (↥K) ⟨𝔓 i, hprime i, h0' i⟩ :=
      (ValuationSubring.nonunits_le hf)
    obtain ⟨y, hy, hfy⟩ := hϖ' i ϖO hϖOirr f hfV hf
    refine ⟨y, hy, ?_⟩
    rw [hfy, hOK, hϖOK]
  ·
    intro R₀' hR₀'
    have hRR : R₀' = R₀ := by
      ext z; rw [hR₀' z, hR₀ z]
    rw [hRR, ← hK₀def]
    have h := hfdeg 0
    rw [show 𝔓 0 = 𝔓₀ from rfl, hf₀', htower₀] at h
    have h' : dM * IntermediateField.relfinrank K₀ R₀ = dM * (p - 1) := by
      rw [h]; show (p - 1) * dM = dM * (p - 1); ring
    exact Nat.eq_of_mul_eq_mul_left hdMpos h'
  ·
    rw [← hKMdef]
    have h := hsumeq
    rw [hsumd, hfinK] at h
    have h' : dM * IntermediateField.relfinrank KM K = dM * (p ^ 2 - 1) := by
      rw [mul_comm dM (IntermediateField.relfinrank KM K), ← h]; ring
    exact Nat.eq_of_mul_eq_mul_left hdMpos h'

end S_ModularCurve_XOneP_valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul (solution)
