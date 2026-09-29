-- Prove2me | solution 1 for ModularCurve.XOneP.apply_mem_gaussValuationSubring_iff_of_apply_eq_diamondAut_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/5b35fd9f-3edb-5916-8050-f7e2a845850a

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Theorems.Thm_ModularCurve_exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff
import Theorems.Thm_ModularCurve_exists_isDiamondAut
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_and_coe_eq_atkinLehnerInvolutionFull_x1_mul
import Theorems.Thm_ModularCurve_XOneP_valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
import Theorems.Thm_ModularCurve_pow_char_eq_map_frobenius_qExpand
import Theorems.Thm_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing
import Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_apply_mem_gaussValuationSubring_iff_of_apply_eq_diamondAut_x1_mul
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul"
p2m_attr_erase "instance" "CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "instance" "WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qExpandAlgHomC_apply ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq"
p2m_attr_erase "simp" "CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen"
p2m_attr_erase "simp" "ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

namespace DiamFixJ

p2m_open "ModularCurve~coeffEmb_jq~coeffEmb_qExpand CongruenceSubgroup"

theorem gamma1_mul_le (M p : ℕ) : Gamma1 (M * p) ≤ Gamma1 M ⊓ Gamma0 p := by
  intro A hA
  refine Subgroup.mem_inf.mpr ⟨Gamma1_le_of_dvd (dvd_mul_right M p) hA, ?_⟩
  rw [Gamma1_mem] at hA
  rw [Gamma0_mem]
  have h := hA.2.2
  have := congrArg (ZMod.castHom (dvd_mul_left p M) (ZMod p)) h
  rwa [map_intCast, map_zero] at this

theorem diamondAut_congr (N : ℕ) {d d' : ℕ} (h : (d : ZMod N) = (d' : ZMod N)) :
    diamondAut N d = diamondAut N d' := by
  have hP : IsDiamondAut N d = IsDiamondAut N d' := by
    funext σ
    have hc : Nat.Coprime d N ↔ Nat.Coprime d' N := by
      have hmod : d ≡ d' [MOD N] := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
      rw [Nat.Coprime, Nat.Coprime, Nat.ModEq.gcd_eq hmod]
    simp only [IsDiamondAut, h, hc]
  have key : ∀ (P Q : (x1FunctionField N ≃ₐ[ℚ] x1FunctionField N) → Prop), P = Q →
      (haveI := Classical.dec (∃ σ : x1FunctionField N ≃ₐ[ℚ] x1FunctionField N, P σ)
       if h : ∃ σ : x1FunctionField N ≃ₐ[ℚ] x1FunctionField N, P σ then h.choose else AlgEquiv.refl) =
      (haveI := Classical.dec (∃ σ : x1FunctionField N ≃ₐ[ℚ] x1FunctionField N, Q σ)
       if h : ∃ σ : x1FunctionField N ≃ₐ[ℚ] x1FunctionField N, Q σ then h.choose else AlgEquiv.refl) := by
    rintro P Q rfl; rfl
  exact key _ _ hP

theorem algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_gamma0
    (N : ℕ) [NeZero N]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    (d : ℕ) (hd : d.Coprime N)
    (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut N d) x' :
            ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))) : LaurentSeries L)) :
    ∀ u : ↥K, (u : LaurentSeries L) ∈
        ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 N)) →
      θ u = u := by
  classical

  obtain ⟨N', rfl⟩ : ∃ N', N = 1 * N' := ⟨N, (one_mul N).symm⟩
  haveI : NeZero N' := ⟨fun h => NeZero.ne (1 * N') (by rw [h, mul_zero])⟩
  set F₀ := x1FunctionField (1 * N') with hF₀
  set F₁ := x1x0FunctionFieldC ℚ 1 N' with hF₁
  have hF₁₀ : F₁ ≤ F₀ := qExpFunctionFieldC_mono ℚ (gamma1_mul_le 1 N')
  have hG : qExpFunctionFieldC ℚ (Gamma0 (1 * N')) ≤ F₁ := by
    rw [one_mul]
    exact qExpFunctionFieldC_mono ℚ inf_le_right

  obtain ⟨δ, hδ, hfix⟩ := exists_monoidHom_diamondAut_mem_x1x0FunctionFieldC_iff 1 N' (Nat.coprime_one_left N')
    (fun d' hd' => exists_isDiamondAut (1 * N') hd')
  have hdu : IsUnit (d : ZMod (1 * N')) := (ZMod.isUnit_iff_coprime d (1 * N')).mpr hd
  set u : (ZMod (1 * N'))ˣ := hdu.unit with hu
  have huker : u ∈ (ZMod.unitsMap (dvd_mul_right 1 N')).ker := by
    rw [MonoidHom.mem_ker]
    exact Subsingleton.elim _ _
  have hδu : δ ⟨u, huker⟩ = diamondAut (1 * N') d := by
    rw [hδ]
    apply diamondAut_congr
    show (((u : ZMod (1 * N')).val : ℕ) : ZMod (1 * N')) = (d : ZMod (1 * N'))
    rw [ZMod.natCast_zmod_val]
    exact hdu.unit_spec
  have hfix1 : ∀ y : ↥F₀, (y : LaurentSeries ℚ) ∈ F₁ → diamondAut (1 * N') d y = y := by
    intro y hy
    rw [← hδu]
    exact (hfix y).mp hy ⟨u, huker⟩

  let P : IntermediateField L (LaurentSeries L) :=
    (IntermediateField.fixedField (Subgroup.zpowers θ)).map K.val
  have hPmem : ∀ x : ↥K, (x : LaurentSeries L) ∈ P ↔ θ x = x := by
    intro x
    constructor
    · rintro ⟨x', hx', hxx'⟩
      have : x' = x := Subtype.ext hxx'
      subst this
      have hx'' : x' ∈ IntermediateField.fixedField (Subgroup.zpowers θ) := hx'
      rw [IntermediateField.mem_fixedField_iff] at hx''
      exact hx'' θ (Subgroup.mem_zpowers θ)
    · intro hx
      refine ⟨x, ?_, rfl⟩
      show x ∈ IntermediateField.fixedField (Subgroup.zpowers θ)
      rw [IntermediateField.mem_fixedField_iff]
      intro g hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have key : ∀ n : ℕ, (θ ^ n) x = x := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
      rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
      · exact_mod_cast key m
      · rw [zpow_neg, zpow_natCast]
        have h1 := key m
        conv_lhs => rw [← h1]
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

  have hgen : laurentBaseChange L F₁ ≤ P := by
    rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨z, hz, rfl⟩
    have hz0 : z ∈ F₀ := hF₁₀ hz
    have hxK : coeffEmb L z ∈ K := by rw [hK]; exact coeffEmb_mem_laurentBaseChange L hz0
    show coeffEmb L z ∈ P
    rw [show coeffEmb L z = ((⟨coeffEmb L z, hxK⟩ : ↥K) : LaurentSeries L) from rfl, hPmem]
    apply Subtype.ext
    rw [hθ ⟨coeffEmb L z, hxK⟩ ⟨coeffEmb L z, coeffEmb_mem_laurentBaseChange L hz0⟩ rfl]
    rcases Classical.em (∃ σ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀,
        IsBaseChangeAutOf L (diamondAut (1 * N') d) σ) with hex | hex
    · have hbc := isBaseChangeAutOf_baseChangeAut hex ⟨z, hz0⟩
      rw [hbc, hfix1 ⟨z, hz0⟩ hz]
    · rw [baseChangeAut_of_not hex]
      rfl

  have hmono : laurentBaseChange L (qExpFunctionFieldC ℚ (Gamma0 (1 * N'))) ≤ laurentBaseChange L F₁ := by
    rw [laurentBaseChange, laurentBaseChange]
    exact IntermediateField.adjoin.mono L _ _ (Set.image_mono hG)
  intro v hv
  exact (hPmem v).mp (hgen (hmono hv))

end DiamFixJ

namespace DiamGauss

p2m_open "ModularCurve~coeffEmb_jq~coeffEmb_qExpand"
open scoped MatrixGroups IntermediateField

theorem jq_mem (Γ : Subgroup SL(2, ℤ)) : jq ∈ qExpFunctionFieldC ℚ Γ := by
  have h := jqModC_mem_intFormRatiosC ℚ Γ
  rw [jqModC_rat] at h
  exact intFormRatiosC_subset ℚ Γ h

theorem coeffEmb_jq (L : Type*) [Field L] [Algebra ℚ L] : coeffEmb L jq = jqModC L := by
  show (jqModC ℚ).map (algebraMap ℚ L) = jqModC L
  exact map_jqModC (algebraMap ℚ L)

theorem T_mem_Gamma1 (N : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.coe_T]

theorem mem_nonunits_iff' {F : Type*} [Field F] (W : ValuationSubring F) (x : F) :
    x ∈ W.nonunits ↔ x = 0 ∨ x⁻¹ ∉ W := by
  rw [ValuationSubring.mem_nonunits_iff]
  by_cases hx : x = 0
  · simp [hx]
  · rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).mpr hx), not_le]
    simp [hx]

theorem mem_nonunits_comap_iff {F : Type*} [Field F] (W : ValuationSubring F) (e : F ≃+* F) (x : F) :
    x ∈ (W.comap (e : F →+* F)).nonunits ↔ e x ∈ W.nonunits := by
  rw [mem_nonunits_iff', mem_nonunits_iff', ValuationSubring.mem_comap]
  simp only [RingHom.coe_coe, map_inv₀, EmbeddingLike.map_eq_zero_iff]

theorem ofPowerSeries_expand {R : Type*} [CommRing R] (p : ℕ) [NeZero p] (φ : PowerSeries R) :
    HahnSeries.ofPowerSeries ℤ R (PowerSeries.expand p (NeZero.ne p) φ) =
      qExpand R p (HahnSeries.ofPowerSeries ℤ R φ) := by
  ext n
  rcases lt_or_ge n 0 with hn | hn
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hn]
    by_cases hdvd : (p : ℤ) ∣ n
    · obtain ⟨k, rfl⟩ := hdvd
      have hk : k < 0 := by
        by_contra hk
        push_neg at hk
        exact absurd (mul_nonneg (Int.natCast_nonneg p) hk) (not_le.mpr hn)
      rw [qExpand_coeff_mul, ModularCurve.ofPowerSeries_coeff_of_neg _ hk]
    · rw [qExpand_coeff_of_not_dvd p _ hdvd]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_expand]
    by_cases hdvd : p ∣ m
    · obtain ⟨k, rfl⟩ := hdvd
      rw [if_pos (dvd_mul_right p k), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne p)),
        Nat.cast_mul, qExpand_coeff_mul, HahnSeries.ofPowerSeries_apply_coeff]
    · rw [if_neg hdvd, qExpand_coeff_of_not_dvd p]
      exact fun h => hdvd (Int.natCast_dvd_natCast.mp h)

theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (p : ℕ) [NeZero p] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ p x) = qExpand L p (coeffEmb L x) := by
  ext k
  rw [coeffEmb_coeff]
  by_cases hdvd : (p : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [qExpand_coeff_of_not_dvd p _ hdvd, qExpand_coeff_of_not_dvd p _ hdvd, map_zero]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem main
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (d : ℕ) (hd : d.Coprime (M * p))
    (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' :
            ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L))
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    ∀ f : ↥K, θ f ∈ W₀ ↔ f ∈ W₀ := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  have hθj : θ j = j :=
    DiamFixJ.algEquiv_apply_eq_self_of_coe_mem_laurentBaseChange_gamma0 (M * p) L K hK d hd θ hθ j
      (by rw [hj]; exact coeffEmb_mem_laurentBaseChange L (jq_mem (CongruenceSubgroup.Gamma0 (M * p))))
  have hθA : ∀ a : A, θ (algebraMap A ↥K a) = algebraMap A ↥K a := by
    intro a
    rw [IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes]

  obtain ⟨W, hWmem, hWA, hWm, hWj, hWnu⟩ :=
    exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC (CongruenceSubgroup.Gamma1 (M * p)) L K hK A j hj
  obtain rfl : W₀ = W := ValuationSubring.ext W₀ W (fun f => (hW₀ f).trans (hWmem f).symm)

  obtain ⟨σw, hσj, -, hσ3, -⟩ :=
    XOneP.exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_and_coe_eq_atkinLehnerInvolutionFull_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj
  obtain ⟨hσW, hσj'⟩ := hσ3 W₀ hW₀
  obtain ⟨w⟩ := nonempty_integralWeightOneForm (IsLocalRing.ResidueField A) M (by omega)
  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} := hϖirr.maximalIdeal_eq
  obtain ⟨hcomplete, -, -, -⟩ :=
    XOneP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj w ϖ hϖ W₀ hW₀ σw hσj hσW hσj'

  have hVθ : W₀.comap (θ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom = W₀ ∨
      W₀.comap (θ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom = (W₀.comap (σw : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) := by
    let θA : ↥K →ₐ[A] ↥K := { (θ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom with commutes' := hθA }
    have hθA_apply : ∀ x, θA x = θ x := fun _ => rfl
    apply hcomplete
    · intro a
      show θ (algebraMap A ↥K a) ∈ W₀
      rw [hθA]; exact hWA a
    · intro a ha
      have : algebraMap A ↥K a ∈ (W₀.comap ((θ : ↥K ≃ₐ[L] ↥K).toRingEquiv : ↥K →+* ↥K)).nonunits := by
        rw [mem_nonunits_comap_iff]
        show θ (algebraMap A ↥K a) ∈ W₀.nonunits
        rw [hθA]; exact hWm a ha
      exact this
    · intro P hP
      obtain ⟨h1, h2⟩ := hWj P hP
      have hθP : θ (Polynomial.aeval j P) = Polynomial.aeval j P := by
        rw [← hθA_apply, ← Polynomial.aeval_algHom_apply, hθA_apply, hθj]
      constructor
      · show θ (Polynomial.aeval j P) ∈ W₀
        rw [hθP]; exact h1
      · show θ (Polynomial.aeval j P)⁻¹ ∈ W₀
        rw [map_inv₀, hθP]; exact h2
  rcases hVθ with hV | hV
  ·
    intro f
    exact (SetLike.ext_iff.mp hV f)
  ·
    exfalso
    have hθσ : ∀ f : ↥K, θ f ∈ W₀ ↔ σw f ∈ W₀ := fun f => SetLike.ext_iff.mp hV f

    let ψ : ↥W₀ ≃+* ↥W₀ :=
      { toFun := fun v => ⟨θ (σw.symm v), (hθσ _).mpr (by rw [AlgEquiv.apply_symm_apply]; exact v.2)⟩
        invFun := fun v => ⟨σw (θ.symm v), (hθσ (θ.symm v)).mp (by rw [AlgEquiv.apply_symm_apply]; exact v.2)⟩
        left_inv := fun v => Subtype.ext (by
          show σw (θ.symm (θ (σw.symm v))) = v
          rw [AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply])
        right_inv := fun v => Subtype.ext (by
          show θ (σw.symm (σw (θ.symm v))) = v
          rw [AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply])
        map_mul' := fun a b => Subtype.ext (by
          show θ (σw.symm ((a : ↥K) * b)) = θ (σw.symm a) * θ (σw.symm b)
          rw [map_mul, map_mul])
        map_add' := fun a b => Subtype.ext (by
          show θ (σw.symm ((a : ↥K) + b)) = θ (σw.symm a) + θ (σw.symm b)
          rw [map_add, map_add]) }
    have hψ_apply : ∀ v : ↥W₀, ((ψ v : ↥W₀) : ↥K) = θ (σw.symm v) := fun _ => rfl

    obtain ⟨red, hred, hker⟩ :=
      ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries L K A W₀ hW₀ hWnu

    let x : PowerSeries A := jNum.map (Int.castRingHom A)
    have hxL : x.map (algebraMap A L) = jNum.map (Int.castRingHom L) := by
      ext n
      rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
    have hXL : (PowerSeries.X : PowerSeries A).map (algebraMap A L) = PowerSeries.X := PowerSeries.map_X _
    have hjser : (j : LaurentSeries L) = HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) := by
      rw [hj, coeffEmb_jq, hxL]; rfl
    have hpres_j : (j : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L ((PowerSeries.X : PowerSeries A).map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) := by
      rw [hXL, HahnSeries.ofPowerSeries_X, hjser, mul_comm (HahnSeries.single (-1 : ℤ) (1 : L)), mul_assoc,
        HahnSeries.single_mul_single, show (-1 : ℤ) + 1 = 0 from by norm_num, mul_one]
      exact mul_one _
    have hXres : (PowerSeries.X : PowerSeries A).map (IsLocalRing.residue A) ≠ 0 := by
      rw [PowerSeries.map_X]; exact PowerSeries.X_ne_zero
    have hjW : j ∈ W₀ := (hW₀ j).mpr ⟨x, PowerSeries.X, hXres, hpres_j⟩
    have hσser : ((σw j : ↥K) : LaurentSeries L) = qExpand L p (j : LaurentSeries L) := by
      rw [hσj, hj, coeffEmb_qExpand]
    have hpres_s : ((σw j : ↥K) : LaurentSeries L) *
          HahnSeries.ofPowerSeries ℤ L ((PowerSeries.expand p (NeZero.ne p) (PowerSeries.X : PowerSeries A)).map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L ((PowerSeries.expand p (NeZero.ne p) x).map (algebraMap A L)) := by
      rw [PowerSeries.map_expand, PowerSeries.map_expand, ofPowerSeries_expand, ofPowerSeries_expand, hσser,
        ← map_mul, hpres_j]
    have hXpres : (PowerSeries.expand p (NeZero.ne p) (PowerSeries.X : PowerSeries A)).map (IsLocalRing.residue A) ≠ 0 := by
      rw [PowerSeries.map_expand, PowerSeries.map_X, PowerSeries.expand_X]
      exact pow_ne_zero _ PowerSeries.X_ne_zero
    have hσjW : σw j ∈ W₀ := (hW₀ _).mpr ⟨_, _, hXpres, hpres_s⟩

    let jW : ↥W₀ := ⟨j, hjW⟩
    let sW : ↥W₀ := ⟨σw j, hσjW⟩
    have hred_j : red jW = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) ((PowerSeries.X : PowerSeries A).map (IsLocalRing.residue A)) :=
      hred jW x PowerSeries.X hXres hpres_j
    have hred_s : red sW = qExpand (IsLocalRing.ResidueField A) p (red jW) := by
      rw [hred sW _ _ hXpres hpres_s, hred_j, PowerSeries.map_expand, PowerSeries.map_expand,
        ofPowerSeries_expand, ofPowerSeries_expand, map_div₀]

    haveI : CharP (IsLocalRing.ResidueField A) p := IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal A p hAp
    haveI : ExpChar (IsLocalRing.ResidueField A) p := ExpChar.prime hp
    have hfrob : frobenius (IsLocalRing.ResidueField A) p = RingHom.id (IsLocalRing.ResidueField A) := by
      refine RingHom.ext fun a => ?_
      obtain ⟨n, rfl⟩ :=
        IsCyclotomicExtension.Rat.surjective_algebraMap_int_residueField_of_isDiscreteValuationRing p L A hAp a
      rw [RingHom.id_apply, eq_intCast, map_intCast]
    have hFrob : ∀ s : LaurentSeries (IsLocalRing.ResidueField A), s ^ p = qExpand (IsLocalRing.ResidueField A) p s := by
      intro s
      rw [pow_char_eq_map_frobenius_qExpand p s, hfrob]
      ext n
      rfl

    have hψs : ψ sW = jW := Subtype.ext (by
      rw [hψ_apply]
      show θ (σw.symm (σw j)) = j
      rw [AlgEquiv.symm_apply_apply, hθj])

    have h1 : jW ^ p - sW ∈ IsLocalRing.maximalIdeal ↥W₀ := by
      rw [← hker, RingHom.mem_ker, map_sub, map_pow, hred_s, hFrob, sub_self]
    have hψmax : ∀ v : ↥W₀, v ∈ IsLocalRing.maximalIdeal ↥W₀ → ψ v ∈ IsLocalRing.maximalIdeal ↥W₀ := by
      intro v hv
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hv ⊢
      intro hu
      apply hv
      have := hu.map ψ.symm
      rwa [RingEquiv.symm_apply_apply] at this
    have h2 : (ψ jW) ^ p - jW ∈ IsLocalRing.maximalIdeal ↥W₀ := by
      have := hψmax _ h1
      rwa [map_sub, map_pow, hψs] at this
    have h3 : red ((ψ jW) ^ p) = red jW := by
      rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hker]
      exact h2

    have h4 : (red ((ψ jW) ^ p)).coeff (-1) = 0 := by
      rw [map_pow, hFrob, qExpand_coeff_of_not_dvd p]
      intro hdvd
      have : (p : ℤ) ∣ 1 := (dvd_neg).mp hdvd
      have hp1 : p = 1 := by exact_mod_cast Int.eq_one_of_dvd_one (Int.natCast_nonneg p) this
      exact hp.one_lt.ne' hp1
    have h5 : (red jW).coeff (-1) = 1 := by
      have hmul : red jW * HahnSeries.single (1 : ℤ) (1 : (IsLocalRing.ResidueField A)) =
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) := by
        rw [hred_j, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
        exact div_mul_cancel₀ _ (HahnSeries.single_ne_zero one_ne_zero)
      have hc : (red jW * HahnSeries.single (1 : ℤ) (1 : (IsLocalRing.ResidueField A))).coeff ((-1 : ℤ) + 1) =
          (HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A))).coeff ((-1 : ℤ) + 1) := by rw [hmul]
      rw [HahnSeries.coeff_mul_single_add, mul_one] at hc
      rw [hc, show ((-1 : ℤ) + 1) = ((0 : ℕ) : ℤ) by norm_num, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
        PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum, map_one, map_one]
    rw [h3, h5] at h4
    exact one_ne_zero h4

end DiamGauss

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

    (d : ℕ) (hd : d.Coprime (M * p))
    (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' :
            ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L))

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    ∀ f : ↥K, θ f ∈ W₀ ↔ f ∈ W₀ :=
  DiamGauss.main p M hM hpM L ζ hζ K hK A hAp hζA j hj d hd θ hθ W₀ hW₀

end S_ModularCurve_XOneP_apply_mem_gaussValuationSubring_iff_of_apply_eq_diamondAut_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_apply_mem_gaussValuationSubring_iff_of_apply_eq_diamondAut_x1_mul (solution)
