-- Prove2me | solution 1 for ModularCurve.XOne.isSeparable_residueField_of_height_eq_one_of_map_maximalIdeal_le_chartAlgFin_levelRaise_x1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/97958c0f-074b-56e2-8fb1-a648cd95daef

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_IsIntegrallyClosed_exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one
import Theorems.Thm_ModularCurve_XOneP_mem_valuationSubring_iff_exists_powerSeries_of_x1
import Theorems.Thm_Polynomial_aeval_notMem_of_height_eq_one_of_map_residue_ne_zero
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_x1FunctionField
import Theorems.Thm_ModularCurve_XOneP_exists_ringHom_residueField_eq_of_gaussPresentation_x1_mul
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Theorems.Thm_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing
import Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
import Theorems.Thm_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOne_isSeparable_residueField_of_height_eq_one_of_map_maximalIdeal_le_chartAlgFin_levelRaise_x1
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec"
p2m_attr_erase "simp" "CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun"
p2m_attr_erase "simp" "KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0"
p2m_attr_erase "simp" "TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false

open AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC intFormRatiosC mem_intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset x1FunctionFieldC x1FunctionField x1FunctionFieldC_le_of_dvd jq ofPowerSeries_coeff_of_neg coeffMap coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC map_jqModC XOneP.mem_valuationSubring_iff_exists_powerSeries_of_x1 finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq exists_gaussValuationSubring_laurentBaseChange_x1FunctionField XOneP.exists_ringHom_residueField_eq_of_gaussPresentation_x1_mul nonempty_integralWeightOneForm exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC jqModC_mem_intFormRatiosC"
namespace XOne
namespace VertSepLink
p2m_open "ModularCurve"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem link_full
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 5 ≤ N) (hpN : ¬ p ∣ N)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (Q : Ideal ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j)) [Q.IsPrime] (hQ1 : Q.height = 1)
    (hQv : Ideal.map (algebraMap A ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j)) (IsLocalRing.maximalIdeal A) ≤ Q) :
    (∀ f : ↥K, f ∈ W₀ ↔ ∃ c s : ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j), s ∉ Q ∧
      f * (s : ↥K) = (c : ↥K)) ∧
    (∀ b : ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀) ∧
    (∀ b : ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j), b ∈ Q ↔ (b : ↥K) ∈ W₀.nonunits) ∧
    ∃ ι : IsLocalRing.ResidueField ↥W₀ ≃+* Q.ResidueField,
      ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j)) (hb : (b : ↥K) ∈ W₀),
        ι (IsLocalRing.residue ↥W₀ ⟨(b : ↥K), hb⟩) =
          algebraMap ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) Q.ResidueField b := by
  classical

  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T]
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by
    subst hK
    exact ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 N) hT L _ rfl j hj
  haveI hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by
    haveI := hFD
    haveI : Algebra.IsIntegral ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsIntegral.of_finite _ _
    exact Algebra.IsSeparable.of_integral _ _
  haveI halgj : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by
    haveI := hFD; exact Algebra.IsAlgebraic.of_finite _ _

  haveI hNoeth : IsNoetherianRing ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) := by
    haveI := (TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep).1
    exact Algebra.FiniteType.isNoetherianRing A _
  haveI hIC : IsIntegrallyClosed ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) :=
    TwoChartIntegralModel.isIntegrallyClosed_chartAlg A (↥K) ({j} : Set ↥K)
  haveI hFrac : IsFractionRing ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) ↥K :=
    TwoChartIntegralModel.isFractionRing_chartAlg A L (↥K) ({j} : Set ↥K)

  obtain ⟨V, hVmem, hCV, hVnu, -, ι, hι⟩ :=
    IsIntegrallyClosed.exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one (K := ↥K) Q hQ1

  have hVA : ∀ a : A, algebraMap A ↥K a ∈ V := fun a => by
    have h := hCV (algebraMap A ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) a)
    rwa [← IsScalarTower.algebraMap_apply] at h
  have hVm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits := fun a ha => by
    have h := (hVnu (algebraMap A ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) a)).mpr
      (hQv (Ideal.mem_map_of_mem _ ha))
    rwa [← IsScalarTower.algebraMap_apply] at h
  have hVj : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V := fun P hP => by

    have hcoe : ∀ P : Polynomial A,
        ((Polynomial.aeval (TwoChartIntegralModel.jChartFin A (↥K) j) P :
          ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = Polynomial.aeval j P := fun P => by
      rw [← Subalgebra.coe_val, ← Polynomial.aeval_algHom_apply]
      rfl
    have hx : Function.Injective (Polynomial.aeval (R := A) (TwoChartIntegralModel.jChartFin A (↥K) j)) := by
      have hinj : Function.Injective (Polynomial.aeval (R := A) j) := transcendental_iff_injective.mp htj
      refine Function.Injective.of_comp (f := fun b : ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) => (b : ↥K)) ?_
      have : ((fun b : ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) => (b : ↥K)) ∘
          (Polynomial.aeval (R := A) (TwoChartIntegralModel.jChartFin A (↥K) j))) = Polynomial.aeval (R := A) j := by
        funext P; exact hcoe P
      rw [this]; exact hinj
    have hint : (Polynomial.aeval (R := A) (TwoChartIntegralModel.jChartFin A (↥K) j)).toRingHom.IsIntegral := by
      intro b
      letI := (Polynomial.aeval (R := A) (TwoChartIntegralModel.jChartFin A (↥K) j)).toRingHom.toAlgebra
      haveI : Module.Finite (Polynomial A) ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) :=
        (TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep).1
      exact Algebra.IsIntegral.isIntegral b
    have hnot := Polynomial.aeval_notMem_of_height_eq_one_of_map_residue_ne_zero
      (TwoChartIntegralModel.jChartFin A (↥K) j) hx hint Q hQ1 hQv P hP
    have hmem : Polynomial.aeval j P ∈ V := by rw [← hcoe]; exact hCV _
    refine ⟨hmem, ?_⟩
    have hnu : Polynomial.aeval j P ∉ V.nonunits := fun h => by
      rw [← hcoe P] at h
      exact hnot ((hVnu _).mp h)
    rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hnu
    exact hnu.2

  have hVeq : V = W₀ := by
    ext f
    rw [hW₀ f]
    exact ModularCurve.XOneP.mem_valuationSubring_iff_exists_powerSeries_of_x1 p N hN hpN L ζ hζ K hK A hAp hζA
      j hj V hVA hVm hVj f
  subst hVeq
  exact ⟨fun f => hVmem f, hCV, fun b => (hVnu b).symm, ι, hι⟩

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem link
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 5 ≤ N) (hpN : ¬ p ∣ N)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (Q : Ideal ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j)) [Q.IsPrime] (hQ1 : Q.height = 1)
    (hQv : Ideal.map (algebraMap A ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j)) (IsLocalRing.maximalIdeal A) ≤ Q) :
    (∀ b : ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀) ∧
    (∀ b : ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j), b ∈ Q ↔ (b : ↥K) ∈ W₀.nonunits) ∧
    ∃ ι : IsLocalRing.ResidueField ↥W₀ ≃+* Q.ResidueField,
      ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j)) (hb : (b : ↥K) ∈ W₀),
        ι (IsLocalRing.residue ↥W₀ ⟨(b : ↥K), hb⟩) =
          algebraMap ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) Q.ResidueField b := by
  obtain ⟨-, h⟩ := link_full p N hN hpN L ζ hζ K hK A hAp hζA j hj W₀ hW₀ Q hQ1 hQv
  exact h

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem link_of_nonunits
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 5 ≤ N) (hpN : ¬ p ∣ N)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hA : ∀ a : A, algebraMap A ↥K a ∈ W₀)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ W₀.nonunits)
    (hjW : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ W₀ ∧ (Polynomial.aeval j P)⁻¹ ∈ W₀)
    (P : Ideal ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j)) [P.IsPrime]
    (hP : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j), b ∈ P ↔ (b : ↥K) ∈ W₀.nonunits) :
    P.height = 1 ∧
    Ideal.map (algebraMap A ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j)) (IsLocalRing.maximalIdeal A) ≤ P ∧
    (∀ b : ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀) ∧
    ∃ ι : IsLocalRing.ResidueField ↥W₀ ≃+* P.ResidueField,
      ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j)) (hb : (b : ↥K) ∈ W₀),
        ι (IsLocalRing.residue ↥W₀ ⟨(b : ↥K), hb⟩) =
          algebraMap ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) P.ResidueField b := by
  classical
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.coe_T]
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by
    subst hK
    exact ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 N) hT L _ rfl j hj
  haveI hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by
    haveI := hFD
    haveI : Algebra.IsIntegral ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsIntegral.of_finite _ _
    exact Algebra.IsSeparable.of_integral _ _
  obtain ⟨-, ⟨𝔓, h𝔓, h𝔓1, h𝔓mem, h𝔓A, -⟩, -⟩ :=
    TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
      A L (↥K) j htj hFD hsep W₀ hA hm hjW
  have hPeq : P = 𝔓 := by
    ext b; rw [hP b, h𝔓mem b]
  subst hPeq
  have hPv : Ideal.map (algebraMap A ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j)) (IsLocalRing.maximalIdeal A) ≤ P :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => h𝔓A a ha
  obtain ⟨ha, -, hc⟩ := link p N hN hpN L ζ hζ K hK A hAp hζA j hj W₀ hW₀ P h𝔓1 hPv
  exact ⟨h𝔓1, hPv, ha, hc⟩

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem mem_nonunits_iff_of_coe_eq
    (L : Type) [Field L] (K_M K_N : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L]
    (WM : ValuationSubring ↥K_M)
    (hWM : ∀ f : ↥K_M, f ∈ WM ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (WN : ValuationSubring ↥K_N)
    (hWN : ∀ f : ↥K_N, f ∈ WN ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (f : ↥K_M) (g : ↥K_N) (hfg : (g : LaurentSeries L) = (f : LaurentSeries L)) :
    (g ∈ WN ↔ f ∈ WM) ∧ (g ∈ WN.nonunits ↔ f ∈ WM.nonunits) := by
  have memTr : ∀ (f : ↥K_M) (g : ↥K_N), (g : LaurentSeries L) = (f : LaurentSeries L) → (g ∈ WN ↔ f ∈ WM) :=
    fun f g h => by rw [hWN g, hWM f, h]
  refine ⟨memTr f g hfg, ?_⟩
  have h0 : g = 0 ↔ f = 0 := by
    constructor
    · intro h; apply Subtype.ext
      have : (g : LaurentSeries L) = 0 := by rw [h]; rfl
      rw [hfg] at this; exact this
    · intro h; apply Subtype.ext
      have : (f : LaurentSeries L) = 0 := by rw [h]; rfl
      rw [← hfg] at this; exact this
  have hinv : g⁻¹ ∈ WN ↔ f⁻¹ ∈ WM :=
    memTr f⁻¹ g⁻¹ (by rw [IntermediateField.coe_inv, IntermediateField.coe_inv, hfg])
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, h0, hinv]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem under_iff
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMp : ¬ ℓ ∣ M * p)

    (K_M : IntermediateField L (LaurentSeries L))
    (hK_M : K_M = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    [Algebra A ↥K_M] [IsScalarTower A L ↥K_M]
    (j_M : ↥K_M) (hj_M : ((j_M : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j_M ≠ 0)]
    (K_N : IntermediateField L (LaurentSeries L))
    (hK_N : K_N = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * ℓ)))
    [Algebra A ↥K_N] [IsScalarTower A L ↥K_N]
    (j_N : ↥K_N) (hj_N : ((j_N : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j_N ≠ 0)]
    (hleMN : K_M ≤ K_N)
    (ι_M : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) →ₐ[A] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N))
    (hι_M : ∀ x, (((ι_M x : ↥K_N) : LaurentSeries L)) = ((x : ↥K_M) : LaurentSeries L))

    [Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)]
    (halg : ∀ x, algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)
        ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) x = ι_M x)

    (Q : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) [Q.IsPrime] (hQ1 : Q.height = 1)
    (hQv : Ideal.map (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) (IsLocalRing.maximalIdeal A) ≤ Q)
    (WM : ValuationSubring ↥K_M)
    (hWM : ∀ f : ↥K_M, f ∈ WM ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (WN : ValuationSubring ↥K_N)
    (hWN : ∀ f : ↥K_N, f ∈ WN ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    :
    ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M), b ∈ Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↔ (b : ↥K_M) ∈ WM.nonunits := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) hℓ.ne_zero⟩
  have hN : 5 ≤ M * ℓ := le_mul_of_le_of_one_le hM hℓ.one_lt.le
  have hpN : ¬ p ∣ M * ℓ := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with hpm | hpl
    · exact hpM hpm
    · have : p = ℓ := (Nat.prime_dvd_prime_iff_eq hp hℓ).mp hpl
      apply hℓMp; rw [← this]; exact dvd_mul_left p M
  obtain ⟨-, hQnu, -⟩ := link p (M * ℓ) hN hpN L ζ hζ K_N hK_N A hAp hζA j_N hj_N WN hWN Q hQ1 hQv
  intro b
  have h1 : b ∈ Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↔ ι_M b ∈ Q := by
    rw [Ideal.under_def, Ideal.mem_comap, halg]
  rw [h1, hQnu (ι_M b)]
  exact (mem_nonunits_iff_of_coe_eq L K_M K_N A WM hWM WN hWN (b : ↥K_M) ((ι_M b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) : ↥K_N) (hι_M b)).2

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem compat
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMp : ¬ ℓ ∣ M * p)

    (K_M : IntermediateField L (LaurentSeries L))
    (hK_M : K_M = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    [Algebra A ↥K_M] [IsScalarTower A L ↥K_M]
    (j_M : ↥K_M) (hj_M : ((j_M : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j_M ≠ 0)]
    (K_N : IntermediateField L (LaurentSeries L))
    (hK_N : K_N = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * ℓ)))
    [Algebra A ↥K_N] [IsScalarTower A L ↥K_N]
    (j_N : ↥K_N) (hj_N : ((j_N : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j_N ≠ 0)]
    (hleMN : K_M ≤ K_N)
    (ι_M : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) →ₐ[A] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N))
    (hι_M : ∀ x, (((ι_M x : ↥K_N) : LaurentSeries L)) = ((x : ↥K_M) : LaurentSeries L))
    (WM : ValuationSubring ↥K_M)
    (hWM : ∀ f : ↥K_M, f ∈ WM ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (WN : ValuationSubring ↥K_N)
    (hWN : ∀ f : ↥K_N, f ∈ WN ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (eM : IsLocalRing.ResidueField ↥WM →+* LaurentSeries (IsLocalRing.ResidueField A))
    (heM : ∀ (f : ↥WM) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      ((f : ↥K_M) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      eM (IsLocalRing.residue ↥WM f) =
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)))
    (eN : IsLocalRing.ResidueField ↥WN →+* LaurentSeries (IsLocalRing.ResidueField A))
    (heN : ∀ (f : ↥WN) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      ((f : ↥K_N) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      eN (IsLocalRing.residue ↥WN f) =
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)))
    (hBM : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M), (b : ↥K_M) ∈ WM)
    (hBN : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N), (b : ↥K_N) ∈ WN) :
    ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M),
      eN (IsLocalRing.residue ↥WN ⟨((ι_M b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) : ↥K_N), hBN (ι_M b)⟩) =
        eM (IsLocalRing.residue ↥WM ⟨(b : ↥K_M), hBM b⟩) := by
  intro b
  obtain ⟨x, y, hy, hxy⟩ := (hWM (b : ↥K_M)).mp (hBM b)
  have hq : (((ι_M b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) : ↥K_N) : LaurentSeries L)
      = ((b : ↥K_M) : LaurentSeries L) := hι_M b
  have hxyN := hxy
  rw [← hq] at hxyN
  have h1 := heN ⟨_, hBN (ι_M b)⟩ x y hy hxyN
  have h2 := heM ⟨_, hBM b⟩ x y hy hxy
  exact h1.trans h2.symm

end ModularCurve.XOne.VertSepLink

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC intFormRatiosC mem_intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset x1FunctionFieldC x1FunctionField x1FunctionFieldC_le_of_dvd jq ofPowerSeries_coeff_of_neg coeffMap coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC map_jqModC XOneP.mem_valuationSubring_iff_exists_powerSeries_of_x1 finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq exists_gaussValuationSubring_laurentBaseChange_x1FunctionField XOneP.exists_ringHom_residueField_eq_of_gaussPresentation_x1_mul nonempty_integralWeightOneForm exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC jqModC_mem_intFormRatiosC"
namespace XOne
namespace VertSepDict
p2m_open "ModularCurve"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem gaussResidue
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 5 ≤ N) (hpN : ¬ p ∣ N)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    ∃ e' : IsLocalRing.ResidueField ↥W₀ →+* LaurentSeries (IsLocalRing.ResidueField A),
      Function.Injective e' ∧
      Set.range e' = (ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) N :
        Set (LaurentSeries (IsLocalRing.ResidueField A))) ∧
      (∀ (f : ↥W₀) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        ((f : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        e' (IsLocalRing.residue ↥W₀ f) =
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))) ∧
      (∀ (a : A) (ha : algebraMap A ↥K a ∈ W₀), e' (IsLocalRing.residue ↥W₀ ⟨algebraMap A ↥K a, ha⟩) =
        algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a)) := by
  classical

  haveI : NeZero (N * p) := ⟨Nat.mul_ne_zero (NeZero.ne N) (Fact.out : p.Prime).ne_zero⟩
  let Kp : IntermediateField L (LaurentSeries L) :=
    ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (N * p))
  letI : Algebra A ↥Kp := ((algebraMap L ↥Kp).comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L ↥Kp := IsScalarTower.of_algebraMap_eq' rfl

  have hle : K ≤ Kp := by
    rw [hK]
    change ModularCurve.laurentBaseChange L _ ≤ ModularCurve.laurentBaseChange L _
    rw [ModularCurve.laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact ModularCurve.coeffEmb_mem_laurentBaseChange L
      (ModularCurve.x1FunctionFieldC_le_of_dvd ℚ (dvd_mul_right N p) hy)

  let jp : ↥Kp := IntermediateField.inclusion hle j
  have hjp : ((jp : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq := by
    rw [← hj]; rfl
  haveI : Fact (jp ≠ 0) := ⟨fun h0 => (Fact.out : j ≠ 0)
    ((IntermediateField.inclusion_injective hle) (by rw [map_zero]; exact h0))⟩

  obtain ⟨w⟩ := ModularCurve.nonempty_integralWeightOneForm (IsLocalRing.ResidueField A) N (by omega)

  obtain ⟨W₀p, hW₀p, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_x1FunctionField (N * p) L Kp rfl A jp hjp

  have hW₀' : ∀ f' : ↥K, f' ∈ W₀ ↔ IntermediateField.inclusion hle f' ∈ W₀p := by
    intro f'
    rw [hW₀ f', hW₀p (IntermediateField.inclusion hle f')]
    rfl
  obtain ⟨e, e', -, he', -, hre', -, -, -, he'pres, he'const⟩ :=
    ModularCurve.XOneP.exists_ringHom_residueField_eq_of_gaussPresentation_x1_mul p N hN hpN L ζ hζ Kp rfl A hAp hζA
      jp hjp K hK hle j hj w W₀p hW₀p W₀ hW₀'
  exact ⟨e', he', hre', he'pres, he'const⟩

end ModularCurve.XOne.VertSepDict

p2m_open "ModularCurve P2MW.S_ModularCurve_XOne_isSeparable_residueField_of_height_eq_one_of_map_maximalIdeal_le_chartAlgFin_levelRaise_x1.ModularCurve"

namespace VertSepField

section Pure

variable {κ k T : Type} [Field κ] [Field k] [Field T] [Algebra κ k] [Algebra k T] [Algebra κ T]
  [IsScalarTower κ k T]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem isSeparable_adjoin_of_isSeparable_adjoin [Algebra.IsSeparable κ k] (t : T)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin k ({t} : Set T)) T) :
    Algebra.IsSeparable ↥(IntermediateField.adjoin κ ({t} : Set T)) T := by
  classical
  set FT : IntermediateField κ T := IntermediateField.adjoin κ ({t} : Set T) with hFT
  let Kk : IntermediateField ↥FT T := IntermediateField.adjoin ↥FT (Set.range (algebraMap k T))
  haveI hsep1 : Algebra.IsSeparable ↥FT ↥Kk := by
    rw [IntermediateField.isSeparable_adjoin_iff_isSeparable]
    rintro _ ⟨a, rfl⟩
    have ha : IsSeparable κ (algebraMap k T a) := by
      have h := IsSeparable.map (IsScalarTower.toAlgHom κ k T) (algebraMap k T).injective
        (Algebra.IsSeparable.isSeparable κ a)
      simpa using h
    exact ha.tower_top ↥FT

  have hcar : ∀ x : T, x ∈ Kk ↔ x ∈ IntermediateField.adjoin k ({t} : Set T) := by
    intro x
    constructor
    · intro hx
      have hle : (Kk.toSubfield : Subfield T) ≤ (IntermediateField.adjoin k ({t} : Set T)).toSubfield := by
        rw [show Kk = IntermediateField.adjoin ↥FT (Set.range (algebraMap k T)) from rfl,
          IntermediateField.adjoin_toSubfield, Subfield.closure_le]
        rintro z (⟨c, rfl⟩ | ⟨a, rfl⟩)
        · have hFle : (FT.toSubfield : Subfield T) ≤ (IntermediateField.adjoin k ({t} : Set T)).toSubfield := by
            rw [hFT, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
            rintro w (⟨c', rfl⟩ | hw)
            · rw [IsScalarTower.algebraMap_apply κ k T]
              exact (IntermediateField.adjoin k ({t} : Set T)).algebraMap_mem (algebraMap κ k c')
            · exact IntermediateField.subset_adjoin k _ hw
          exact hFle c.2
        · exact (IntermediateField.adjoin k ({t} : Set T)).algebraMap_mem a
      exact hle hx
    · intro hx
      have hle : (IntermediateField.adjoin k ({t} : Set T)).toSubfield ≤ Kk.toSubfield := by
        rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
        rintro z (⟨a, rfl⟩ | hz)
        · exact IntermediateField.subset_adjoin ↥FT _ ⟨a, rfl⟩
        · rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact Kk.algebraMap_mem ⟨t, IntermediateField.mem_adjoin_simple_self κ t⟩
      exact hle hx
  haveI hsep2 : Algebra.IsSeparable ↥Kk T := by
    let e₁ : ↥(IntermediateField.adjoin k ({t} : Set T)) ≃+* ↥Kk :=
      { toFun := fun x => ⟨x.1, (hcar x.1).mpr x.2⟩
        invFun := fun y => ⟨y.1, (hcar y.1).mp y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl
        map_add' := fun _ _ => rfl }
    exact Algebra.IsSeparable.of_equiv_equiv e₁ (RingEquiv.refl T) (by ext x; rfl)
  haveI := hsep2
  exact Algebra.IsSeparable.trans ↥FT ↥Kk T

variable {F : Type} [Field F] [Algebra F T]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem isSeparable_of_le_of_le (EM EN : IntermediateField F T) (h : EM ≤ EN) [Algebra.IsSeparable F T] :
    @Algebra.IsSeparable ↥EM ↥EN _ _ (IntermediateField.inclusion h).toRingHom.toAlgebra := by
  letI := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower F ↥EM ↥EN := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.IsSeparable F ↥EN := Algebra.isSeparable_tower_bot_of_isSeparable F ↥EN T
  exact Algebra.isSeparable_tower_top_of_isSeparable F ↥EM ↥EN

end Pure

section Coeff

variable (κ : Type) [Field κ] (k : Type) [Field k] [Algebra κ k]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

abbrev φ : LaurentSeries κ →+* LaurentSeries k := coeffMap (algebraMap κ k)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem φ_coeff (x : LaurentSeries κ) (n : ℤ) : (φ κ k x).coeff n = algebraMap κ k (x.coeff n) := rfl

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem φ_injective : Function.Injective (φ κ k) := by
  intro x y h
  ext n
  have := congrArg (fun z : LaurentSeries k => z.coeff n) h
  exact (algebraMap κ k).injective (by simpa [φ_coeff] using this)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem φ_intSeriesC (r : PowerSeries ℤ) : φ κ k (intSeriesC κ r) = intSeriesC k r := by
  ext n
  rw [φ_coeff]
  simp only [intSeriesC]
  rcases lt_or_ge n 0 with hn | hn
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hn, ModularCurve.ofPowerSeries_coeff_of_neg _ hn, map_zero]
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_map]
    simp

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem φ_C (c : κ) : φ κ k (HahnSeries.C c) = HahnSeries.C (algebraMap κ k c) := by
  ext n
  rw [φ_coeff, HahnSeries.C_apply, HahnSeries.C_apply, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs <;> simp

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem φ_algebraMap (c : κ) : φ κ k (algebraMap κ (LaurentSeries κ) c) = algebraMap k (LaurentSeries k) (algebraMap κ k c) := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.algebraMap_laurentSeries_eq_single]
  exact ModularCurve.coeffMap_single (algebraMap κ k) 0 c

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem φ_jqModC : φ κ k (jqModC κ) = jqModC k := map_jqModC (algebraMap κ k)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem φ_mem {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} {x : LaurentSeries κ}
    (hx : x ∈ qExpFunctionFieldC κ Γ) : φ κ k x ∈ qExpFunctionFieldC k Γ := by
  have hsub : (qExpFunctionFieldC κ Γ).toSubfield ≤ (qExpFunctionFieldC k Γ).toSubfield.comap (φ κ k) := by
    rw [show qExpFunctionFieldC κ Γ = IntermediateField.adjoin κ (intFormRatiosC κ Γ) from rfl,
      IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro z (⟨c, rfl⟩ | ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩)
    · show φ κ k (algebraMap κ (LaurentSeries κ) c) ∈ (qExpFunctionFieldC k Γ).toSubfield
      rw [φ_algebraMap]
      exact (qExpFunctionFieldC k Γ).algebraMap_mem (algebraMap κ k c)
    · show φ κ k (intSeriesC κ pf / intSeriesC κ pg) ∈ (qExpFunctionFieldC k Γ).toSubfield
      rw [map_div₀, φ_intSeriesC, φ_intSeriesC]
      have hg0' : intSeriesC k pg ≠ 0 := by
        rw [← φ_intSeriesC κ k]; exact (map_ne_zero_iff _ (φ_injective κ k)).mpr hg0
      exact intFormRatiosC_subset k Γ (mem_intFormRatiosC f g hf hg hg0')
  exact hsub hx

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

noncomputable def ψ (N : ℕ) : ↥(x1FunctionFieldC κ N) →+* ↥(x1FunctionFieldC k N) where
  toFun x := ⟨φ κ k (x : LaurentSeries κ), φ_mem κ k x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem coe_ψ (N : ℕ) (x : ↥(x1FunctionFieldC κ N)) : ((ψ κ k N x : ↥(x1FunctionFieldC k N)) : LaurentSeries k) = φ κ k x := rfl

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem ψ_injective (N : ℕ) : Function.Injective (ψ κ k N) := fun x y h =>
  Subtype.ext (φ_injective κ k (congrArg (fun z : ↥(x1FunctionFieldC k N) => (z : LaurentSeries k)) h))

end Coeff

section Main

variable (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

@[reducible] noncomputable def algIncl (M N : ℕ) [h : Fact (M ∣ N)] : Algebra ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ N) :=
  (IntermediateField.inclusion (x1FunctionFieldC_le_of_dvd κ h.out)).toRingHom.toAlgebra

attribute [local instance] algIncl

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem algIncl_apply (M N : ℕ) [h : Fact (M ∣ N)] (y : ↥(x1FunctionFieldC κ M)) :
    algebraMap ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ N) y =
      IntermediateField.inclusion (x1FunctionFieldC_le_of_dvd κ h.out) y := rfl

variable [PerfectField κ]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem isSeparable_aux (k : Type) [Field k] [Algebra κ k] [IsAlgClosed k] [CharP k p] [Algebra.IsAlgebraic κ k]
    (M N : ℕ) [NeZero M] [NeZero N] [hMN' : Fact (M ∣ N)] (hN : 5 ≤ N) (hpN : ¬ p ∣ N) :
    Algebra.IsSeparable ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ N) := by
  classical
  obtain ⟨t, ht, -, -, hsep⟩ :=
    exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC p N hN hpN k

  letI algT : Algebra κ ↥(x1FunctionFieldC k N) :=
    ((algebraMap k ↥(x1FunctionFieldC k N)).comp (algebraMap κ k)).toAlgebra
  haveI : IsScalarTower κ k ↥(x1FunctionFieldC k N) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hFT : Algebra.IsSeparable ↥(IntermediateField.adjoin κ ({t} : Set ↥(x1FunctionFieldC k N))) ↥(x1FunctionFieldC k N) :=
    isSeparable_adjoin_of_isSeparable_adjoin (κ := κ) (k := k) t hsep

  let ψN : ↥(x1FunctionFieldC κ N) →+* ↥(x1FunctionFieldC k N) := ψ κ k N
  let ψM : ↥(x1FunctionFieldC κ M) →+* ↥(x1FunctionFieldC k N) :=
    ψN.comp (IntermediateField.inclusion (x1FunctionFieldC_le_of_dvd κ hMN'.out)).toRingHom
  have hψM : Function.Injective ψM :=
    (ψ_injective κ k N).comp (IntermediateField.inclusion_injective _)
  have hψMN : ∀ y : ↥(x1FunctionFieldC κ M),
      ψN (IntermediateField.inclusion (x1FunctionFieldC_le_of_dvd κ hMN'.out) y) = ψM y := fun _ => rfl

  have hFM : ∀ z : ↥(x1FunctionFieldC k N), z ∈ IntermediateField.adjoin κ ({t} : Set ↥(x1FunctionFieldC k N)) → ∃ y : ↥(x1FunctionFieldC κ M), ψM y = z := by
    have hle : (IntermediateField.adjoin κ ({t} : Set ↥(x1FunctionFieldC k N))).toSubfield ≤ ψM.fieldRange := by
      rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
      rintro z (⟨c', rfl⟩ | hz)
      · refine ⟨algebraMap κ _ c', Subtype.ext ?_⟩
        show φ κ k (algebraMap κ (LaurentSeries κ) c') = _
        rw [φ_algebraMap]; rfl
      · rw [Set.mem_singleton_iff] at hz
        rw [hz]
        refine ⟨⟨jqModC κ, intFormRatiosC_subset κ _ (jqModC_mem_intFormRatiosC κ _)⟩, Subtype.ext ?_⟩
        show φ κ k (jqModC κ) = (t : LaurentSeries k)
        rw [φ_jqModC, ht]
    intro z hz
    exact RingHom.mem_fieldRange.mp (hle hz)

  letI algMT : Algebra ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC k N) := ψM.toAlgebra
  let f : ↥(x1FunctionFieldC κ N) →ₐ[↥(x1FunctionFieldC κ M)] ↥(x1FunctionFieldC k N) :=
    { ψN with commutes' := fun y => hψMN y }

  choose g hg using fun z : ↥(IntermediateField.adjoin κ ({t} : Set ↥(x1FunctionFieldC k N))) => hFM z.1 z.2
  let gHom : ↥(IntermediateField.adjoin κ ({t} : Set ↥(x1FunctionFieldC k N))) →+* ↥(x1FunctionFieldC κ M) :=
    { toFun := g
      map_one' := hψM (by rw [hg, map_one]; rfl)
      map_mul' := fun a b => hψM (by rw [hg, map_mul, hg, hg]; rfl)
      map_zero' := hψM (by rw [hg, map_zero]; rfl)
      map_add' := fun a b => hψM (by rw [hg, map_add, hg, hg]; rfl) }
  letI algFM : Algebra ↥(IntermediateField.adjoin κ ({t} : Set ↥(x1FunctionFieldC k N))) ↥(x1FunctionFieldC κ M) := gHom.toAlgebra
  haveI : IsScalarTower ↥(IntermediateField.adjoin κ ({t} : Set ↥(x1FunctionFieldC k N))) ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC k N) :=
    IsScalarTower.of_algebraMap_eq (fun z => (hg z).symm)
  haveI hMT : Algebra.IsSeparable ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC k N) :=
    Algebra.isSeparable_tower_top_of_isSeparable ↥(IntermediateField.adjoin κ ({t} : Set ↥(x1FunctionFieldC k N))) ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC k N)
  exact Algebra.IsSeparable.of_algHom (F := ↥(x1FunctionFieldC κ M)) (E' := ↥(x1FunctionFieldC k N)) f

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem isSeparable_x1FunctionFieldC_of_dvd (M N : ℕ) [NeZero M] [NeZero N] [Fact (M ∣ N)]
    (hN : 5 ≤ N) (hpN : ¬ p ∣ N) :
    Algebra.IsSeparable ↥(x1FunctionFieldC κ M) ↥(x1FunctionFieldC κ N) := by
  haveI : CharP (AlgebraicClosure κ) p := charP_of_injective_algebraMap (algebraMap κ (AlgebraicClosure κ)).injective p
  exact isSeparable_aux p κ (AlgebraicClosure κ) M N hN hpN

end Main

end VertSepField

namespace ModularCurve p2m_export "ModularCurve" "intSeriesC intFormRatiosC mem_intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset x1FunctionFieldC x1FunctionField x1FunctionFieldC_le_of_dvd jq ofPowerSeries_coeff_of_neg coeffMap coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange jqModC map_jqModC XOneP.mem_valuationSubring_iff_exists_powerSeries_of_x1 finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange transcendental_of_coe_eq_coeffEmb_jq exists_gaussValuationSubring_laurentBaseChange_x1FunctionField XOneP.exists_ringHom_residueField_eq_of_gaussPresentation_x1_mul nonempty_integralWeightOneForm exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC jqModC_mem_intFormRatiosC" namespace XOne namespace VertSepAsm end ModularCurve.XOne.VertSepAsm
p2m_open_scoped "ModularCurve" in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem ModularCurve.XOne.VertSepAsm.finite_residueField_A
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) : Finite (IsLocalRing.ResidueField A) := by
  haveI : CharP (IsLocalRing.ResidueField A) p := IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal A p hAp
  have hs := IsCyclotomicExtension.Rat.surjective_algebraMap_int_residueField_of_isDiscreteValuationRing p L A hAp
  refine Finite.of_surjective (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)) fun x => ?_
  obtain ⟨m, rfl⟩ := hs x
  exact ⟨(m : ZMod p), by rw [map_intCast, eq_intCast]⟩

open ModularCurve.XOne in
attribute [local instance] VertSepField.algIncl in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓMp : ¬ ℓ ∣ M * p)

    (K_M : IntermediateField L (LaurentSeries L))
    (hK_M : K_M = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    [Algebra A ↥K_M] [IsScalarTower A L ↥K_M]
    (j_M : ↥K_M) (hj_M : ((j_M : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j_M ≠ 0)]
    (K_N : IntermediateField L (LaurentSeries L))
    (hK_N : K_N = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * ℓ)))
    [Algebra A ↥K_N] [IsScalarTower A L ↥K_N]
    (j_N : ↥K_N) (hj_N : ((j_N : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j_N ≠ 0)]
    (hleMN : K_M ≤ K_N)
    (ι_M : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) →ₐ[A] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N))
    (hι_M : ∀ x, (((ι_M x : ↥K_N) : LaurentSeries L)) = ((x : ↥K_M) : LaurentSeries L))

    [Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)]
    (halg : ∀ x, algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)
        ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) x = ι_M x)

    (Q : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) [Q.IsPrime] (hQ1 : Q.height = 1)
    (hQv : Ideal.map (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) (IsLocalRing.maximalIdeal A) ≤ Q)
    [Algebra (Localization.AtPrime (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M))) (Localization.AtPrime Q)]
    [Localization.AtPrime.IsLiesOverAlgebra (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)) Q] :
    Algebra.IsSeparable (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)).ResidueField Q.ResidueField := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) hℓ.ne_zero⟩
  have hN : 5 ≤ M * ℓ := le_mul_of_le_of_one_le hM hℓ.one_lt.le
  have hpN : ¬ p ∣ M * ℓ := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).mp h with hpm | hpl
    · exact hpM hpm
    · have : p = ℓ := (Nat.prime_dvd_prime_iff_eq hp hℓ).mp hpl
      apply hℓMp; rw [← this]; exact dvd_mul_left p M

  haveI hchar : CharP (IsLocalRing.ResidueField A) p := IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal A p hAp
  haveI hfin : Finite (IsLocalRing.ResidueField A) := VertSepAsm.finite_residueField_A p L A hAp
  haveI hperf : PerfectField (IsLocalRing.ResidueField A) := PerfectField.ofFinite

  obtain ⟨WM, hWM, hAM, hmM, hjWM, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_x1FunctionField M L K_M hK_M A j_M hj_M
  obtain ⟨WN, hWN, -, -, -, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_x1FunctionField (M * ℓ) L K_N hK_N A j_N hj_N

  obtain ⟨hBN, -, ιN, hιN⟩ := VertSepLink.link p (M * ℓ) hN hpN L ζ hζ K_N hK_N A hAp hζA j_N hj_N WN hWN Q hQ1 hQv
  have hP := VertSepLink.under_iff p M hM hpM L ζ hζ A hAp hζA ℓ hℓ hℓMp K_M hK_M j_M hj_M K_N hK_N j_N hj_N hleMN ι_M hι_M halg Q hQ1 hQv WM hWM WN hWN
  obtain ⟨-, -, hBM, ιM, hιM⟩ := VertSepLink.link_of_nonunits p M hM hpM L ζ hζ K_M hK_M A hAp hζA j_M hj_M WM hWM
    hAM hmM hjWM (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)) hP

  obtain ⟨eM, heMi, hreM, heMp, -⟩ := VertSepDict.gaussResidue p M hM hpM L ζ hζ K_M hK_M A hAp hζA j_M hj_M WM hWM
  obtain ⟨eN, heNi, hreN, heNp, -⟩ := VertSepDict.gaussResidue p (M * ℓ) hN hpN L ζ hζ K_N hK_N A hAp hζA j_N hj_N WN hWN
  have hcompat := VertSepLink.compat p M hM hpM L ζ hζ A hAp hζA ℓ hℓ hℓMp K_M hK_M j_M hj_M K_N hK_N j_N hj_N hleMN ι_M hι_M WM hWM WN hWN eM heMp eN heNp hBM hBN

  have hrM : ∀ x, eM x ∈ ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M := fun x => by
    have hx := Set.mem_range_self (f := eM) x
    rw [hreM] at hx; exact hx
  have hrN : ∀ x, eN x ∈ ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * ℓ) := fun x => by
    have hx := Set.mem_range_self (f := eN) x
    rw [hreN] at hx; exact hx
  let eM' : IsLocalRing.ResidueField ↥WM →+* ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) := eM.codRestrict (ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) hrM
  let eN' : IsLocalRing.ResidueField ↥WN →+* ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * ℓ)) := eN.codRestrict (ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * ℓ)) hrN
  have hbM : Function.Bijective eM' := by
    refine ⟨fun a b h => heMi (congrArg Subtype.val h), fun y => ?_⟩
    have hy : (y : LaurentSeries (IsLocalRing.ResidueField A)) ∈ Set.range eM := by rw [hreM]; exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  have hbN : Function.Bijective eN' := by
    refine ⟨fun a b h => heNi (congrArg Subtype.val h), fun y => ?_⟩
    have hy : (y : LaurentSeries (IsLocalRing.ResidueField A)) ∈ Set.range eN := by rw [hreN]; exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  let φM : IsLocalRing.ResidueField ↥WM ≃+* ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) := RingEquiv.ofBijective eM' hbM
  let φN : IsLocalRing.ResidueField ↥WN ≃+* ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * ℓ)) := RingEquiv.ofBijective eN' hbN

  haveI : Fact (M ∣ M * ℓ) := ⟨dvd_mul_right M ℓ⟩
  haveI hsepX : Algebra.IsSeparable ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * ℓ)) :=
    VertSepField.isSeparable_x1FunctionFieldC_of_dvd p (IsLocalRing.ResidueField A) M (M * ℓ) hN hpN
  let e₁ : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) ≃+* (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)).ResidueField := φM.symm.trans ιM
  let e₂ : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * ℓ)) ≃+* Q.ResidueField := φN.symm.trans ιN
  have he₁s : ∀ y, e₁.symm y = φM (ιM.symm y) := fun _ => rfl
  have he₂ : ∀ z, e₂ z = ιN (φN.symm z) := fun _ => rfl
  have hφM : ∀ r, ((φM r : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M)) : LaurentSeries (IsLocalRing.ResidueField A)) = eM r := fun _ => rfl
  have hφN : ∀ r, ((φN r : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * ℓ))) : LaurentSeries (IsLocalRing.ResidueField A)) = eN r := fun _ => rfl

  have step : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M), algebraMap (Localization.AtPrime (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M))) (Localization.AtPrime Q) (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) (Localization.AtPrime (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M))) b)
      = algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) (Localization.AtPrime Q) (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) b) := fun b => by
    rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq (p := Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)) (P := Q),
      Localization.localRingHom_to_map]
  have key : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M),
      algebraMap (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)).ResidueField Q.ResidueField (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)).ResidueField b) = algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) Q.ResidueField (ι_M b) := fun b => by
    rw [← halg b]
    exact (IsLocalRing.ResidueField.algebraMap_residue (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) (Localization.AtPrime (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M))) b)).trans
      (congrArg (IsLocalRing.residue (Localization.AtPrime Q)) (step b))

  let g₂ : (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)).ResidueField →+* Q.ResidueField := (e₂ : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * ℓ)) →+* Q.ResidueField).comp ((algebraMap ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * ℓ))).comp (e₁.symm : (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)).ResidueField →+* ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M)))
  have hg₂' : ∀ y, g₂ y = e₂ (algebraMap ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * ℓ)) (e₁.symm y)) := fun _ => rfl
  have hg₂ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M), g₂ (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)).ResidueField b) = algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) Q.ResidueField (ι_M b) := fun b => by
    rw [hg₂']
    have s1 : ιM.symm (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)).ResidueField b) = IsLocalRing.residue ↥WM ⟨(b : ↥K_M), hBM b⟩ := by
      rw [RingEquiv.symm_apply_eq]; exact (hιM b (hBM b)).symm
    have s2 : e₁.symm (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)).ResidueField b) = φM (IsLocalRing.residue ↥WM ⟨(b : ↥K_M), hBM b⟩) := by
      rw [he₁s, s1]
    have s3 : (↑(algebraMap ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * ℓ)) (e₁.symm (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)).ResidueField b))) : LaurentSeries (IsLocalRing.ResidueField A))
        = eN (IsLocalRing.residue ↥WN ⟨((ι_M b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) : ↥K_N), hBN (ι_M b)⟩) := by
      rw [s2, VertSepField.algIncl_apply, IntermediateField.coe_inclusion, hφM]
      exact (hcompat b).symm
    have s4 : algebraMap ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * ℓ)) (e₁.symm (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)).ResidueField b))
        = φN (IsLocalRing.residue ↥WN ⟨((ι_M b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) : ↥K_N), hBN (ι_M b)⟩) :=
      Subtype.ext (s3.trans (hφN _).symm)
    rw [s4, he₂, RingEquiv.symm_apply_apply]
    exact hιN (ι_M b) (hBN (ι_M b))
  have Hg : algebraMap (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)).ResidueField Q.ResidueField = g₂ := by
    apply Ideal.ResidueField.ringHom_ext
    ext b
    rw [RingHom.comp_apply, RingHom.comp_apply, key b, hg₂ b]
  have he : (algebraMap (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)).ResidueField Q.ResidueField).comp (e₁ : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) →+* (Q.under ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)).ResidueField) = (e₂ : ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * ℓ)) →+* Q.ResidueField).comp (algebraMap ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * ℓ))) := by
    refine RingHom.ext fun x => ?_
    exact (RingHom.congr_fun Hg (e₁ x)).trans ((hg₂' (e₁ x)).trans
      (congrArg (fun z => e₂ (algebraMap ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) ↥(ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * ℓ)) z)) (e₁.symm_apply_apply x)))
  exact Algebra.IsSeparable.of_equiv_equiv e₁ e₂ he

end S_ModularCurve_XOne_isSeparable_residueField_of_height_eq_one_of_map_maximalIdeal_le_chartAlgFin_levelRaise_x1
end P2MW
export P2MW.S_ModularCurve_XOne_isSeparable_residueField_of_height_eq_one_of_map_maximalIdeal_le_chartAlgFin_levelRaise_x1 (solution)
