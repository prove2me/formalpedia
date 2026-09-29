-- Prove2me | solution 1 for ModularCurve.XOne.finite_and_flat_chartAlgFin_levelRaise_x1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/afb646d4-e548-56d1-bfff-1442d3d06749

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_IsLocalRing_exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient
import Theorems.Thm_RingTheory_Sequence_isRegular_pair_of_isSMulRegular_of_isReduced_of_forall_notMem_minimalPrimes
import Theorems.Thm_Module_free_of_isRegular_of_span_eq_maximalIdeal
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isRegularLocalRing_localization_fractionRing_tensor_chartAlgFin
import Theorems.Thm_ModularCurve_XOne_exists_isDomain_isDiscreteValuationRing_localization_quotient_span_chartAlgFin_twoChartIntegralModel_x1
import Theorems.Thm_ModularCurve_XOne_isDomain_quotient_span_and_not_isMaximal_chartAlgFin_twoChartIntegralModel_x1
import Theorems.Thm_ModularCurve_XOne_isPrincipalIdealRing_localization_atPrime_chartAlgFin_of_not_mem_twoChartIntegralModel_x1
import Theorems.Thm_ModularCurve_XOne_not_lt_of_lt_of_mem_of_isPrime_chartAlgFin_twoChartIntegralModel_x1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOne_finite_and_flat_chartAlgFin_levelRaise_x1
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply"
p2m_attr_erase "simp" "ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero"
p2m_attr_erase "simp" "compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace LevelFiniteFlat

open AlgebraicCurve.TwoChartIntegralModel

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem finite_levelRaise
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (K_M : IntermediateField L (LaurentSeries L))
    [Algebra A ↥K_M] [IsScalarTower A L ↥K_M]
    (j_M : ↥K_M) (hj_M : ((j_M : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j_M ≠ 0)]
    (K_N : IntermediateField L (LaurentSeries L))
    (hK_N : K_N = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * ℓ)))
    [Algebra A ↥K_N] [IsScalarTower A L ↥K_N]
    (j_N : ↥K_N) (hj_N : ((j_N : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j_N ≠ 0)]
    (ι_M : ↥(chartAlgFin A (↥K_M) j_M) →ₐ[A] ↥(chartAlgFin A (↥K_N) j_N))
    (hι_M : ∀ x, (((ι_M x : ↥K_N) : LaurentSeries L)) = ((x : ↥K_M) : LaurentSeries L)) :
    ι_M.toRingHom.Finite := by
  classical
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) hℓ.ne_zero⟩

  have htj : Transcendental A j_N := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K_N A j_N hj_N
  have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j_N} : Set ↥K_N)) ↥K_N :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma1 (M * ℓ)) (by simp [ModularGroup.T]) L K_N hK_N j_N hj_N
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j_N} : Set ↥K_N)) ↥K_N :=
    Algebra.IsAlgebraic.of_finite _ _
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j_N} : Set ↥K_N)) ↥K_N := inferInstance
  have hfin := (finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K_N) j_N htj hFD hsep).1

  have hpin : ι_M (jChartFin A (↥K_M) j_M) = jChartFin A (↥K_N) j_N := by
    apply Subtype.ext
    apply Subtype.ext
    show (((ι_M (jChartFin A (↥K_M) j_M) : ↥K_N) : LaurentSeries L)) = ((jChartFin A (↥K_N) j_N : ↥K_N) : LaurentSeries L)
    rw [hι_M, coe_jChartFin, coe_jChartFin, hj_M, hj_N]

  letI algPN : Algebra (Polynomial A) ↥(chartAlgFin A (↥K_N) j_N) := (polynomialToChartFin A (↥K_N) j_N).toRingHom.toAlgebra
  letI algPM : Algebra (Polynomial A) ↥(chartAlgFin A (↥K_M) j_M) := (polynomialToChartFin A (↥K_M) j_M).toRingHom.toAlgebra
  letI algMN : Algebra ↥(chartAlgFin A (↥K_M) j_M) ↥(chartAlgFin A (↥K_N) j_N) := ι_M.toRingHom.toAlgebra
  have hcomp : (ι_M.comp (polynomialToChartFin A (↥K_M) j_M)) = polynomialToChartFin A (↥K_N) j_N := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, polynomialToChartFin_X, polynomialToChartFin_X, hpin]
  haveI : IsScalarTower (Polynomial A) ↥(chartAlgFin A (↥K_M) j_M) ↥(chartAlgFin A (↥K_N) j_N) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    show polynomialToChartFin A (↥K_N) j_N r = ι_M (polynomialToChartFin A (↥K_M) j_M r)
    rw [← hcomp, AlgHom.comp_apply]
  haveI : Module.Finite (Polynomial A) ↥(chartAlgFin A (↥K_N) j_N) := hfin
  exact Module.Finite.of_restrictScalars_finite (Polynomial A) ↥(chartAlgFin A (↥K_M) j_M) ↥(chartAlgFin A (↥K_N) j_N)

end LevelFiniteFlat

namespace LFFAlg

open IsLocalRing

theorem free_localizedModule_of_dim_two
    {A₀ B₀ : Type*} [CommRing A₀] [CommRing B₀] [IsDomain A₀] [IsDomain B₀] [Algebra A₀ B₀] [Module.Finite A₀ B₀]
    (hinj : Function.Injective (algebraMap A₀ B₀)) (ϖ : A₀)
    (hred : IsReduced (B₀ ⧸ Ideal.span {algebraMap A₀ B₀ ϖ}))
    (hnomax : ∀ P ∈ (Ideal.span {algebraMap A₀ B₀ ϖ}).minimalPrimes, ¬ P.IsMaximal)
    (hchain : ∀ 𝔮 𝔭' m : Ideal A₀, 𝔮.IsPrime → 𝔭'.IsPrime → m.IsPrime → ϖ ∈ 𝔮 → 𝔮 < 𝔭' → ¬ 𝔭' < m)
    (𝔭 : Ideal A₀) [𝔭.IsPrime] [IsNoetherianRing (Localization.AtPrime 𝔭)]
    (hq𝔪 : algebraMap A₀ (Localization.AtPrime 𝔭) ϖ ∈ maximalIdeal (Localization.AtPrime 𝔭))
    (hq0 : algebraMap A₀ (Localization.AtPrime 𝔭) ϖ ≠ 0)
    [IsDomain (Localization.AtPrime 𝔭 ⧸ Ideal.span {algebraMap A₀ (Localization.AtPrime 𝔭) ϖ})]
    [IsDiscreteValuationRing (Localization.AtPrime 𝔭 ⧸ Ideal.span {algebraMap A₀ (Localization.AtPrime 𝔭) ϖ})] :
    Module.Free (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl B₀) := by
  classical
  set A := Localization.AtPrime 𝔭 with hA
  let B := Localization (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl)
  haveI : FaithfulSMul A₀ B₀ := (faithfulSMul_iff_algebraMap_injective A₀ B₀).mpr hinj
  haveI : IsDomain B := inferInstance
  haveI : Module.Finite A B := inferInstance
  haveI : Algebra.IsIntegral A₀ B₀ := inferInstance

  obtain ⟨t, hspan, hAreg⟩ :=
    IsLocalRing.exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient
      (algebraMap A₀ A ϖ) hq𝔪 hq0
  have ht𝔪 : t ∈ maximalIdeal A := by
    rw [← hspan]; exact Ideal.subset_span (by simp)

  have hqB : algebraMap A B (algebraMap A₀ A ϖ) = algebraMap A₀ B ϖ := (IsScalarTower.algebraMap_apply A₀ A B ϖ).symm
  have hqB0 : algebraMap A₀ B ϖ ≠ 0 := by
    intro h
    apply hq0
    have h1 : algebraMap A B (algebraMap A₀ A ϖ) = 0 := by rw [hqB, h]
    exact (FaithfulSMul.algebraMap_injective A B) (by rw [h1, map_zero])
  have ha : IsSMulRegular B (algebraMap A B (algebraMap A₀ A ϖ)) := by
    rw [hqB]; exact fun x y h => mul_left_cancel₀ hqB0 h

  have hmapq : (Ideal.span {algebraMap A₀ B₀ ϖ}).map (algebraMap B₀ B) = Ideal.span {algebraMap A B (algebraMap A₀ A ϖ)} := by
    rw [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply A₀ B₀ B, hqB]
  have hredB : IsReduced (B ⧸ Ideal.span {algebraMap A B (algebraMap A₀ A ϖ)}) := by
    rw [← hmapq]
    haveI := hred
    exact isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (B₀ ⧸ Ideal.span {algebraMap A₀ B₀ ϖ})
      (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl)) _ hred

  have h𝔭max : 𝔭.IsMaximal := by
    have hprime : (Ideal.span {algebraMap A₀ A ϖ}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
    set 𝔮 : Ideal A₀ := (Ideal.span {algebraMap A₀ A ϖ}).under A₀ with h𝔮
    have h𝔮p : 𝔮.IsPrime := Ideal.IsPrime.under _ _
    have hq𝔮 : ϖ ∈ 𝔮 := by
      rw [h𝔮, Ideal.under, Ideal.mem_comap]; exact Ideal.subset_span rfl
    have h𝔭eq : (maximalIdeal A).under A₀ = 𝔭 := IsLocalization.AtPrime.under_maximalIdeal A 𝔭
    have h𝔮le : 𝔮 ≤ 𝔭 := by
      rw [← h𝔭eq]; exact Ideal.comap_mono ((Ideal.span_singleton_le_iff_mem _).mpr hq𝔪)
    have h𝔮ne : 𝔮 ≠ 𝔭 := by
      intro he
      have h1 : Ideal.span {algebraMap A₀ A ϖ} = maximalIdeal A := by
        rw [← IsLocalization.map_under 𝔭.primeCompl A (Ideal.span {algebraMap A₀ A ϖ}), ← h𝔮, he]
        exact Localization.AtPrime.map_eq_maximalIdeal
      have hF : IsField (A ⧸ Ideal.span {algebraMap A₀ A ϖ}) := by
        rw [h1]; exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
      exact IsDiscreteValuationRing.not_isField _ hF
    by_contra hnm
    obtain ⟨m, hm, h𝔭m⟩ := Ideal.exists_le_maximal 𝔭 (Ideal.IsPrime.ne_top inferInstance)
    have hne : 𝔭 ≠ m := fun he => hnm (he ▸ hm)
    exact hchain 𝔮 𝔭 m h𝔮p inferInstance hm.isPrime hq𝔮 (lt_of_le_of_ne h𝔮le h𝔮ne) (lt_of_le_of_ne h𝔭m hne)

  have hb : ∀ P ∈ minimalPrimes (B ⧸ Ideal.span {algebraMap A B (algebraMap A₀ A ϖ)}),
      Ideal.Quotient.mk (Ideal.span {algebraMap A B (algebraMap A₀ A ϖ)}) (algebraMap A B t) ∉ P := by
    intro P hP htP

    set P' : Ideal B := P.comap (Ideal.Quotient.mk _) with hP'
    have hP'min : P' ∈ (Ideal.span {algebraMap A B (algebraMap A₀ A ϖ)}).minimalPrimes := by
      rw [Ideal.minimalPrimes_eq_comap]; exact ⟨P, hP, rfl⟩
    haveI hP'p : P'.IsPrime := hP'min.1.1
    have hqP' : algebraMap A B (algebraMap A₀ A ϖ) ∈ P' := hP'min.1.2 (Ideal.subset_span rfl)
    have htP' : algebraMap A B t ∈ P' := htP

    have hPA : P'.comap (algebraMap A B) = maximalIdeal A := by
      refine ((IsLocalRing.maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
      rw [← hspan, Ideal.ofList, Ideal.span_le]
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hx
      rcases hx with rfl | rfl
      · exact hqP'
      · exact htP'

    set P₀ : Ideal B₀ := P'.comap (algebraMap B₀ B) with hP₀
    haveI : P₀.IsPrime := Ideal.IsPrime.comap _
    have hP₀A : P₀.comap (algebraMap A₀ B₀) = 𝔭 := by
      rw [hP₀, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A₀ A B,
        ← Ideal.comap_comap, hPA]
      exact IsLocalization.AtPrime.under_maximalIdeal A 𝔭
    have hP₀min : P₀ ∈ (Ideal.span {algebraMap A₀ B₀ ϖ}).minimalPrimes := by
      have h := IsLocalization.minimalPrimes_map (Algebra.algebraMapSubmonoid B₀ 𝔭.primeCompl) B (Ideal.span {algebraMap A₀ B₀ ϖ})
      rw [hmapq] at h
      have : P' ∈ Ideal.under B₀ ⁻¹' (Ideal.span {algebraMap A₀ B₀ ϖ}).minimalPrimes := h ▸ hP'min
      exact this
    have hP₀max : P₀.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P₀ (hP₀A ▸ h𝔭max)
    exact hnomax P₀ hP₀min hP₀max

  haveI : Nontrivial B := inferInstance
  have hreg : RingTheory.Sequence.IsRegular B [algebraMap A₀ A ϖ, t] :=
    RingTheory.Sequence.isRegular_pair_of_isSMulRegular_of_isReduced_of_forall_notMem_minimalPrimes
      (algebraMap A₀ A ϖ) t hq𝔪 ht𝔪 ha hredB hb
  have hfreeB : Module.Free A B :=
    Module.free_of_isRegular_of_span_eq_maximalIdeal [algebraMap A₀ A ϖ, t] hAreg hspan B hreg

  have hloc : IsLocalizedModule 𝔭.primeCompl (IsScalarTower.toAlgHom A₀ B₀ B).toLinearMap :=
    (isLocalizedModule_iff_isLocalization).mpr inferInstance
  let e₀ : LocalizedModule 𝔭.primeCompl B₀ ≃ₗ[A₀] B :=
    IsLocalizedModule.iso 𝔭.primeCompl (IsScalarTower.toAlgHom A₀ B₀ B).toLinearMap
  let e : LocalizedModule 𝔭.primeCompl B₀ ≃ₗ[A] B := LinearEquiv.extendScalarsOfIsLocalization 𝔭.primeCompl A e₀
  exact Module.Free.of_equiv e.symm

end LFFAlg

namespace Leaf

open AlgebraicCurve.TwoChartIntegralModel

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem isReduced_quotient_and_not_isMaximal_of_mem_minimalPrimes
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hN : 5 ≤ N) (hpN : ¬ p ∣ N)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L] (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (K_N : IntermediateField L (LaurentSeries L))
    (hK_N : K_N = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N))
    [Algebra A ↥K_N] [IsScalarTower A L ↥K_N]
    (j_N : ↥K_N) (hj_N : ((j_N : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j_N ≠ 0)] :
    IsReduced (↥(chartAlgFin A (↥K_N) j_N) ⧸ Ideal.span {algebraMap A ↥(chartAlgFin A (↥K_N) j_N) ϖ}) ∧
    ∀ P ∈ (Ideal.span {algebraMap A ↥(chartAlgFin A (↥K_N) j_N) ϖ}).minimalPrimes, ¬ P.IsMaximal := by
  obtain ⟨hprime, hnm⟩ := ModularCurve.XOne.isDomain_quotient_span_and_not_isMaximal_chartAlgFin_twoChartIntegralModel_x1
    p N hN hpN L ζ hζ K_N hK_N A hAp hζA j_N hj_N ϖ hϖ
  haveI := hprime
  haveI : IsDomain (↥(chartAlgFin A (↥K_N) j_N) ⧸ Ideal.span {algebraMap A ↥(chartAlgFin A (↥K_N) j_N) ϖ}) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hprime
  refine ⟨inferInstance, fun P hP => ?_⟩
  rw [Ideal.minimalPrimes_eq_subsingleton_self] at hP
  rw [Set.mem_singleton_iff.mp hP]
  exact hnm

end Leaf

namespace LevelFiniteFlat

theorem flat_of_leaves
    {A : Type*} [CommRing A] {A₀ B₀ : Type*} [CommRing A₀] [CommRing B₀] [IsDomain A₀] [IsDomain B₀]
    [Algebra A A₀] [Algebra A B₀] [Algebra A₀ B₀] [IsScalarTower A A₀ B₀] [Module.Finite A₀ B₀] [IsNoetherianRing A₀]
    (hinj : Function.Injective (algebraMap A₀ B₀)) (ϖ : A) (hϖA₀ : algebraMap A A₀ ϖ ≠ 0)
    (hcruxa : ∀ (𝔪 : Ideal A₀) [𝔪.IsMaximal], algebraMap A A₀ ϖ ∈ 𝔪 →
      ∃ _ : IsDomain (Localization.AtPrime 𝔪 ⧸ Ideal.span {algebraMap A₀ (Localization.AtPrime 𝔪) (algebraMap A A₀ ϖ)}),
        IsDiscreteValuationRing
          (Localization.AtPrime 𝔪 ⧸ Ideal.span {algebraMap A₀ (Localization.AtPrime 𝔪) (algebraMap A A₀ ϖ)}))
    (hcruxb : ∀ (𝔪 : Ideal A₀) [𝔪.IsMaximal], algebraMap A A₀ ϖ ∉ 𝔪 → IsPrincipalIdealRing (Localization.AtPrime 𝔪))
    (hchain : ∀ 𝔮 𝔭' m : Ideal A₀, 𝔮.IsPrime → 𝔭'.IsPrime → m.IsPrime →
      algebraMap A A₀ ϖ ∈ 𝔮 → 𝔮 < 𝔭' → ¬ 𝔭' < m)
    (hred : IsReduced (B₀ ⧸ Ideal.span {algebraMap A B₀ ϖ}))
    (hnomax : ∀ P ∈ (Ideal.span {algebraMap A B₀ ϖ}).minimalPrimes, ¬ P.IsMaximal) :
    Module.Flat A₀ B₀ := by
  classical
  have hϖB : algebraMap A₀ B₀ (algebraMap A A₀ ϖ) = algebraMap A B₀ ϖ := (IsScalarTower.algebraMap_apply A A₀ B₀ ϖ).symm
  rw [← hϖB] at hred hnomax
  haveI : FaithfulSMul A₀ B₀ := (faithfulSMul_iff_algebraMap_injective A₀ B₀).mpr hinj
  apply Module.flat_of_localized_maximal
  intro 𝔪 h𝔪
  haveI hfree : Module.Free (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl B₀) := by
    by_cases hϖ𝔪 : algebraMap A A₀ ϖ ∈ 𝔪
    · obtain ⟨hdom, hdvr⟩ := hcruxa 𝔪 hϖ𝔪
      haveI := hdom
      haveI := hdvr
      have hq𝔪 : algebraMap A₀ (Localization.AtPrime 𝔪) (algebraMap A A₀ ϖ) ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪) :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 _).mpr hϖ𝔪
      have hq0 : algebraMap A₀ (Localization.AtPrime 𝔪) (algebraMap A A₀ ϖ) ≠ 0 := fun h =>
        hϖA₀ (IsLocalization.injective (Localization.AtPrime 𝔪) 𝔪.primeCompl_le_nonZeroDivisors (by rw [h, map_zero]))
      exact LFFAlg.free_localizedModule_of_dim_two hinj (algebraMap A A₀ ϖ) hred hnomax hchain 𝔪 hq𝔪 hq0
    · haveI hpid := hcruxb 𝔪 hϖ𝔪
      let Bₘ := Localization (Algebra.algebraMapSubmonoid B₀ 𝔪.primeCompl)
      haveI : IsDomain Bₘ := inferInstance
      haveI : Module.Finite (Localization.AtPrime 𝔪) Bₘ := inferInstance
      haveI : Module.IsTorsionFree (Localization.AtPrime 𝔪) Bₘ :=
        (Module.isTorsionFree_iff_algebraMap_injective (R := Localization.AtPrime 𝔪) (A := Bₘ)).mpr
          (FaithfulSMul.algebraMap_injective (Localization.AtPrime 𝔪) Bₘ)
      haveI : Module.Free (Localization.AtPrime 𝔪) Bₘ := Module.free_of_finite_type_torsion_free'
      have hloc : IsLocalizedModule 𝔪.primeCompl (IsScalarTower.toAlgHom A₀ B₀ Bₘ).toLinearMap :=
        (isLocalizedModule_iff_isLocalization).mpr inferInstance
      let e₀ : LocalizedModule 𝔪.primeCompl B₀ ≃ₗ[A₀] Bₘ :=
        IsLocalizedModule.iso 𝔪.primeCompl (IsScalarTower.toAlgHom A₀ B₀ Bₘ).toLinearMap
      let e : LocalizedModule 𝔪.primeCompl B₀ ≃ₗ[Localization.AtPrime 𝔪] Bₘ :=
        LinearEquiv.extendScalarsOfIsLocalization 𝔪.primeCompl (Localization.AtPrime 𝔪) e₀
      exact Module.Free.of_equiv e.symm
  exact Module.Flat.trans A₀ (Localization.AtPrime 𝔪) (LocalizedModule 𝔪.primeCompl B₀)

end LevelFiniteFlat

open LevelFiniteFlat in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
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
    (hι_M : ∀ x, (((ι_M x : ↥K_N) : LaurentSeries L)) = ((x : ↥K_M) : LaurentSeries L)) :
    ι_M.toRingHom.Finite ∧ ι_M.toRingHom.Flat := by
  refine ⟨?_, ?_⟩
  · exact finite_levelRaise p M L A ℓ hℓ K_M j_M hj_M K_N hK_N j_N hj_N ι_M hι_M
  ·
    classical
    haveI hfin : ι_M.toRingHom.Finite := finite_levelRaise p M L A ℓ hℓ K_M j_M hj_M K_N hK_N j_N hj_N ι_M hι_M
    letI algMN : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)
        ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) := ι_M.toRingHom.toAlgebra
    haveI : Module.Finite ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)
        ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) := hfin
    show Module.Flat _ _
    have halg : ∀ x, algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)
        ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) x = ι_M x := fun _ => rfl
    haveI : IsScalarTower A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)
        ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) :=
      IsScalarTower.of_algebraMap_eq fun a => by rw [halg, ι_M.commutes]
    have hinj : Function.Injective (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M)
        ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) := by
      intro x y h
      rw [halg, halg] at h
      have h' := congrArg (fun z : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) =>
        (((z : ↥K_N) : LaurentSeries L))) h
      simp only [hι_M] at h'
      exact Subtype.ext (Subtype.ext h')
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
    have hϖspan : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
    have hϖA₀ : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ϖ ≠ 0 := by
      intro h
      have h' : algebraMap A (↥K_M) ϖ = 0 := congrArg (fun z : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) => (z : ↥K_M)) h
      rw [IsScalarTower.algebraMap_apply A L ↥K_M, map_eq_zero, map_eq_zero_iff _ (IsFractionRing.injective A L)] at h'
      exact hϖ.ne_zero h'

    haveI : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) := by
      have htj : Transcendental A j_M := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K_M A j_M hj_M
      have hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j_M} : Set ↥K_M)) ↥K_M :=
        ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
          (CongruenceSubgroup.Gamma1 M) (by simp [ModularGroup.T]) L K_M hK_M j_M hj_M
      haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j_M} : Set ↥K_M)) ↥K_M :=
        Algebra.IsAlgebraic.of_finite _ _
      have hfinM := (AlgebraicCurve.TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K_M) j_M htj hFD
        inferInstance).1
      letI algPM : Algebra (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) :=
        (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin A (↥K_M) j_M).toRingHom.toAlgebra
      haveI : Module.Finite (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) := hfinM
      exact Algebra.FiniteType.isNoetherianRing (Polynomial A) _
    have hℓp : ℓ ≠ p := by
      rintro rfl
      exact hℓMp (dvd_mul_left ℓ M)
    have hN5 : 5 ≤ M * ℓ := le_trans hM (Nat.le_mul_of_pos_right M hℓ.pos)
    have hpN : ¬ p ∣ M * ℓ := by
      intro h
      rcases (Nat.Prime.dvd_mul (Fact.out)).mp h with h1 | h2
      · exact hpM h1
      · exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hℓ).mp h2).symm
    haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) hℓ.ne_zero⟩
    obtain ⟨hred, hnomax⟩ := Leaf.isReduced_quotient_and_not_isMaximal_of_mem_minimalPrimes p (M * ℓ) hN5 hpN L ζ hζ A
      hAp hζA ϖ hϖspan K_N hK_N j_N hj_N
    exact flat_of_leaves hinj ϖ hϖA₀
      (fun 𝔪 _ h =>
        ModularCurve.XOne.exists_isDomain_isDiscreteValuationRing_localization_quotient_span_chartAlgFin_twoChartIntegralModel_x1
          p M hM hpM L ζ hζ A hAp hζA ϖ hϖspan K_M hK_M j_M hj_M 𝔪 h)
      (fun 𝔪 _ h =>
        ModularCurve.XOne.isPrincipalIdealRing_localization_atPrime_chartAlgFin_of_not_mem_twoChartIntegralModel_x1
          p M L A ϖ hϖ K_M hK_M j_M hj_M 𝔪 h)
      (ModularCurve.XOne.not_lt_of_lt_of_mem_of_isPrime_chartAlgFin_twoChartIntegralModel_x1 p M L A ϖ hϖ K_M hK_M j_M hj_M)
      hred hnomax

end S_ModularCurve_XOne_finite_and_flat_chartAlgFin_levelRaise_x1
end P2MW
export P2MW.S_ModularCurve_XOne_finite_and_flat_chartAlgFin_levelRaise_x1 (solution)
