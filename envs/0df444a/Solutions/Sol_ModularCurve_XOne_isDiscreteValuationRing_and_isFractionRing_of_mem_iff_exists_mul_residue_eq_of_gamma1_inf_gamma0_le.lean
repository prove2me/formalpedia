-- Prove2me | solution 1 for ModularCurve.XOne.isDiscreteValuationRing_and_isFractionRing_of_mem_iff_exists_mul_residue_eq_of_gamma1_inf_gamma0_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/11ac12a0-c4d8-54a5-88f3-e2ceb444fcee

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_XOne_isDiscreteValuationRing_and_isFractionRing_of_mem_iff_exists_mul_residue_eq_x1
import Theorems.Thm_Subring_eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed
import Theorems.Thm_ModularCurve_XOneGammaZeroP_gaussReduction_mem_x1FunctionFieldC_of_x1x0
import Theorems.Thm_ModularCurve_coeffEmb_jq_mem_laurentBaseChange_x1FunctionField
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOne_isDiscreteValuationRing_and_isFractionRing_of_mem_iff_exists_mul_residue_eq_of_gamma1_inf_gamma0_le
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.qExpandAlgHomC_apply"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply"
p2m_attr_erase "simp" "ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero"
p2m_attr_erase "simp" "compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply"
p2m_attr_erase "simp" "ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 16000000

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel
open CongruenceSubgroup ModularCurve
open scoped MatrixGroups

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

theorem exists_ratio_presentation
    (Γ : Subgroup SL(2, ℤ))
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = laurentBaseChange L (qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    {k : ℤ} (f g : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
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
  have hmem : intSeriesC ℚ pf / intSeriesC ℚ pg ∈ qExpFunctionFieldC ℚ Γ :=
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

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓle : Γ ≤ CongruenceSubgroup.Gamma1 M)
    (hΓge : CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p ≤ Γ)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K₁)
    (hW₀ : ∀ f : ↥K₁, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hSW₀ : ∀ s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∈ W₀)

    (y : ↥(XFin A (↥K₁) j))
    (hyϖ : algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ ∈ y.asIdeal)
    (hy𝔓 : ∀ s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∈ W₀.nonunits → s ∈ y.asIdeal)
    (hy₀ : ∃ s : ↥(chartAlgFin A (↥K₁) j), s ∈ y.asIdeal ∧ (s : ↥K₁) ∉ W₀.nonunits)

    (R : Subring (IsLocalRing.ResidueField ↥W₀))
    (hR : ∀ e : IsLocalRing.ResidueField ↥W₀, e ∈ R ↔
      ∃ s t : ↥(chartAlgFin A (↥K₁) j), t ∉ y.asIdeal ∧
        e * IsLocalRing.residue ↥W₀ ⟨(t : ↥K₁), hSW₀ t⟩ = IsLocalRing.residue ↥W₀ ⟨(s : ↥K₁), hSW₀ s⟩) :
    IsDiscreteValuationRing ↥R ∧ IsFractionRing ↥R (IsLocalRing.ResidueField ↥W₀) := by
  classical
  haveI hp : Fact p.Prime := inferInstance

  obtain ⟨W₀', hW₀', hW₀A, hW₀m, -, hW₀nu⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC Γ L K₁ hK₁ A j hj
  have hWW : W₀ = W₀' := by ext f; rw [hW₀ f, hW₀' f]
  subst hWW
  clear hW₀'

  obtain ⟨KM, hKMdef⟩ : ∃ KM : IntermediateField L (LaurentSeries L),
      KM = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M) := ⟨_, rfl⟩
  have hKMK₁ : KM ≤ K₁ := by
    rw [hK₁, hKMdef]
    exact (IntermediateField.adjoin.mono L _ _ (Set.image_mono (qExpFunctionFieldC_mono ℚ hΓle)) :
      laurentBaseChange L (qExpFunctionFieldC ℚ (Gamma1 M)) ≤ laurentBaseChange L (qExpFunctionFieldC ℚ Γ))
  obtain ⟨Kfl, hKfldef⟩ : ∃ Kfl : IntermediateField L (LaurentSeries L),
      Kfl = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p) := ⟨_, rfl⟩
  have hK₁Kfl : K₁ ≤ Kfl := by
    rw [hK₁, hKfldef]
    exact (IntermediateField.adjoin.mono L _ _ (Set.image_mono (qExpFunctionFieldC_mono ℚ hΓge)) :
      laurentBaseChange L (qExpFunctionFieldC ℚ Γ) ≤ laurentBaseChange L (qExpFunctionFieldC ℚ (Gamma1 M ⊓ Gamma0 p)))
  letI instAKM : Algebra A ↥KM := ((algebraMap L ↥KM).comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L ↥KM := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI instAKfl : Algebra A ↥Kfl := ((algebraMap L ↥Kfl).comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L ↥Kfl := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let ι : ↥KM →ₐ[L] ↥K₁ := IntermediateField.inclusion hKMK₁
  let ι' : ↥K₁ →ₐ[L] ↥Kfl := IntermediateField.inclusion hK₁Kfl
  have hιcoe : ∀ x : ↥KM, ((ι x : ↥K₁) : LaurentSeries L) = (x : LaurentSeries L) := fun _ => rfl
  have hιinj : Function.Injective ι := ι.toRingHom.injective
  have hι'coe : ∀ x : ↥K₁, ((ι' x : ↥Kfl) : LaurentSeries L) = (x : LaurentSeries L) := fun _ => rfl

  have hjKM : (j : LaurentSeries L) ∈ KM := by
    rw [hKMdef, hj]; exact ModularCurve.coeffEmb_jq_mem_laurentBaseChange_x1FunctionField L M
  let jM : ↥KM := ⟨(j : LaurentSeries L), hjKM⟩
  have hιjM : ι jM = j := Subtype.ext rfl
  have hjM : ((jM : ↥KM) : LaurentSeries L) = ModularCurve.coeffEmb L ModularCurve.jq := hj
  haveI : Fact (jM ≠ 0) := ⟨fun h => (Fact.out : j ≠ 0) (by rw [← hιjM, h, map_zero])⟩

  let W₀M : ValuationSubring ↥KM := W₀.comap ι.toRingHom
  have hmemW₀M : ∀ f : ↥KM, f ∈ W₀M ↔ ι f ∈ W₀ := fun _ => ValuationSubring.mem_comap
  have hW₀M : ∀ f : ↥KM, f ∈ W₀M ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) := by
    intro f; rw [hmemW₀M, hW₀ (ι f), hιcoe]

  let ιA : ↥KM →ₐ[A] ↥K₁ := ι.restrictScalars A
  have hadjmap : (Algebra.adjoin A ({jM} : Set ↥KM)).map ιA = Algebra.adjoin A ({j} : Set ↥K₁) := by
    rw [AlgHom.map_adjoin_singleton, show ιA jM = j from Subtype.ext rfl]
  have hadj : ∀ x : ↥KM, x ∈ Algebra.adjoin A ({jM} : Set ↥KM) →
      ιA x ∈ Algebra.adjoin A ({j} : Set ↥K₁) :=
    fun x hx => hadjmap ▸ Subalgebra.mem_map.mpr ⟨x, hx, rfl⟩
  let φ₀ : ↥(Algebra.adjoin A ({jM} : Set ↥KM)) →+* ↥(Algebra.adjoin A ({j} : Set ↥K₁)) :=
    (ιA.toRingHom.comp (Algebra.adjoin A ({jM} : Set ↥KM)).val.toRingHom).codRestrict
      (Algebra.adjoin A ({j} : Set ↥K₁)) (fun x => hadj x x.2)
  have hφ₀coe : ∀ x, ((φ₀ x : ↥(Algebra.adjoin A ({j} : Set ↥K₁))) : ↥K₁) = ι (x : ↥KM) := fun _ => rfl
  have hφ₀surj : Function.Surjective φ₀ := by
    intro c
    obtain ⟨x, hx, hxc⟩ := Subalgebra.mem_map.mp (hadjmap.symm ▸ c.2 : (c : ↥K₁) ∈ (Algebra.adjoin A ({jM} : Set ↥KM)).map ιA)
    exact ⟨⟨x, hx⟩, Subtype.ext hxc⟩
  have hθmem : ∀ s : ↥(chartAlgFin A (↥KM) jM), (ι (s : ↥KM) : ↥K₁) ∈ chartAlgFin A (↥K₁) j := by
    intro s
    change IsIntegral (Algebra.adjoin A ({j} : Set ↥K₁)) (ιA (s : ↥KM))
    exact (s.2 : IsIntegral (Algebra.adjoin A ({jM} : Set ↥KM)) (s : ↥KM)).map_of_comp_eq φ₀ ιA.toRingHom
      (RingHom.ext fun x => rfl)
  let θ : ↥(chartAlgFin A (↥KM) jM) →+* ↥(chartAlgFin A (↥K₁) j) :=
    { toFun := fun s => ⟨ι (s : ↥KM), hθmem s⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hθcoe : ∀ s, ((θ s : ↥(chartAlgFin A (↥K₁) j)) : ↥K₁) = ι (s : ↥KM) := fun _ => rfl
  have hSW₀M : ∀ s : ↥(chartAlgFin A (↥KM) jM), (s : ↥KM) ∈ W₀M :=
    fun s => (hmemW₀M _).mpr (hSW₀ (θ s))

  have hθint : ∀ s : ↥(chartAlgFin A (↥K₁) j), θ.IsIntegralElem s := by
    intro s

    let incl' : ↥(Algebra.adjoin A ({jM} : Set ↥KM)) →+* ↥(chartAlgFin A (↥KM) jM) :=
      (Subalgebra.inclusion (adjoin_le_chartAlg A (↥KM) ({jM} : Set ↥KM))).toRingHom
    let e₀ := RingEquiv.ofBijective φ₀ ⟨fun a b h => Subtype.ext (hιinj (by
        have := congrArg (fun c : ↥(Algebra.adjoin A ({j} : Set ↥K₁)) => (c : ↥K₁)) h
        simpa [hφ₀coe] using this)), hφ₀surj⟩
    let g : ↥(Algebra.adjoin A ({j} : Set ↥K₁)) →+* ↥(chartAlgFin A (↥KM) jM) :=
      incl'.comp e₀.symm.toRingHom
    letI algMK : Algebra ↥(chartAlgFin A (↥KM) jM) ↥K₁ :=
      ((chartAlgFin A (↥K₁) j).val.toRingHom.comp θ).toAlgebra
    have hcomp : (algebraMap ↥(chartAlgFin A (↥KM) jM) ↥K₁).comp g =
        (RingHom.id ↥K₁).comp (algebraMap ↥(Algebra.adjoin A ({j} : Set ↥K₁)) ↥K₁) := by
      refine RingHom.ext fun c => ?_
      show ((θ (g c) : ↥(chartAlgFin A (↥K₁) j)) : ↥K₁) = (c : ↥K₁)
      rw [hθcoe]
      show ι ((e₀.symm c : ↥(Algebra.adjoin A ({jM} : Set ↥KM))) : ↥KM) = (c : ↥K₁)
      rw [← hφ₀coe, show φ₀ (e₀.symm c) = e₀ (e₀.symm c) from rfl, RingEquiv.apply_symm_apply]
    have hK : IsIntegral ↥(chartAlgFin A (↥KM) jM) ((s : ↥(chartAlgFin A (↥K₁) j)) : ↥K₁) :=
      (s.2 : IsIntegral (Algebra.adjoin A ({j} : Set ↥K₁)) (s : ↥K₁)).map_of_comp_eq g (RingHom.id ↥K₁) hcomp
    letI algM1 : Algebra ↥(chartAlgFin A (↥KM) jM) ↥(chartAlgFin A (↥K₁) j) := θ.toAlgebra
    let f : ↥(chartAlgFin A (↥K₁) j) →ₐ[↥(chartAlgFin A (↥KM) jM)] ↥K₁ :=
      { (chartAlgFin A (↥K₁) j).val.toRingHom with commutes' := fun _ => rfl }
    exact (isIntegral_algHom_iff f Subtype.val_injective).mp hK

  let yM : ↥(XFin A (↥KM) jM) := ⟨y.asIdeal.comap θ, Ideal.comap_isPrime θ y.asIdeal⟩
  have hyMmem : ∀ s, s ∈ yM.asIdeal ↔ θ s ∈ y.asIdeal := fun _ => Ideal.mem_comap
  have hθϖ : θ (algebraMap A ↥(chartAlgFin A (↥KM) jM) ϖ) = algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ := by
    apply Subtype.ext
    rw [hθcoe, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply A L ↥K₁ ϖ]
    exact ι.commutes (algebraMap A L ϖ)
  have hyϖM : algebraMap A ↥(chartAlgFin A (↥KM) jM) ϖ ∈ yM.asIdeal := by
    rw [hyMmem, hθϖ]; exact hyϖ
  have hnuM : ∀ f : ↥KM, f ∈ W₀M.nonunits ↔ ι f ∈ W₀.nonunits := by
    intro f
    rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
      map_eq_zero_iff ι hιinj, ← map_inv₀, hmemW₀M]
  have hy𝔓M : ∀ s : ↥(chartAlgFin A (↥KM) jM), (s : ↥KM) ∈ W₀M.nonunits → s ∈ yM.asIdeal := by
    intro s hs
    rw [hyMmem]
    exact hy𝔓 (θ s) ((hnuM _).mp hs)

  let ιW : ↥W₀M →+* ↥W₀ :=
    (ι.toRingHom.comp W₀M.subtype).codRestrict W₀.toSubring (fun w => (hmemW₀M w.1).mp w.2)
  have hιWcoe : ∀ w : ↥W₀M, ((ιW w : ↥W₀) : ↥K₁) = ι (w : ↥KM) := fun _ => rfl
  haveI : IsLocalHom ιW := by
    refine ⟨fun w hw => ?_⟩
    by_contra h
    have h1 : w ∈ IsLocalRing.maximalIdeal ↥W₀M := (IsLocalRing.mem_maximalIdeal w).mpr (mem_nonunits_iff.mpr h)
    have h2 : ((w : ↥KM)) ∈ W₀M.nonunits := ValuationSubring.coe_mem_nonunits_iff.mpr h1
    have h3 : ((ιW w : ↥W₀) : ↥K₁) ∈ W₀.nonunits := by rw [hιWcoe]; exact (hnuM _).mp h2
    have h4 : ιW w ∈ IsLocalRing.maximalIdeal ↥W₀ := ValuationSubring.coe_mem_nonunits_iff.mp h3
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h4) hw
  let φ : IsLocalRing.ResidueField ↥W₀M →+* IsLocalRing.ResidueField ↥W₀ := IsLocalRing.ResidueField.map ιW
  have hφres : ∀ w : ↥W₀M, φ (IsLocalRing.residue ↥W₀M w) = IsLocalRing.residue ↥W₀ (ιW w) := fun _ => rfl
  have hφsurj : Function.Surjective φ := by

    obtain ⟨red, hred, hker⟩ :=
      ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
        L K₁ A W₀ hW₀ hW₀nu

    have hW₀MA : ∀ a : A, algebraMap A ↥KM a ∈ W₀M := by
      intro a
      rw [hmemW₀M]
      have h : ι (algebraMap A ↥KM a) = algebraMap A ↥K₁ a := by
        rw [IsScalarTower.algebraMap_apply A L ↥K₁ a]; exact ι.commutes (algebraMap A L a)
      rw [h]; exact hW₀A a
    have hW₀Mnu : ∀ (f : ↥KM) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (f ∈ W₀M.nonunits ↔ x.map (IsLocalRing.residue A) = 0) := by
      intro f x y hy hxy
      rw [hnuM]
      exact hW₀nu (ι f) x y hy hxy
    obtain ⟨red', R₀M, hred', hker', -, hR₀Mrng, hR₀M⟩ :=
      S1cAux.exists_red_and_reductionField L KM A W₀M hW₀M hW₀MA hW₀Mnu

    have hredι : ∀ w : ↥W₀M, red (ιW w) = red' w := by
      intro w
      obtain ⟨x, y, hy, hxy⟩ := (hW₀M (w : ↥KM)).mp w.2
      rw [hred' w x y hy hxy]
      exact hred (ιW w) x y hy hxy

    have hleR₀M : x1FunctionFieldC (IsLocalRing.ResidueField A) M ≤ R₀M := by
      rw [x1FunctionFieldC, qExpFunctionFieldC, IntermediateField.adjoin_le_iff]
      rintro _ ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
      obtain ⟨F, hy, hpres, hredF⟩ :=
        S1cAux.exists_ratio_presentation (Gamma1 M) L KM hKMdef A f g pf pg hf hg hg0
      exact (hR₀M _).mpr ⟨F, _, _, hy, hpres, hredF⟩

    have hredmem : ∀ w : ↥W₀, red w ∈ x1FunctionFieldC (IsLocalRing.ResidueField A) M := by
      intro w
      obtain ⟨x, y, hy, hxy⟩ := (hW₀ (w : ↥K₁)).mp w.2
      rw [hred w x y hy hxy]
      exact ModularCurve.XOneGammaZeroP.gaussReduction_mem_x1FunctionFieldC_of_x1x0 p M hM hpM L ζ hζ Kfl hKfldef
        A hAp hζA (ι' (w : ↥K₁)) x y hy hxy

    intro e
    obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective e
    obtain ⟨w', hw'⟩ := (hR₀Mrng _).mp (hleR₀M (hredmem w))
    refine ⟨IsLocalRing.residue ↥W₀M w', ?_⟩
    rw [hφres, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← hker, RingHom.mem_ker, map_sub,
      hredι, hw', sub_self]

  let incl : ↥(chartAlgFin A (↥K₁) j) →+* ↥W₀ :=
    ((chartAlgFin A (↥K₁) j).val.toRingHom).codRestrict W₀.toSubring hSW₀
  have hinclcoe : ∀ s, ((incl s : ↥W₀) : ↥K₁) = (s : ↥K₁) := fun _ => rfl
  let ρ : ↥(chartAlgFin A (↥K₁) j) →+* IsLocalRing.ResidueField ↥W₀ := (IsLocalRing.residue ↥W₀).comp incl
  have hρ : ∀ s, ρ s = IsLocalRing.residue ↥W₀ ⟨(s : ↥K₁), hSW₀ s⟩ := fun _ => rfl
  let inclM : ↥(chartAlgFin A (↥KM) jM) →+* ↥W₀M :=
    ((chartAlgFin A (↥KM) jM).val.toRingHom).codRestrict W₀M.toSubring hSW₀M
  let ρM : ↥(chartAlgFin A (↥KM) jM) →+* IsLocalRing.ResidueField ↥W₀M := (IsLocalRing.residue ↥W₀M).comp inclM
  have hρM : ∀ s, ρM s = IsLocalRing.residue ↥W₀M ⟨(s : ↥KM), hSW₀M s⟩ := fun _ => rfl
  have hρθ : ∀ s, ρ (θ s) = φ (ρM s) := fun _ => rfl
  let BM : Subring (IsLocalRing.ResidueField ↥W₀M) := ρM.range
  let Bfl : Subring (IsLocalRing.ResidueField ↥W₀) := BM.map φ
  let B : Subring (IsLocalRing.ResidueField ↥W₀) := ρ.range
  have hBflB : Bfl ≤ B := by
    rintro _ ⟨b, ⟨s, rfl⟩, rfl⟩
    exact ⟨θ s, hρθ s⟩

  have hRMex : ∀ 𝔮 : ↥(XFin A (↥KM) jM), ∃ RM : Subring (IsLocalRing.ResidueField ↥W₀M),
      ∀ e : IsLocalRing.ResidueField ↥W₀M, e ∈ RM ↔ ∃ s t : ↥(chartAlgFin A (↥KM) jM), t ∉ 𝔮.asIdeal ∧
        e * IsLocalRing.residue ↥W₀M ⟨(t : ↥KM), hSW₀M t⟩ = IsLocalRing.residue ↥W₀M ⟨(s : ↥KM), hSW₀M s⟩ := by
    intro 𝔮
    haveI := 𝔮.2
    refine ⟨{ carrier := {e | ∃ s t : ↥(chartAlgFin A (↥KM) jM), t ∉ 𝔮.asIdeal ∧ e * ρM t = ρM s}
              mul_mem' := ?_, one_mem' := ?_, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ },
      fun e => Iff.rfl⟩
    · rintro a b ⟨s₁, t₁, ht₁, h₁⟩ ⟨s₂, t₂, ht₂, h₂⟩
      refine ⟨s₁ * s₂, t₁ * t₂, fun h => (𝔮.2.mem_or_mem h).elim ht₁ ht₂, ?_⟩
      rw [map_mul, map_mul]
      linear_combination (b * ρM t₂) * h₁ + (ρM s₁) * h₂
    · exact ⟨1, 1, fun h => 𝔮.2.ne_top ((Ideal.eq_top_iff_one _).mpr h), by rw [map_one, mul_one]⟩
    · rintro a b ⟨s₁, t₁, ht₁, h₁⟩ ⟨s₂, t₂, ht₂, h₂⟩
      refine ⟨s₁ * t₂ + s₂ * t₁, t₁ * t₂, fun h => (𝔮.2.mem_or_mem h).elim ht₁ ht₂, ?_⟩
      rw [map_mul, map_add, map_mul, map_mul]
      linear_combination (ρM t₂) * h₁ + (ρM t₁) * h₂
    · exact ⟨0, 1, fun h => 𝔮.2.ne_top ((Ideal.eq_top_iff_one _).mpr h), by rw [map_zero, zero_mul]⟩
    · rintro a ⟨s, t, ht, h⟩
      exact ⟨-s, t, ht, by rw [map_neg, neg_mul, h]⟩
  have hREG : ∀ 𝔮 : ↥(XFin A (↥KM) jM), algebraMap A ↥(chartAlgFin A (↥KM) jM) ϖ ∈ 𝔮.asIdeal →
      (∀ s : ↥(chartAlgFin A (↥KM) jM), (s : ↥KM) ∈ W₀M.nonunits → s ∈ 𝔮.asIdeal) →
      (∃ s : ↥(chartAlgFin A (↥KM) jM), s ∈ 𝔮.asIdeal ∧ (s : ↥KM) ∉ W₀M.nonunits) →
      ∀ RM : Subring (IsLocalRing.ResidueField ↥W₀M),
        (∀ e : IsLocalRing.ResidueField ↥W₀M, e ∈ RM ↔ ∃ s t : ↥(chartAlgFin A (↥KM) jM), t ∉ 𝔮.asIdeal ∧
          e * IsLocalRing.residue ↥W₀M ⟨(t : ↥KM), hSW₀M t⟩ = IsLocalRing.residue ↥W₀M ⟨(s : ↥KM), hSW₀M s⟩) →
        IsDiscreteValuationRing ↥RM ∧ IsFractionRing ↥RM (IsLocalRing.ResidueField ↥W₀M) :=
    fun 𝔮 h1 h2 h3 RM hRM =>
      ModularCurve.XOne.isDiscreteValuationRing_and_isFractionRing_of_mem_iff_exists_mul_residue_eq_x1
        p M hM hpM L ζ hζ KM hKMdef A hAp hζA jM hjM ϖ hϖ W₀M hW₀M hSW₀M 𝔮 h1 h2 h3 RM hRM

  have hy₀M : ∃ s : ↥(chartAlgFin A (↥KM) jM), s ∈ yM.asIdeal ∧ (s : ↥KM) ∉ W₀M.nonunits := by

    letI algM1 : Algebra ↥(chartAlgFin A (↥KM) jM) ↥(chartAlgFin A (↥K₁) j) := θ.toAlgebra
    let 𝔓₀ : Ideal ↥(chartAlgFin A (↥K₁) j) := (IsLocalRing.maximalIdeal ↥W₀).comap incl
    have h𝔓₀ : ∀ s, s ∈ 𝔓₀ ↔ (s : ↥K₁) ∈ W₀.nonunits := fun s => by
      rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]; rfl
    haveI : 𝔓₀.IsPrime := Ideal.comap_isPrime incl _
    have hle : 𝔓₀ ≤ y.asIdeal := fun s hs => hy𝔓 s ((h𝔓₀ s).mp hs)
    obtain ⟨s, hsy, hs⟩ := hy₀
    have hlt := Ideal.comap_lt_comap_of_integral_mem_sdiff (R := ↥(chartAlgFin A (↥KM) jM)) hle
      ⟨hsy, fun h => hs ((h𝔓₀ s).mp h)⟩ (hθint s)
    obtain ⟨t, ht, ht'⟩ := SetLike.exists_of_lt hlt
    refine ⟨t, ht, fun h => ht' ?_⟩
    rw [Ideal.mem_comap]
    show θ t ∈ 𝔓₀
    rw [h𝔓₀, hθcoe]
    exact (hnuM _).mp h
  obtain ⟨RM, hRM⟩ := hRMex yM
  obtain ⟨hDVRM, hFracM⟩ := hREG yM hyϖM hy𝔓M hy₀M RM hRM
  have hρMne : ∀ t : ↥(chartAlgFin A (↥KM) jM), t ∉ yM.asIdeal → ρM t ≠ 0 := by
    intro t ht h0
    apply ht
    apply hy𝔓M
    exact ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.residue_eq_zero_iff _).mp h0)
  haveI := hFracM

  have hratioM : ∀ zM : IsLocalRing.ResidueField ↥W₀M, ∃ a b : ↥BM, (b : IsLocalRing.ResidueField ↥W₀M) ≠ 0 ∧
      zM * b = a := by
    intro zM
    obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := ↥RM) zM
    obtain ⟨s₁, t₁, ht₁, h₁⟩ := (hRM u).mp u.2
    obtain ⟨s₂, t₂, ht₂, h₂⟩ := (hRM v).mp v.2
    change (u : IsLocalRing.ResidueField ↥W₀M) * ρM t₁ = ρM s₁ at h₁
    change (v : IsLocalRing.ResidueField ↥W₀M) * ρM t₂ = ρM s₂ at h₂
    have hv0 : algebraMap (↥RM) (IsLocalRing.ResidueField ↥W₀M) v ≠ 0 := by
      intro h
      exact nonZeroDivisors.ne_zero hv (Subtype.ext h)
    have hs₂ : ρM s₂ ≠ 0 := by
      intro h
      apply hv0
      have := h₂
      rw [h] at this
      exact (mul_eq_zero.mp this).resolve_right (hρMne t₂ ht₂)
    refine ⟨⟨ρM (s₁ * t₂), ⟨_, rfl⟩⟩, ⟨ρM (t₁ * s₂), ⟨_, rfl⟩⟩, ?_, ?_⟩
    · show ρM (t₁ * s₂) ≠ 0
      rw [map_mul]
      exact mul_ne_zero (hρMne t₁ ht₁) hs₂
    · show zM * ρM (t₁ * s₂) = ρM (s₁ * t₂)
      rw [← huv]
      rw [map_mul, map_mul, div_mul_eq_mul_div, div_eq_iff hv0]

      change (u : IsLocalRing.ResidueField ↥W₀M) * (ρM t₁ * ρM s₂) = ρM s₁ * ρM t₂ * (v : IsLocalRing.ResidueField ↥W₀M)
      linear_combination (ρM s₂) * h₁ - (ρM s₁) * h₂
  have hratio : ∀ z : IsLocalRing.ResidueField ↥W₀, ∃ a b : ↥Bfl, (b : IsLocalRing.ResidueField ↥W₀) ≠ 0 ∧
      z * b = a := by
    intro z
    obtain ⟨zM, rfl⟩ := hφsurj z
    obtain ⟨a, b, hb, hab⟩ := hratioM zM
    refine ⟨⟨φ a, Subring.mem_map.mpr ⟨a, a.2, rfl⟩⟩, ⟨φ b, Subring.mem_map.mpr ⟨b, b.2, rfl⟩⟩, ?_, ?_⟩
    · show φ b ≠ 0
      exact (map_ne_zero φ).mpr hb
    · show φ zM * φ b = φ a
      rw [← map_mul, hab]
  haveI hBflFrac : IsFractionRing ↥Bfl (IsLocalRing.ResidueField ↥W₀) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨b, hb⟩
      exact IsUnit.mk0 _ (by
        show (b : IsLocalRing.ResidueField ↥W₀) ≠ 0
        exact fun h => nonZeroDivisors.ne_zero hb (Subtype.ext h))
    · intro z
      obtain ⟨a, b, hb, hz⟩ := hratio z
      exact ⟨⟨a, ⟨b, mem_nonZeroDivisors_of_ne_zero (fun h => hb (congrArg Subtype.val h))⟩⟩, hz⟩
    · intro a b h
      exact ⟨1, by rw [Subtype.ext h]⟩
  have hφinj : Function.Injective φ := φ.injective
  haveI hBflIC : IsIntegrallyClosed ↥Bfl := by
    refine (isIntegrallyClosed_iff (IsLocalRing.ResidueField ↥W₀)).mpr (fun {x} hx => ?_)
    obtain ⟨xM, rfl⟩ := hφsurj x
    let eB : ↥BM ≃+* ↥Bfl := BM.equivMapOfInjective φ hφinj

    have hxM : IsIntegral ↥BM xM := by
      obtain ⟨q, hq, hqx⟩ := hx
      refine ⟨q.map eB.symm.toRingHom, hq.map _, ?_⟩
      have hhom : φ.comp ((algebraMap ↥BM (IsLocalRing.ResidueField ↥W₀M)).comp eB.symm.toRingHom) =
          algebraMap ↥Bfl (IsLocalRing.ResidueField ↥W₀) := by
        refine RingHom.ext fun c => ?_
        show φ ((eB.symm c : ↥BM) : IsLocalRing.ResidueField ↥W₀M) = (c : IsLocalRing.ResidueField ↥W₀)
        rw [← Subring.coe_equivMapOfInjective_apply BM φ hφinj (eB.symm c)]
        show ((eB (eB.symm c) : ↥Bfl) : IsLocalRing.ResidueField ↥W₀) = _
        rw [RingEquiv.apply_symm_apply]
      apply hφinj
      rw [map_zero, Polynomial.eval₂_map, Polynomial.hom_eval₂, hhom]
      exact hqx

    let I : Ideal ↥BM :=
      { carrier := {c | ∃ d : ↥BM, (c : IsLocalRing.ResidueField ↥W₀M) * xM = d}
        add_mem' := by
          rintro a b ⟨d₁, h₁⟩ ⟨d₂, h₂⟩
          exact ⟨d₁ + d₂, by rw [Subring.coe_add, Subring.coe_add, add_mul, h₁, h₂]⟩
        zero_mem' := ⟨0, by simp⟩
        smul_mem' := by
          rintro c a ⟨d, h⟩
          exact ⟨c * d, by rw [smul_eq_mul, Subring.coe_mul, Subring.coe_mul, mul_assoc, h]⟩ }
    by_cases hI : I = ⊤
    · have h1 : (1 : ↥BM) ∈ I := hI ▸ Submodule.mem_top
      obtain ⟨d, hd⟩ := h1
      refine ⟨eB d, ?_⟩
      show ((eB d : ↥Bfl) : IsLocalRing.ResidueField ↥W₀) = φ xM
      rw [Subring.coe_equivMapOfInjective_apply, ← hd, Subring.coe_one, one_mul]
    · exfalso
      obtain ⟨𝔪, h𝔪, hI𝔪⟩ := Ideal.exists_le_maximal I hI
      let ρM' : ↥(chartAlgFin A (↥KM) jM) →+* ↥BM := ρM.rangeRestrict
      have hρM' : ∀ s, ((ρM' s : ↥BM) : IsLocalRing.ResidueField ↥W₀M) = ρM s := fun _ => rfl
      haveI := h𝔪
      let 𝔮 : ↥(XFin A (↥KM) jM) := ⟨𝔪.comap ρM', Ideal.comap_isPrime ρM' 𝔪⟩
      have h𝔮 : ∀ s, s ∈ 𝔮.asIdeal ↔ ρM' s ∈ 𝔪 := fun _ => Ideal.mem_comap
      have hzero : ∀ s : ↥(chartAlgFin A (↥KM) jM), ρM s = 0 → s ∈ 𝔮.asIdeal := by
        intro s hs
        rw [h𝔮, show ρM' s = 0 from Subtype.ext hs]
        exact 𝔪.zero_mem
      have hnu0 : ∀ s : ↥(chartAlgFin A (↥KM) jM), (s : ↥KM) ∈ W₀M.nonunits → ρM s = 0 := by
        intro s hs
        rw [hρM, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
        exact hs

      have t1 : algebraMap A ↥(chartAlgFin A (↥KM) jM) ϖ ∈ 𝔮.asIdeal := by
        apply hzero
        apply hnu0
        rw [Subalgebra.coe_algebraMap, hnuM]
        have h : ι (algebraMap A ↥KM ϖ) = algebraMap A ↥K₁ ϖ := by
          rw [IsScalarTower.algebraMap_apply A L ↥K₁ ϖ]; exact ι.commutes (algebraMap A L ϖ)
        rw [h]
        exact hW₀m ϖ (by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
      have t2 : ∀ s : ↥(chartAlgFin A (↥KM) jM), (s : ↥KM) ∈ W₀M.nonunits → s ∈ 𝔮.asIdeal :=
        fun s hs => hzero s (hnu0 s hs)
      have t3 : ∃ s : ↥(chartAlgFin A (↥KM) jM), s ∈ 𝔮.asIdeal ∧ (s : ↥KM) ∉ W₀M.nonunits := by
        obtain ⟨a, b, hb, hab⟩ := hratioM xM
        have hbI : b ∈ I := ⟨a, by rw [mul_comm]; exact hab⟩
        have h𝔪ne : 𝔪 ≠ ⊥ := by
          intro h
          apply hb
          have hb0 : b ∈ (⊥ : Ideal ↥BM) := h ▸ hI𝔪 hbI
          rw [Ideal.mem_bot] at hb0
          rw [hb0, Subring.coe_zero]
        obtain ⟨c, hc𝔪, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔪ne
        obtain ⟨s, rfl⟩ := ρM.rangeRestrict_surjective c
        exact ⟨s, (h𝔮 s).mpr hc𝔪, fun hs => hc0 (Subtype.ext (hnu0 s hs))⟩
      obtain ⟨RMq, hRMq⟩ := hRMex 𝔮
      obtain ⟨hDVRq, hFracq⟩ := hREG 𝔮 t1 t2 t3 RMq hRMq
      haveI := hDVRq
      haveI := hFracq

      have hBMle : BM ≤ RMq := by
        rintro _ ⟨s, rfl⟩
        exact (hRMq _).mpr ⟨s, 1, fun h => 𝔮.2.ne_top ((Ideal.eq_top_iff_one _).mpr h), by
          change ρM s * ρM 1 = ρM s
          rw [map_one, mul_one]⟩
      have hxq : IsIntegral ↥RMq xM :=
        hxM.map_of_comp_eq (Subring.inclusion hBMle) (RingHom.id _) (RingHom.ext fun _ => rfl)
      obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥RMq) (K := IsLocalRing.ResidueField ↥W₀M)).mp hxq
      have hxRM : xM ∈ RMq := by rw [← hr]; exact r.2
      obtain ⟨s, t, ht, hst⟩ := (hRMq xM).mp hxRM
      change xM * ρM t = ρM s at hst
      apply ht
      rw [h𝔮]
      exact hI𝔪 ⟨ρM' s, by rw [hρM', hρM', mul_comm]; exact hst⟩

  have hint : ∀ b ∈ B, IsIntegral ↥Bfl b := by
    rintro _ ⟨s, rfl⟩
    obtain ⟨q, hq, hqs⟩ := hθint s
    let g : ↥(chartAlgFin A (↥KM) jM) →+* ↥Bfl :=
      (φ.comp ρM).codRestrict Bfl (fun x => ⟨ρM x, ⟨x, rfl⟩, rfl⟩)
    refine ⟨q.map g, hq.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap ↥Bfl (IsLocalRing.ResidueField ↥W₀)).comp g = ρ.comp θ := by
      ext x; exact (hρθ x).symm
    rw [hcomp, ← Polynomial.hom_eval₂, hqs, map_zero]
  have hBBfl : B = Bfl := Subring.eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed Bfl B hBflB hint

  have hRφ : R = RM.map φ := by
    have hkerρ : ∀ x : ↥(chartAlgFin A (↥K₁) j), ρ x = 0 → x ∈ y.asIdeal := fun x hx =>
      hy𝔓 x (ValuationSubring.coe_mem_nonunits_iff.mpr ((IsLocalRing.residue_eq_zero_iff _).mp hx))
    have hρne : ∀ t : ↥(chartAlgFin A (↥K₁) j), t ∉ y.asIdeal → ρ t ≠ 0 := fun t ht h0 => ht (hkerρ t h0)
    ext e
    constructor
    · intro he
      obtain ⟨s, t, ht, hst⟩ := (hR e).mp he
      change e * ρ t = ρ s at hst
      obtain ⟨_, ⟨a, rfl⟩, ha⟩ := Subring.mem_map.mp (show ρ s ∈ Bfl from hBBfl ▸ ⟨s, rfl⟩)
      obtain ⟨_, ⟨b, rfl⟩, hb⟩ := Subring.mem_map.mp (show ρ t ∈ Bfl from hBBfl ▸ ⟨t, rfl⟩)
      have hbθ : θ b ∉ y.asIdeal := by
        intro h
        apply ht
        have h2 : θ b - t ∈ y.asIdeal := hkerρ _ (by rw [map_sub, hρθ, hb, sub_self])
        simpa using y.asIdeal.sub_mem h h2
      have hbM : b ∉ yM.asIdeal := fun h => hbθ ((hyMmem b).mp h)
      have hρMb : ρM b ≠ 0 := hρMne b hbM
      refine Subring.mem_map.mpr ⟨ρM a / ρM b, (hRM _).mpr ⟨a, b, hbM, ?_⟩, ?_⟩
      · change ρM a / ρM b * ρM b = ρM a
        exact div_mul_cancel₀ _ hρMb
      · rw [map_div₀, ha, hb, div_eq_iff (hρne t ht)]
        exact hst.symm
    · intro he
      obtain ⟨e', he', rfl⟩ := Subring.mem_map.mp he
      obtain ⟨a, b, hb, hab⟩ := (hRM e').mp he'
      change e' * ρM b = ρM a at hab
      refine (hR _).mpr ⟨θ a, θ b, fun h => hb ((hyMmem b).mpr h), ?_⟩
      change φ e' * ρ (θ b) = ρ (θ a)
      rw [hρθ, hρθ, ← map_mul, hab]
  refine ⟨?_, ?_⟩
  · rw [hRφ]
    haveI := hDVRM
    let eR : ↥RM ≃+* ↥(RM.map φ) := RM.equivMapOfInjective φ hφinj
    haveI : IsPrincipalIdealRing ↥(RM.map φ) := IsPrincipalIdealRing.of_surjective eR.toRingHom eR.surjective
    haveI : IsLocalRing ↥(RM.map φ) := IsLocalRing.of_surjective' eR.toRingHom eR.surjective
    exact { toIsPrincipalIdealRing := inferInstance, toIsLocalRing := inferInstance,
            not_a_field' := fun h => IsDiscreteValuationRing.not_isField (↥RM)
              (MulEquiv.isField (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h) eR.toMulEquiv) }
  · rw [hRφ]
    haveI := hFracM
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨b, hb⟩
      exact IsUnit.mk0 _ (by
        show (b : IsLocalRing.ResidueField ↥W₀) ≠ 0
        exact fun h => nonZeroDivisors.ne_zero hb (Subtype.ext h))
    · intro z
      obtain ⟨zM, rfl⟩ := hφsurj z
      obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := ↥RM) zM
      have hv0 : algebraMap (↥RM) (IsLocalRing.ResidueField ↥W₀M) v ≠ 0 :=
        fun h => nonZeroDivisors.ne_zero hv (Subtype.ext h)
      refine ⟨⟨⟨φ (algebraMap (↥RM) (IsLocalRing.ResidueField ↥W₀M) u), Subring.mem_map.mpr ⟨u, u.2, rfl⟩⟩,
        ⟨⟨φ (algebraMap (↥RM) (IsLocalRing.ResidueField ↥W₀M) v), Subring.mem_map.mpr ⟨v, v.2, rfl⟩⟩,
        mem_nonZeroDivisors_of_ne_zero (fun h => (map_ne_zero φ).mpr hv0 (congrArg Subtype.val h))⟩⟩, ?_⟩
      show φ zM * φ (algebraMap (↥RM) (IsLocalRing.ResidueField ↥W₀M) v) =
        φ (algebraMap (↥RM) (IsLocalRing.ResidueField ↥W₀M) u)
      rw [← map_mul, ← huv, div_mul_cancel₀ _ hv0]
    · intro a b h
      exact ⟨1, by rw [Subtype.ext h]⟩

end S_ModularCurve_XOne_isDiscreteValuationRing_and_isFractionRing_of_mem_iff_exists_mul_residue_eq_of_gamma1_inf_gamma0_le
end P2MW
export P2MW.S_ModularCurve_XOne_isDiscreteValuationRing_and_isFractionRing_of_mem_iff_exists_mul_residue_eq_of_gamma1_inf_gamma0_le (solution)
