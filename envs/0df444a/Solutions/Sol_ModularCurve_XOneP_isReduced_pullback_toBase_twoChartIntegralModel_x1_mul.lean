-- Prove2me | solution 1 for ModularCurve.XOneP.isReduced_pullback_toBase_twoChartIntegralModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/5f894ab3-379a-5868-bed0-6000cb2967d6

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isReduced_pullback_toBase_of_forall_map_span_eq_maximalIdeal
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_ModularCurve_XOneP_exists_eq_mul_of_mem_nonunits_valuationSubring_x1_mul
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_isReduced_pullback_toBase_twoChartIntegralModel_x1_mul
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper"
p2m_attr_erase "simp" "CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero"
p2m_attr_erase "simp" "TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open AlgebraicCurve.TwoChartIntegralModel

namespace RedAux

theorem maximalIdeal_le_span_of_forall_exists
    (S : Type) [CommRing S] (𝔓 : Ideal S) [𝔓.IsPrime] (x : S)
    (hdiv : ∀ a ∈ 𝔓, ∃ a' b' : S, b' ∉ 𝔓 ∧ a * b' = x * a') :
    maximalIdeal (Localization.AtPrime 𝔓) ≤ Ideal.span {algebraMap S (Localization.AtPrime 𝔓) x} := by
  intro m hm
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔓.primeCompl m
  dsimp only at hm ⊢
  have ha : a ∈ 𝔓 := by
    simpa using (IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime 𝔓) 𝔓 a s).mp hm
  obtain ⟨a', b', hb', hab⟩ := hdiv a ha
  have : IsLocalization.mk' (Localization.AtPrime 𝔓) a s =
      algebraMap S _ x * IsLocalization.mk' (Localization.AtPrime 𝔓) a' (s * ⟨b', hb'⟩) := by
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq]
    simp only [Submonoid.coe_mul]
    rw [← hab]; ring_nf
  rw [this]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem map_residue_eq_zero_iff {ϖ : R} (hϖ : maximalIdeal R = Ideal.span {ϖ}) (P : Polynomial R) :
    P.map (residue R) = 0 ↔ Polynomial.C ϖ ∣ P := by
  rw [Polynomial.C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
  refine forall_congr' fun i => ?_
  rw [Polynomial.coeff_map, Polynomial.coeff_zero, residue_eq_zero_iff, hϖ, Ideal.mem_span_singleton]

theorem aeval_mem_and_inv_mem_of_inv {F : Type} [Field F] [Algebra R F] (ϖ : R) (V : ValuationSubring F) (j : F)
    (hj0 : j ≠ 0) (hjV : j ∈ V) (hjiV : j⁻¹ ∈ V)
    (h : ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j⁻¹ P ∈ V ∧ (Polynomial.aeval j⁻¹ P)⁻¹ ∈ V) :
    ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V := by
  intro P hP
  have hrev : ¬ (Polynomial.C ϖ ∣ P.reverse) := by
    intro hd
    apply hP
    rw [Polynomial.C_dvd_iff_dvd_coeff] at hd ⊢
    intro i
    by_cases hi : i ≤ P.natDegree
    · have := hd (Polynomial.revAt P.natDegree i)
      rwa [Polynomial.reverse, Polynomial.coeff_reflect, Polynomial.revAt_invol] at this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.mp hi)]; exact dvd_zero _
  obtain ⟨h1, h2⟩ := h P.reverse hrev
  letI : Invertible j := invertibleOfNonzero hj0
  have key : Polynomial.aeval j P = Polynomial.aeval j⁻¹ P.reverse * j ^ P.natDegree := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, ← invOf_eq_inv j, Polynomial.eval₂_reverse_mul_pow]
  refine ⟨by rw [key]; exact mul_mem h1 (pow_mem hjV _), ?_⟩
  rw [key, mul_inv, ← inv_pow]
  exact mul_mem h2 (pow_mem hjiV _)

theorem map_span_eq_maximalIdeal_of_forall_exists_eq_mul
    (K₀ : Type) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : maximalIdeal R = Ideal.span {ϖ})
    (RAM : ∀ V : ValuationSubring F, (∀ a : R, algebraMap R F a ∈ V) → algebraMap R F ϖ ∈ V.nonunits →
      (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
      ∀ f : F, f ∈ V.nonunits → ∃ g : F, g ∈ V ∧ f = algebraMap R F ϖ * g)
    (P : Ideal ↥(chartAlgFin R F j)) [P.IsPrime]
    (hP : P ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes) :
    Ideal.map (algebraMap ↥(chartAlgFin R F j) (Localization.AtPrime P))
        (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}) =
      maximalIdeal (Localization.AtPrime P) := by
  classical
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ

  obtain ⟨V, -, hsub, hPmem, hϖV, hVj⟩ :=
    exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin R K₀ F j htj hFD hsep ϖ hirr.prime P hP
  have hVA : ∀ a : R, algebraMap R F a ∈ V := fun a => hsub (algebraMap R _ a)
  have hVm : ∀ a ∈ maximalIdeal R, algebraMap R F a ∈ V.nonunits := by
    intro a ha
    rw [hϖ, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul]
    have hcoe : algebraMap R F ϖ * algebraMap R F b = (((⟨_, hVA ϖ⟩ : V) * ⟨_, hVA b⟩ : V) : F) := rfl
    rw [hcoe, ValuationSubring.coe_mem_nonunits_iff]
    exact Ideal.mul_mem_right _ _ (ValuationSubring.coe_mem_nonunits_iff.mp hϖV)
  have hVj' : ∀ Q : Polynomial R, Q.map (residue R) ≠ 0 → Polynomial.aeval j Q ∈ V ∧ (Polynomial.aeval j Q)⁻¹ ∈ V :=
    fun Q hQ => hVj Q ((map_residue_eq_zero_iff hϖ Q).not.mp hQ)

  obtain ⟨-, ⟨𝔓, h𝔓p, -, h𝔓mem, -, h𝔓loc⟩, -⟩ :=
    le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental R K₀ F j htj hFD hsep V hVA hVm hVj'
  have h𝔓eq : 𝔓 = P := by ext b; rw [h𝔓mem, hPmem]
  subst h𝔓eq

  have hram := RAM V hVA hϖV hVj
  have hdiv : ∀ a ∈ 𝔓, ∃ a' b' : ↥(chartAlgFin R F j), b' ∉ 𝔓 ∧ a * b' = algebraMap R _ ϖ * a' := by
    intro a ha
    obtain ⟨g, hg, hag⟩ := hram _ ((hPmem a).mp ha)
    obtain ⟨a', b', hb', hgb⟩ := (h𝔓loc g).mp hg
    refine ⟨a', b', hb', Subtype.ext ?_⟩
    change (a : F) * (b' : F) = ((algebraMap R ↥(chartAlgFin R F j) ϖ : ↥(chartAlgFin R F j)) : F) * (a' : F)
    rw [hag, mul_assoc, hgb]; rfl
  apply le_antisymm
  ·
    rw [Ideal.map_le_iff_le_comap, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔓) 𝔓 _).mpr (hP.1.2 (Ideal.subset_span rfl))
  · rw [Ideal.map_span, Set.image_singleton]
    exact maximalIdeal_le_span_of_forall_exists _ 𝔓 _ hdiv

end RedAux

open RedAux in

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
    (k : Type) [Field k] [CharP k p] [Algebra A k] :
    IsReduced (pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A k)))) := by
  classical

  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  have htj := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  haveI hFD := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma1 (M * p)) hT L K hK j hj
  haveI hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsSeparable.of_integral _ _

  obtain ⟨ϖ, hirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ : maximalIdeal A = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hirr
  have hj0 : (j : ↥K) ≠ 0 := Fact.out

  have hX : ¬ (Polynomial.C ϖ ∣ (Polynomial.X : Polynomial A)) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]; intro h
    have := h 1
    rw [Polynomial.coeff_X_one] at this
    exact hirr.not_isUnit (isUnit_of_dvd_one this)

  have RAMj : ∀ V : ValuationSubring ↥K, (∀ a : A, algebraMap A ↥K a ∈ V) → algebraMap A ↥K ϖ ∈ V.nonunits →
      (∀ P : Polynomial A, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
      ∀ f : ↥K, f ∈ V.nonunits → ∃ g : ↥K, g ∈ V ∧ f = algebraMap A ↥K ϖ * g := by
    intro V hVA hϖV hVj
    have hVm : ∀ a ∈ maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits := by
      intro a ha
      rw [hϖ, Ideal.mem_span_singleton] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [map_mul]
      have hcoe : algebraMap A ↥K ϖ * algebraMap A ↥K b = (((⟨_, hVA ϖ⟩ : V) * ⟨_, hVA b⟩ : V) : ↥K) := rfl
      rw [hcoe, ValuationSubring.coe_mem_nonunits_iff]
      exact Ideal.mul_mem_right _ _ (ValuationSubring.coe_mem_nonunits_iff.mp hϖV)
    have hVj' : ∀ Q : Polynomial A, Q.map (residue A) ≠ 0 → Polynomial.aeval j Q ∈ V ∧ (Polynomial.aeval j Q)⁻¹ ∈ V :=
      fun Q hQ => hVj Q ((map_residue_eq_zero_iff hϖ Q).not.mp hQ)
    exact ModularCurve.XOneP.exists_eq_mul_of_mem_nonunits_valuationSubring_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj
      ϖ hϖ V hVA hVm hVj'

  have RAMi : ∀ V : ValuationSubring ↥K, (∀ a : A, algebraMap A ↥K a ∈ V) → algebraMap A ↥K ϖ ∈ V.nonunits →
      (∀ P : Polynomial A, ¬ (Polynomial.C ϖ ∣ P) → Polynomial.aeval j⁻¹ P ∈ V ∧ (Polynomial.aeval j⁻¹ P)⁻¹ ∈ V) →
      ∀ f : ↥K, f ∈ V.nonunits → ∃ g : ↥K, g ∈ V ∧ f = algebraMap A ↥K ϖ * g := by
    intro V hVA hϖV hVj
    have hjX := hVj Polynomial.X hX
    simp only [Polynomial.aeval_X, inv_inv] at hjX
    exact RAMj V hVA hϖV (aeval_mem_and_inv_mem_of_inv ϖ V j hj0 hjX.2 hjX.1 hVj)

  have hFin := fun (P : Ideal ↥(chartAlgFin A (↥K) j)) (hPp : P.IsPrime) hP =>
    @map_span_eq_maximalIdeal_of_forall_exists_eq_mul A _ _ _ L _ _ _ ↥K _ _ _ _ j _ htj hFD hsep ϖ hϖ RAMj P hPp hP

  haveI : Fact ((j : ↥K)⁻¹ ≠ 0) := ⟨inv_ne_zero hj0⟩
  have htji : Transcendental A (j : ↥K)⁻¹ := fun h => htj (by simpa using h.inv)
  have hadj : IntermediateField.adjoin L ({(j : ↥K)⁻¹} : Set ↥K) = IntermediateField.adjoin L ({j} : Set ↥K) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self L j)
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have := IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self L (j : ↥K)⁻¹)
      rwa [inv_inv] at this
  have hFDi : FiniteDimensional ↥(IntermediateField.adjoin L ({(j : ↥K)⁻¹} : Set ↥K)) ↥K := by rw [hadj]; exact hFD
  have hsepi : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({(j : ↥K)⁻¹} : Set ↥K)) ↥K := by rw [hadj]; exact hsep
  have hInf := fun (P : Ideal ↥(chartAlgFin A (↥K) (j : ↥K)⁻¹)) (hPp : P.IsPrime) hP =>
    @map_span_eq_maximalIdeal_of_forall_exists_eq_mul A _ _ _ L _ _ _ ↥K _ _ _ _ (j : ↥K)⁻¹ _ htji hFDi hsepi ϖ hϖ RAMi P hPp hP

  haveI : CharP (ResidueField A) p := by
    have hp0 : ((p : ℕ) : ResidueField A) = 0 := by
      rw [← map_natCast (residue A), residue_eq_zero_iff]; exact hAp
    exact ringChar.of_eq (CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) hp0)
  haveI : Finite (ResidueField A) := by
    refine Finite.of_surjective (ZMod.castHom (dvd_refl p) (ResidueField A)) fun x => ?_
    obtain ⟨n, rfl⟩ := IsCyclotomicExtension.Rat.surjective_algebraMap_int_residueField_of_isDiscreteValuationRing p L A hAp x
    exact ⟨(n : ZMod p), by simp⟩
  haveI : PerfectField (ResidueField A) := inferInstance

  have hk : algebraMap A k ϖ = 0 := by
    have hker : RingHom.ker (algebraMap A k) = maximalIdeal A := by
      refine IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal_of_ne_bot (RingHom.ker_isPrime _) ?_)
      intro h
      have hp : (p : A) ∈ RingHom.ker (algebraMap A k) := by
        rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
      rw [h, Ideal.mem_bot] at hp
      haveI : CharZero A := (algebraMap A L).charZero
      exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)
    have : ϖ ∈ RingHom.ker (algebraMap A k) := by rw [hker, hϖ]; exact Ideal.mem_span_singleton_self ϖ
    exact this
  exact isReduced_pullback_toBase_of_forall_map_span_eq_maximalIdeal A ϖ hϖ L ↥K j htj hFD hsep
    (fun P _ hP => hFin P inferInstance hP) (fun P _ hP => hInf P inferInstance hP) k hk

end S_ModularCurve_XOneP_isReduced_pullback_toBase_twoChartIntegralModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_isReduced_pullback_toBase_twoChartIntegralModel_x1_mul (solution)
