-- Prove2me | solution 1 for ModularCurve.XOneP.isPushout_chartAlgFin_levelRaise_twoChartIntegralModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e8466c51-66cc-5bbe-9047-382cfd16bbc7

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_XOne_finite_and_etale_chartAlgFin_levelRaise_x1
import Theorems.Thm_ModularCurve_laurentBaseChange_x1FunctionField_sup_levelRaise_eq_and_relfinrank_eq
import Theorems.Thm_Algebra_Etale_isIntegrallyClosed_tensorProduct_of_isDomain
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_isPushout_chartAlgFin_levelRaise_twoChartIntegralModel_x1_mul
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.jqNModC_one AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.congrEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper"
p2m_attr_erase "simp" "CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_uniformizerMod"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero"
p2m_attr_erase "simp" "TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace TensorNormalProof

theorem injective_productMap_of_flat_of_linearDisjoint
    {R₀ : Type*} [CommRing R₀]
    {F₀ : Type*} [Field F₀] [Algebra R₀ F₀] [IsFractionRing R₀ F₀]
    {E : Type*} [Field E] [Algebra F₀ E] [Algebra R₀ E] [IsScalarTower R₀ F₀ E]
    {P N : Type*} [CommRing P] [CommRing N] [Algebra R₀ P] [Algebra R₀ N] [Module.Flat R₀ N]
    (AK BK : Subalgebra F₀ E) (hLD : AK.LinearDisjoint BK)
    (fP : P →ₐ[R₀] E) (fN : N →ₐ[R₀] E) (hfP : Function.Injective fP) (hfN : Function.Injective fN)
    (hP : ∀ x, fP x ∈ AK) (hN : ∀ y, fN y ∈ BK) :
    Function.Injective (Algebra.TensorProduct.productMap fP fN) := by
  classical
  let fP₁ : P →ₗ[R₀] ↥AK :=
    { toFun := fun x => ⟨fP x, hP x⟩
      map_add' := fun x y => Subtype.ext (map_add fP x y)
      map_smul' := fun r x => Subtype.ext (by simp) }
  have hfP₁ : Function.Injective fP₁ := fun x y h => hfP (congrArg Subtype.val h :)
  let fN₁ : N →ₗ[R₀] ↥BK :=
    { toFun := fun y => ⟨fN y, hN y⟩
      map_add' := fun x y => Subtype.ext (map_add fN x y)
      map_smul' := fun r x => Subtype.ext (by simp) }
  have hfN₁ : Function.Injective fN₁ := fun x y h => hfN (congrArg Subtype.val h :)
  haveI : Module.Flat R₀ F₀ := IsLocalization.flat F₀ (nonZeroDivisors R₀)
  haveI : Module.Flat R₀ ↥AK := Module.Flat.trans R₀ F₀ ↥AK
  have h1 : Function.Injective (fP₁.rTensor N) := Module.Flat.rTensor_preserves_injective_linearMap fP₁ hfP₁
  have h2 : Function.Injective (fN₁.lTensor ↥AK) := Module.Flat.lTensor_preserves_injective_linearMap fN₁ hfN₁
  have h3 : Function.Injective (AK.mulMap BK) := Subalgebra.linearDisjoint_iff_injective.mp hLD
  haveI : TensorProduct.CompatibleSMul R₀ F₀ ↥AK ↥BK :=
    IsLocalization.tensorProduct_compatibleSMul (nonZeroDivisors R₀) F₀ ↥AK ↥BK
  let γ : ↥AK ⊗[R₀] ↥BK →ₗ[F₀] ↥AK ⊗[F₀] ↥BK := TensorProduct.mapOfCompatibleSMul F₀ R₀ F₀ ↥AK ↥BK
  have hγ : ∀ (a : ↥AK) (b : ↥BK), γ (a ⊗ₜ[R₀] b) = a ⊗ₜ[F₀] b := fun a b =>
    TensorProduct.mapOfCompatibleSMul_tmul F₀ R₀ F₀ ↥AK ↥BK a b
  have key : ∀ u : P ⊗[R₀] N,
      AK.mulMap BK (γ (fN₁.lTensor ↥AK (fP₁.rTensor N u))) = Algebra.TensorProduct.productMap fP fN u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y =>
        rw [LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hγ, Subalgebra.mulMap_tmul,
          Algebra.TensorProduct.productMap_apply_tmul]
        rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  intro u v huv
  have h : AK.mulMap BK (γ (fN₁.lTensor ↥AK (fP₁.rTensor N u))) = AK.mulMap BK (γ (fN₁.lTensor ↥AK (fP₁.rTensor N v))) := by
    rw [key, key, huv]

  have hγinj : Function.Injective γ := by
    haveI : TensorProduct.CompatibleSMul F₀ R₀ ↥AK ↥BK := inferInstance
    let γ' : ↥AK ⊗[F₀] ↥BK →ₗ[F₀] ↥AK ⊗[R₀] ↥BK := TensorProduct.mapOfCompatibleSMul R₀ F₀ F₀ ↥AK ↥BK
    have hleft : ∀ w, γ' (γ w) = w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a b => rw [hγ]; exact TensorProduct.mapOfCompatibleSMul_tmul R₀ F₀ F₀ ↥AK ↥BK a b
      | add x y hx hy => simp only [map_add, hx, hy]
    exact Function.LeftInverse.injective hleft
  exact h1 (h2 (hγinj (h3 h)))

theorem exists_mul_eq_algebraMap_of_ne_zero
    {R₀ S : Type*} [CommRing R₀] [Nontrivial R₀] [CommRing S] [IsDomain S] [Algebra R₀ S] [Module.Finite R₀ S]
    (d : S) (hd : d ≠ 0) : ∃ (d' : S) (m : R₀), m ≠ 0 ∧ d * d' = algebraMap R₀ S m := by
  classical
  obtain ⟨p, hp, hpd⟩ : IsIntegral R₀ d := Algebra.IsIntegral.isIntegral d
  obtain ⟨q, hq, hXq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp.ne_zero 0
  rw [map_zero, sub_zero] at hq hXq
  have hq0 : q.coeff 0 ≠ 0 := fun h => hXq (Polynomial.X_dvd_iff.mpr h)
  have hqd : Polynomial.aeval d q = 0 := by
    have h0 : Polynomial.aeval d p = 0 := hpd
    rw [hq, map_mul, map_pow, Polynomial.aeval_X] at h0
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero _ hd)
  refine ⟨-(Polynomial.aeval d q.divX), q.coeff 0, hq0, ?_⟩
  have h := congrArg (Polynomial.aeval d) (Polynomial.X_mul_divX_add q)
  rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, hqd] at h
  linear_combination (-1 : S) * h

theorem isPushout_of_etale_of_linearDisjoint
    {RM RN RP RQ : Type*} [CommRing RM] [CommRing RN] [CommRing RP] [CommRing RQ]
    [IsDomain RN] [IsDomain RP] [IsIntegrallyClosed RP]
    (iM : RM →+* RN) (ρ : RM →+* RP) (ρ' : RN →+* RQ) (ι : RP →+* RQ)
    (hsq : ∀ r, ι (ρ r) = ρ' (iM r)) (hρ : Function.Injective ρ)
    (hfin : iM.Finite) (het : iM.Etale)
    {F₀ E : Type*} [Field F₀] [Field E] [Algebra RM F₀] [IsFractionRing RM F₀] [Algebra F₀ E]
    (fP : RP →+* E) (fN : RN →+* E) (fQ : RQ →+* E)
    (hfP : Function.Injective fP) (hfN : Function.Injective fN) (hfQ : Function.Injective fQ)
    (hfPρ : fP.comp ρ = (algebraMap F₀ E).comp (algebraMap RM F₀))
    (hfNi : fN.comp iM = (algebraMap F₀ E).comp (algebraMap RM F₀))
    (hfQι : fQ.comp ι = fP) (hfQρ' : fQ.comp ρ' = fN)
    (AK BK : Subalgebra F₀ E) (hLD : AK.LinearDisjoint BK)
    (hP : ∀ x, fP x ∈ AK) (hN : ∀ y, fN y ∈ BK)
    (hK : ∀ k ∈ AK, ∃ a b : RP, b ≠ 0 ∧ k * fP b = fP a)
    (hKN : ∀ n ∈ BK, ∃ c d : RN, d ≠ 0 ∧ n * fN d = fN c)
    (hQsup : ∀ z : RQ, fQ z ∈ AK ⊔ BK)
    (hQint : ∀ z : RQ, fP.IsIntegralElem (fQ z)) :
    letI : Algebra RM RN := iM.toAlgebra
    letI : Algebra RM RP := ρ.toAlgebra
    letI : Algebra RN RQ := ρ'.toAlgebra
    letI : Algebra RP RQ := ι.toAlgebra
    letI : Algebra RM RQ := (ι.comp ρ).toAlgebra
    haveI : IsScalarTower RM RP RQ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : IsScalarTower RM RN RQ := IsScalarTower.of_algebraMap_eq (fun r => hsq r)
    Algebra.IsPushout RM RN RP RQ := by
  classical
  letI : Algebra RM RN := iM.toAlgebra
  letI : Algebra RM RP := ρ.toAlgebra
  letI : Algebra RN RQ := ρ'.toAlgebra
  letI : Algebra RP RQ := ι.toAlgebra
  letI : Algebra RM RQ := (ι.comp ρ).toAlgebra
  haveI : IsScalarTower RM RP RQ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower RM RN RQ := IsScalarTower.of_algebraMap_eq (fun r => hsq r)
  show Algebra.IsPushout RM RN RP RQ
  haveI : Module.Finite RM RN := hfin
  haveI : Algebra.Etale RM RN := het
  haveI : Nontrivial RM := nontrivial_of_ne 0 1 (fun h => by simpa using congrArg ρ h)

  letI : Algebra RM E := ((algebraMap F₀ E).comp (algebraMap RM F₀)).toAlgebra
  haveI : IsScalarTower RM F₀ E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let fP' : RP →ₐ[RM] E := { fP with commutes' := fun r => (RingHom.congr_fun hfPρ r : _) }
  let fN' : RN →ₐ[RM] E := { fN with commutes' := fun r => (RingHom.congr_fun hfNi r : _) }
  have hfP' : ∀ x, fP' x = fP x := fun _ => rfl
  have hfN' : ∀ y, fN' y = fN y := fun _ => rfl

  let Ψ := Algebra.TensorProduct.productMap fP' fN'
  have hΨ_tmul : ∀ (x : RP) (y : RN), Ψ (x ⊗ₜ y) = fP x * fN y := fun x y =>
    Algebra.TensorProduct.productMap_apply_tmul fP' fN' x y
  have hΨinj : Function.Injective Ψ :=
    injective_productMap_of_flat_of_linearDisjoint AK BK hLD fP' fN' hfP hfN hP hN

  let Φ : RP ⊗[RM] RN →ₐ[RP] RQ :=
    Algebra.TensorProduct.lift (Algebra.ofId RP RQ) (IsScalarTower.toAlgHom RM RN RQ) (fun x y => Commute.all _ _)
  have hΦ_tmul : ∀ (x : RP) (y : RN), Φ (x ⊗ₜ y) = ι x * ρ' y := fun x y => by
    simp only [Φ, Algebra.TensorProduct.lift_tmul]
    rfl
  have hfac : ∀ t, fQ (Φ t) = Ψ t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
        rw [hΦ_tmul, map_mul, hΨ_tmul]
        exact congrArg₂ (· * ·) (RingHom.congr_fun hfQι x) (RingHom.congr_fun hfQρ' y)
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hΦinj : Function.Injective Φ := fun a b h => hΨinj (by rw [← hfac, ← hfac, h])

  haveI : IsDomain (RP ⊗[RM] RN) := Function.Injective.isDomain Ψ.toRingHom hΨinj
  haveI : IsIntegrallyClosed (RP ⊗[RM] RN) := Algebra.Etale.isIntegrallyClosed_tensorProduct_of_isDomain RP RN

  have hden : ∀ ξ : ↥AK ⊗[F₀] ↥BK, ∃ b : RP, b ≠ 0 ∧ ∃ t : RP ⊗[RM] RN, AK.mulMap BK ξ * fP b = Ψ t := by
    intro ξ
    induction ξ using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | tmul k n =>
        obtain ⟨a, b, hb, hk⟩ := hK k.1 k.2
        obtain ⟨c, d, hd, hn⟩ := hKN n.1 n.2
        obtain ⟨d', m, hm, hdd'⟩ := exists_mul_eq_algebraMap_of_ne_zero (R₀ := RM) d hd
        refine ⟨b * ρ m, mul_ne_zero hb (fun h => hm (hρ (by rw [h, map_zero]))), a ⊗ₜ (c * d'), ?_⟩
        have h1 : fP (ρ m) = fN d * fN d' := by
          rw [← map_mul, hdd']
          exact (RingHom.congr_fun hfPρ m).trans (RingHom.congr_fun hfNi m).symm
        rw [Subalgebra.mulMap_tmul, hΨ_tmul]
        calc k.1 * n.1 * fP (b * ρ m) = (k.1 * fP b) * (n.1 * fN d) * fN d' := by rw [map_mul, h1]; ring
          _ = fP a * fN (c * d') := by rw [hk, hn, map_mul]; ring
    | add ξ₁ ξ₂ h₁ h₂ =>
        obtain ⟨b₁, hb₁, t₁, e₁⟩ := h₁
        obtain ⟨b₂, hb₂, t₂, e₂⟩ := h₂
        refine ⟨b₁ * b₂, mul_ne_zero hb₁ hb₂, (b₂ ⊗ₜ 1) * t₁ + (b₁ ⊗ₜ 1) * t₂, ?_⟩
        rw [map_add, map_add, map_mul Ψ, map_mul Ψ, hΨ_tmul, hΨ_tmul, map_one, mul_one, mul_one, ← e₁, ← e₂,
          map_mul, add_mul]
        ring

  have hΦsurj : Function.Surjective Φ := by
    intro z
    have hz : fQ z ∈ (AK.mulMap BK).range := by rw [Subalgebra.mulMap_range]; exact hQsup z
    obtain ⟨ξ, hξ⟩ := hz
    obtain ⟨b, hb, t, hbt⟩ := hden ξ
    have hξ' : AK.mulMap BK ξ = fQ z := hξ
    rw [hξ'] at hbt
    let FT := FractionRing (RP ⊗[RM] RN)
    have hΨinj' : Function.Injective Ψ.toRingHom := hΨinj
    let θ : FT →+* E := IsFractionRing.lift hΨinj'
    have hθ : ∀ s, θ (algebraMap (RP ⊗[RM] RN) FT s) = Ψ s := fun s => IsFractionRing.lift_algebraMap hΨinj' s
    have hfPb : fP b ≠ 0 := fun h => hb (hfP (h.trans (map_zero fP).symm))
    have hb1 : algebraMap (RP ⊗[RM] RN) FT (b ⊗ₜ[RM] (1 : RN)) ≠ 0 := by
      intro h
      apply hfPb
      have h2 := congrArg θ h
      rwa [hθ, map_zero, hΨ_tmul, map_one, mul_one] at h2
    let w : FT := algebraMap _ FT t / algebraMap _ FT (b ⊗ₜ[RM] (1 : RN))
    have hθw : θ w = fQ z := by
      rw [map_div₀, hθ, hθ, hΨ_tmul, map_one, mul_one, ← hbt]
      exact mul_div_cancel_right₀ _ hfPb
    have hcomp : θ.comp (algebraMap RP FT) = fP := by
      ext x
      rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply RP (RP ⊗[RM] RN) FT, hθ,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hΨ_tmul, map_one, mul_one]
    have hwint : IsIntegral (RP ⊗[RM] RN) w := by
      obtain ⟨poly, hmonic, heval⟩ := hQint z
      have hRP : IsIntegral RP w := by
        refine ⟨poly, hmonic, θ.injective ?_⟩
        rw [Polynomial.hom_eval₂, map_zero, hθw, hcomp]
        exact heval
      exact hRP.tower_top
    obtain ⟨t', ht'⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hwint
    refine ⟨t', hfQ ?_⟩
    rw [hfac, ← hθ, ht', hθw]

  have hpo : Algebra.IsPushout RM RP RN RQ := by
    refine ⟨IsBaseChange.of_equiv (AlgEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩).toLinearEquiv (fun y => ?_)⟩
    show Φ (1 ⊗ₜ y) = _
    rw [hΦ_tmul, map_one, one_mul]
    rfl
  exact hpo.symm

end TensorNormalProof

open TensorNormalProof in
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

    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (K' : IntermediateField L (LaurentSeries L))
    (hK' : K' = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * ℓ * p)))
    [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (j' : ↥K') (hj' : ((j' : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j' ≠ 0)]
    (hle : K ≤ K') (hleMK : K_M ≤ K) (hleNK' : K_N ≤ K')
    (ι : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →ₐ[A] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K') j'))
    (hι : ∀ x, (((ι x : ↥K') : LaurentSeries L)) = ((x : ↥K) : LaurentSeries L))
    (ρ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) →ₐ[A] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (hρ : ∀ x, (((ρ x : ↥K) : LaurentSeries L)) = ((x : ↥K_M) : LaurentSeries L))
    (ρ' : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) →ₐ[A] ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K') j'))
    (hρ' : ∀ x, (((ρ' x : ↥K') : LaurentSeries L)) = ((x : ↥K_N) : LaurentSeries L))
    (hsq : ∀ r, ι (ρ r) = ρ' (ι_M r)) :
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) := ι_M.toRingHom.toAlgebra
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := ρ.toRingHom.toAlgebra
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K') j') := ρ'.toRingHom.toAlgebra
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K') j') := ι.toRingHom.toAlgebra
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K') j') := (ι.toRingHom.comp ρ.toRingHom).toAlgebra
    haveI : IsScalarTower ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K') j') := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : IsScalarTower ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K') j') := IsScalarTower.of_algebraMap_eq (fun r => hsq r)
    Algebra.IsPushout ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K') j') := by
  classical

  have hT : ∀ N : ℕ, ModularGroup.T ∈ CongruenceSubgroup.Gamma1 N := fun N => by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.coe_T]
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  haveI : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) hℓ.ne_zero⟩
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne p)⟩
  haveI : NeZero (M * ℓ * p) := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne M) hℓ.ne_zero) (NeZero.ne p)⟩
  have hfdM : FiniteDimensional ↥(IntermediateField.adjoin L ({j_M} : Set ↥K_M)) ↥K_M :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CongruenceSubgroup.Gamma1 M) (hT M)
      L K_M hK_M j_M hj_M
  have hfdN : FiniteDimensional ↥(IntermediateField.adjoin L ({j_N} : Set ↥K_N)) ↥K_N :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CongruenceSubgroup.Gamma1 (M * ℓ)) (hT _)
      L K_N hK_N j_N hj_N
  have hfdP : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CongruenceSubgroup.Gamma1 (M * p)) (hT _)
      L K hK j hj
  have hfdQ : FiniteDimensional ↥(IntermediateField.adjoin L ({j'} : Set ↥K')) ↥K' :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange (CongruenceSubgroup.Gamma1 (M * ℓ * p)) (hT _)
      L K' hK' j' hj'
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j_M} : Set ↥K_M)) ↥K_M := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j_N} : Set ↥K_N)) ↥K_N := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsAlgebraic.of_finite _ _

  haveI hfrM : IsFractionRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_M) j_M) ↥K_M :=
    AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L (↥K_M) {j_M}
  haveI hfrN : IsFractionRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) ↥K_N :=
    AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L (↥K_N) {j_N}
  haveI hfrP : IsFractionRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ↥K :=
    AlgebraicCurve.TwoChartIntegralModel.isFractionRing_chartAlg A L (↥K) {j}
  haveI : IsIntegrallyClosed ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :=
    AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A (↥K) {j}

  obtain ⟨hfinMN, hetMN⟩ := ModularCurve.XOne.finite_and_etale_chartAlgFin_levelRaise_x1 p M hM hpM L ζ hζ A hAp hζA ℓ hℓ hℓMp
    K_M hK_M j_M hj_M K_N hK_N j_N hj_N hleMN ι_M hι_M
  obtain ⟨hsup, hdeg⟩ := ModularCurve.laurentBaseChange_x1FunctionField_sup_levelRaise_eq_and_relfinrank_eq L M ℓ p
    (le_trans (by norm_num) hM) hℓ hℓMp
  rw [← hK, ← hK_N, ← hK'] at hsup
  rw [← hK, ← hK_N, ← hK', ← hK_M] at hdeg

  let fP : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* LaurentSeries L :=
    (algebraMap ↥K (LaurentSeries L)).comp (algebraMap _ ↥K)
  let fN : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N) →+* LaurentSeries L :=
    (algebraMap ↥K_N (LaurentSeries L)).comp (algebraMap _ ↥K_N)
  let fQ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K') j') →+* LaurentSeries L :=
    (algebraMap ↥K' (LaurentSeries L)).comp (algebraMap _ ↥K')
  have hfP_apply : ∀ x, fP x = ((x : ↥K) : LaurentSeries L) := fun _ => rfl
  have hfN_apply : ∀ y, fN y = ((y : ↥K_N) : LaurentSeries L) := fun _ => rfl
  have hfQ_apply : ∀ z, fQ z = ((z : ↥K') : LaurentSeries L) := fun _ => rfl
  have hfP : Function.Injective fP := fun x y h => Subtype.ext (Subtype.ext h)
  have hfN : Function.Injective fN := fun x y h => Subtype.ext (Subtype.ext h)
  have hfQ : Function.Injective fQ := fun x y h => Subtype.ext (Subtype.ext h)
  have hρinj : Function.Injective ρ.toRingHom := fun x y h => by
    apply Subtype.ext; apply Subtype.ext
    rw [← hρ x, ← hρ y]
    exact congrArg (fun t : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) => ((t : ↥K) : LaurentSeries L)) h
  have hfPρ : fP.comp ρ.toRingHom = (algebraMap ↥K_M (LaurentSeries L)).comp (algebraMap _ ↥K_M) :=
    RingHom.ext fun r => hρ r
  have hfNi : fN.comp ι_M.toRingHom = (algebraMap ↥K_M (LaurentSeries L)).comp (algebraMap _ ↥K_M) :=
    RingHom.ext fun r => hι_M r
  have hfQι : fQ.comp ι.toRingHom = fP := RingHom.ext fun x => hι x
  have hfQρ' : fQ.comp ρ'.toRingHom = fN := RingHom.ext fun y => hρ' y

  have hleMK' : K_M ≤ K' := hleMK.trans hle
  let AKf : IntermediateField ↥K_M (LaurentSeries L) := IntermediateField.extendScalars hleMK
  let BKf : IntermediateField ↥K_M (LaurentSeries L) := IntermediateField.extendScalars hleMN
  let CKf : IntermediateField ↥K_M (LaurentSeries L) := IntermediateField.extendScalars hleMK'
  have hAC : AKf ≤ CKf := (IntermediateField.extendScalars_le_extendScalars_iff _ _).2 hle
  have hBC : BKf ≤ CKf := (IntermediateField.extendScalars_le_extendScalars_iff _ _).2 hleNK'
  have hsup' : AKf ⊔ BKf = CKf := by
    apply le_antisymm (sup_le hAC hBC)
    rw [IntermediateField.extendScalars_sup]
    exact (IntermediateField.extendScalars_le_extendScalars_iff _ _).2 hsup.ge

  haveI hfdC : FiniteDimensional ↥K_M ↥(IntermediateField.extendScalars hleMK') := by
    let Lj : IntermediateField L ↥K' := IntermediateField.adjoin L ({j'} : Set ↥K')
    have hLj : ∀ x : ↥K', x ∈ Lj → ((x : LaurentSeries L)) ∈ K_M := by
      intro x hx
      induction hx using IntermediateField.adjoin_induction with
      | mem x hx =>
          rw [Set.mem_singleton_iff] at hx
          subst hx
          rw [hj', ← hj_M]
          exact j_M.2
      | algebraMap c => exact K_M.algebraMap_mem c
      | add x y _ _ hx hy => exact K_M.add_mem hx hy
      | inv x _ hx => exact K_M.inv_mem hx
      | mul x y _ _ hx hy => exact K_M.mul_mem hx hy
    let φ : ↥Lj →+* ↥K_M :=
      { toFun := fun x => ⟨((x : ↥K') : LaurentSeries L), hLj x x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    letI : Algebra ↥Lj ↥K_M := φ.toAlgebra
    letI : Module ↥Lj ↥(IntermediateField.extendScalars hleMK') :=
      Module.compHom ↥(IntermediateField.extendScalars hleMK') φ
    haveI : IsScalarTower ↥Lj ↥K_M ↥(IntermediateField.extendScalars hleMK') :=
      ⟨fun x c v => mul_smul (φ x) c v⟩
    let e : ↥K' ≃ₗ[↥Lj] ↥(IntermediateField.extendScalars hleMK') :=
      { toFun := fun v => ⟨v.1, v.2⟩
        invFun := fun v => ⟨v.1, v.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun x v => Subtype.ext rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    haveI : Module.Finite ↥Lj ↥(IntermediateField.extendScalars hleMK') := Module.Finite.equiv e
    exact Module.Finite.of_restrictScalars_finite ↥Lj ↥K_M ↥(IntermediateField.extendScalars hleMK')
  haveI hfdA : FiniteDimensional ↥K_M ↥AKf :=
    Module.Finite.of_injective (IntermediateField.inclusion hAC).toLinearMap (IntermediateField.inclusion_injective hAC)
  haveI hfdB : FiniteDimensional ↥K_M ↥BKf :=
    Module.Finite.of_injective (IntermediateField.inclusion hBC).toLinearMap (IntermediateField.inclusion_injective hBC)
  have hfr : Module.finrank ↥K_M ↥(AKf ⊔ BKf) = Module.finrank ↥K_M ↥AKf * Module.finrank ↥K_M ↥BKf := by
    rw [hsup']
    show Module.finrank ↥K_M ↥(IntermediateField.extendScalars hleMK') =
      Module.finrank ↥K_M ↥(IntermediateField.extendScalars hleMK) * Module.finrank ↥K_M ↥(IntermediateField.extendScalars hleMN)
    rw [← IntermediateField.relfinrank_eq_finrank_of_le, ← IntermediateField.relfinrank_eq_finrank_of_le,
      ← IntermediateField.relfinrank_eq_finrank_of_le, ← hdeg, IntermediateField.relfinrank_mul_relfinrank hleMK hle]
  have hLDf : AKf.LinearDisjoint BKf := IntermediateField.LinearDisjoint.of_finrank_sup hfr
  have hLD : AKf.toSubalgebra.LinearDisjoint BKf.toSubalgebra := IntermediateField.linearDisjoint_iff'.mp hLDf

  have hP : ∀ x, fP x ∈ AKf.toSubalgebra := fun x => (x : ↥K).2
  have hN : ∀ y, fN y ∈ BKf.toSubalgebra := fun y => (y : ↥K_N).2
  have hK : ∀ k ∈ AKf.toSubalgebra, ∃ a b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), b ≠ 0 ∧ k * fP b = fP a := by
    intro k hk
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) (⟨k, hk⟩ : ↥K)
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    refine ⟨a, b, hb0, ?_⟩
    have hbK : (algebraMap _ ↥K b) ≠ 0 := fun h => hb0 (Subtype.ext h)
    have := congrArg (fun t : ↥K => (t : LaurentSeries L)) ((div_eq_iff hbK).mp hab)
    rw [hfP_apply, hfP_apply]
    exact this.symm
  have hKN : ∀ n ∈ BKf.toSubalgebra, ∃ c d : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N), d ≠ 0 ∧ n * fN d = fN c := by
    intro n hn
    obtain ⟨c, d, hd, hcd⟩ := IsFractionRing.div_surjective (A := ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K_N) j_N)) (⟨n, hn⟩ : ↥K_N)
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    refine ⟨c, d, hd0, ?_⟩
    have hdK : (algebraMap _ ↥K_N d) ≠ 0 := fun h => hd0 (Subtype.ext h)
    have := congrArg (fun t : ↥K_N => (t : LaurentSeries L)) ((div_eq_iff hdK).mp hcd)
    rw [hfN_apply, hfN_apply]
    exact this.symm
  have hQsup : ∀ z, fQ z ∈ AKf.toSubalgebra ⊔ BKf.toSubalgebra := by
    intro z
    rw [← IntermediateField.sup_toSubalgebra_of_right, hsup']
    exact (z : ↥K').2
  have hQint : ∀ z, fP.IsIntegralElem (fQ z) := by
    intro z
    have hz : IsIntegral ↥(Algebra.adjoin A ({j'} : Set ↥K')) (z : ↥K') :=
      (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff A (↥K')).mp z.2
    obtain ⟨q, hqm, hqz⟩ := hz
    let c : ↥(Algebra.adjoin A ({j'} : Set ↥K')) →+* LaurentSeries L :=
      (algebraMap ↥K' (LaurentSeries L)).comp (algebraMap ↥(Algebra.adjoin A ({j'} : Set ↥K')) ↥K')
    have hqz' : (q.map c).eval (fQ z) = 0 := by
      rw [Polynomial.eval_map, hfQ_apply]
      have h := congrArg (algebraMap ↥K' (LaurentSeries L)) hqz
      rwa [Polynomial.hom_eval₂, map_zero] at h
    have hrange : ∀ x : ↥K', x ∈ Algebra.adjoin A ({j'} : Set ↥K') → (x : LaurentSeries L) ∈ Set.range fP := by
      intro x hx
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
          rw [Set.mem_singleton_iff] at hx
          subst hx
          refine ⟨AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j, ?_⟩
          rw [hfP_apply, AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin, hj, hj']
      | algebraMap a =>
          refine ⟨algebraMap A _ a, ?_⟩
          rw [hfP_apply, Subalgebra.coe_algebraMap,
            IsScalarTower.algebraMap_apply A L ↥K, IsScalarTower.algebraMap_apply A L ↥K']
          rfl
      | add x y _ _ hx hy =>
          obtain ⟨a, ha⟩ := hx
          obtain ⟨b, hb⟩ := hy
          exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩
      | mul x y _ _ hx hy =>
          obtain ⟨a, ha⟩ := hx
          obtain ⟨b, hb⟩ := hy
          exact ⟨a * b, by rw [map_mul, ha, hb]; rfl⟩
    have hcoef : q.map c ∈ Polynomial.lifts fP := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      exact hrange _ (q.coeff n).2
    obtain ⟨pP, hpP, -, hpPm⟩ := Polynomial.lifts_and_degree_eq_and_monic hcoef (hqm.map c)
    refine ⟨pP, hpPm, ?_⟩
    rw [← Polynomial.eval_map, hpP]
    exact hqz'
  exact isPushout_of_etale_of_linearDisjoint ι_M.toRingHom ρ.toRingHom ρ'.toRingHom ι.toRingHom hsq hρinj hfinMN hetMN
    fP fN fQ hfP hfN hfQ hfPρ hfNi hfQι hfQρ' AKf.toSubalgebra BKf.toSubalgebra hLD hP hN hK hKN hQsup hQint

end S_ModularCurve_XOneP_isPushout_chartAlgFin_levelRaise_twoChartIntegralModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_isPushout_chartAlgFin_levelRaise_twoChartIntegralModel_x1_mul (solution)
