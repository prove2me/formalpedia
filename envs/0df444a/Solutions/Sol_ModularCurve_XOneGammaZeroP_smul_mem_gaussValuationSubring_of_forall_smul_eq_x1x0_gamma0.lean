-- Prove2me | solution 1 for ModularCurve.XOneGammaZeroP.smul_mem_gaussValuationSubring_of_forall_smul_eq_x1x0_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/8f4a47ae-0adf-54d3-9d45-f3e603c6d0cb

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_SupersingularModuli

import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_valuationSubring_adjoin_isDiscreteValuationRing_mem_iff_of_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem
import Theorems.Thm_ModularCurve_coeffEmb_jq_mem_laurentBaseChange_x1FunctionField
import Theorems.Thm_ModularCurve_laurentBaseChange_mono
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_exists_mulSemiringAction_faithful_fixed_iff_x1x0FunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_XOneGammaZeroP_finrank_residueField_valuationSubring_eq_finrank_and_isSeparable_of_gauss_x1x0_gamma0
import Theorems.Thm_IsDiscreteValuationRing_valuationSubring_eq_of_finrank_le_finrank_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneGammaZeroP_smul_mem_gaussValuationSubring_of_forall_smul_eq_x1x0_gamma0
p2m_attr_erase "instance" "IsLocalRing.ResidueField.instModule"
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex WeierstrassCurve.Affine.Point.instFinite instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup AlgebraicCurve.CurveModel.algebraAdjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.jqNModC_one CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply"
p2m_attr_erase "simp" "GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice"
p2m_attr_erase "simp" "PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ"
p2m_attr_erase "simp" "ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate"
p2m_attr_erase "simp" "ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

open scoped Pointwise

namespace GsAux

theorem inv_not_mem_of_mem_nonunits {E : Type*} [Field E] (V : ValuationSubring E) {x : E}
    (hx : x ∈ V.nonunits) (hx0 : x ≠ 0) : x⁻¹ ∉ V := by
  intro hinv
  rw [ValuationSubring.mem_nonunits_iff] at hx
  have hle : V.valuation x⁻¹ ≤ 1 := (V.valuation_le_one_iff _).mpr hinv
  have : V.valuation (x * x⁻¹) < 1 := by
    rw [map_mul]
    calc V.valuation x * V.valuation x⁻¹ ≤ V.valuation x * 1 := mul_le_mul_right hle _
      _ < 1 := by rw [mul_one]; exact hx
  rw [mul_inv_cancel₀ hx0, map_one] at this
  exact lt_irrefl _ this

theorem mem_of_isIntegral {O E : Type*} [CommRing O] [Field E] [Algebra O E]
    (V : ValuationSubring E) (hOV : ∀ x : O, algebraMap O E x ∈ V)
    {y : E} (hy : IsIntegral O y) : y ∈ V := by
  let φ : O →+* ↥V := (algebraMap O E).codRestrict V.toSubring hOV
  have hy' : IsIntegral ↥V y := by
    obtain ⟨q, hq, hqy⟩ := hy
    refine ⟨q.map φ, hq.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hqy
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥V) (K := E)).mp hy'
  rw [← hz]
  exact z.2

theorem mem_nonunits_iff' {F : Type*} [Field F] (A : ValuationSubring F) (x : F) :
    x ∈ A.nonunits ↔ x ∈ A ∧ (x = 0 ∨ x⁻¹ ∉ A) := by
  rw [ValuationSubring.mem_nonunits_iff]
  by_cases hx : x = 0
  · subst hx
    simp [A.zero_mem]
  · constructor
    · intro h
      refine ⟨(A.valuation_le_one_iff x).mp h.le, Or.inr ?_⟩
      intro hinv
      have h1 : A.valuation x⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr hinv
      rw [map_inv₀] at h1
      have hx' : A.valuation x ≠ 0 := (map_ne_zero _).mpr hx
      have : 1 ≤ A.valuation x := by
        rwa [inv_le_one₀ (zero_lt_iff.mpr hx')] at h1
      exact absurd h (not_lt.mpr this)
    · rintro ⟨-, h0 | hinv⟩
      · exact absurd h0 hx
      · by_contra hlt
        apply hinv
        rw [← A.valuation_le_one_iff, map_inv₀]
        have hx' : A.valuation x ≠ 0 := (map_ne_zero _).mpr hx
        rw [inv_le_one₀ (zero_lt_iff.mpr hx')]
        exact not_lt.mp hlt

theorem mem_nonunits_pointwise_smul_iff {F : Type*} [Field F] {G : Type*} [Group G] [MulSemiringAction G F]
    (g : G) (A : ValuationSubring F) (x : F) :
    x ∈ (g • A).nonunits ↔ g⁻¹ • x ∈ A.nonunits := by
  rw [mem_nonunits_iff', mem_nonunits_iff', ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, smul_inv'', smul_eq_zero_iff_eq]

end GsAux

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]

    (W₀ : ValuationSubring ↥K₁)
    (hW₀ : ∀ f : ↥K₁, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (G : Type) [Group G] [Fintype G] [MulSemiringAction G ↥K₁]
    (hGfixK : ∀ (g : G) (x : ↥K₁), (x : LaurentSeries L) ∈ K₂ → g • x = x) :
    ∀ (g : G) (f : ↥K₁), f ∈ W₀ → g • f ∈ W₀ := by
  classical
  intro g f hf
  have hp : p.Prime := Fact.out

  have hΓ : CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p ≤ CongruenceSubgroup.Gamma0 (M * p) := by
    intro γ hγ
    obtain ⟨h1, h0⟩ := Subgroup.mem_inf.mp hγ
    rw [CongruenceSubgroup.Gamma1_mem] at h1
    rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
    have hM : (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp h1.2.2
    have hP : (p : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h0
    have hcop : IsCoprime (M : ℤ) (p : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM))
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact hcop.mul_dvd hM hP
  have hle : K₂ ≤ K₁ := by
    rw [hK₁, hK₂]
    exact ModularCurve.laurentBaseChange_mono L (ModularCurve.qExpFunctionFieldC_mono ℚ hΓ)

  have hΓ1 : CongruenceSubgroup.Gamma0 (M * p) ≤ CongruenceSubgroup.Gamma1 1 := by
    intro γ _
    rw [CongruenceSubgroup.Gamma1_mem]
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hjK₂ : ModularCurve.coeffEmb L ModularCurve.jq ∈ K₂ := by
    rw [hK₂]
    exact ModularCurve.laurentBaseChange_mono L (ModularCurve.qExpFunctionFieldC_mono ℚ hΓ1)
      (ModularCurve.coeffEmb_jq_mem_laurentBaseChange_x1FunctionField L 1)
  let j₂ : ↥K₂ := ⟨ModularCurve.coeffEmb L ModularCurve.jq, hjK₂⟩
  let j₁ : ↥K₁ := ⟨ModularCurve.coeffEmb L ModularCurve.jq, hle hjK₂⟩
  have hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq := rfl
  have hj₁ : ((j₁ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq := rfl
  letI algAK₂ : Algebra A ↥K₂ := ((algebraMap L ↥K₂).comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L ↥K₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have htr₂ : Transcendental A j₂ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₂ A j₂ hj₂
  have htr₁ : Transcendental A j₁ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₁ A j₁ hj₁
  haveI : Fact (j₂ ≠ 0) := ⟨fun h => htr₂ (h ▸ isAlgebraic_zero)⟩
  haveI : Fact (j₁ ≠ 0) := ⟨fun h => htr₁ (h ▸ isAlgebraic_zero)⟩

  let ι₂ : ↥K₂ →+* ↥K₁ := (IntermediateField.inclusion hle).toRingHom
  have hι₂ : ∀ y : ↥K₂, ((ι₂ y : ↥K₁) : LaurentSeries L) = (y : LaurentSeries L) := fun _ => rfl
  have hgι : ∀ y : ↥K₂, g • ι₂ y = ι₂ y := fun y => hGfixK g (ι₂ y) (by rw [hι₂]; exact y.2)
  set O : ValuationSubring ↥K₂ := W₀.comap ι₂ with hOdef
  have hmemO : ∀ y : ↥K₂, y ∈ O ↔ ι₂ y ∈ W₀ := fun _ => ValuationSubring.mem_comap
  obtain ⟨U₂, hU1, hU2, hU3, hU4, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
      (CongruenceSubgroup.Gamma0 (M * p)) L K₂ hK₂ A j₂ hj₂
  have hOU : O = U₂ := by
    ext y
    rw [hmemO, hW₀, hU1]
    rfl
  have hAO : ∀ a : A, algebraMap A ↥K₂ a ∈ O := fun a => hOU ▸ hU2 a
  have hmO : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K₂ a ∈ O.nonunits := fun a ha => hOU ▸ hU3 a ha
  have hpO : algebraMap A ↥K₂ (p : A) ∈ O.nonunits := hmO _ hAp
  have hp0 : algebraMap A ↥K₂ (p : A) ≠ 0 := by
    intro h0
    have h1 := congrArg (fun x : ↥K₂ => (x : LaurentSeries L)) h0
    simp only [ZeroMemClass.coe_zero] at h1
    have h2 : ((algebraMap A ↥K₂ (p : A) : ↥K₂) : LaurentSeries L) = algebraMap L (LaurentSeries L) (p : L) := by
      show ((algebraMap L ↥K₂ (algebraMap A L (p : A)) : ↥K₂) : LaurentSeries L) = _
      rw [map_natCast]
      first
        | rfl
        | exact IntermediateField.coe_algebraMap_apply K₂ _
    rw [h2] at h1
    have h3 : ((p : ℕ) : L) = 0 := (algebraMap L (LaurentSeries L)).injective (h1.trans (map_zero _).symm)
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) h3
  have hOtop : O ≠ ⊤ := fun h => GsAux.inv_not_mem_of_mem_nonunits O hpO hp0 (h ▸ Subring.mem_top _)

  obtain ⟨OE, hOE1, hOE2, -, -, -⟩ :=
    ModularCurve.exists_valuationSubring_adjoin_isDiscreteValuationRing_mem_iff_of_laurentBaseChange_qExpFunctionFieldC
      (CongruenceSubgroup.Gamma0 (M * p)) L K₂ hK₂ A j₂ hj₂ U₂ hU1
  haveI := hOE1
  have hTΓ : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (M * p) := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp.ne_zero⟩
  haveI hFD₂ := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma0 (M * p)) hTΓ L K₂ hK₂ j₂ hj₂
  haveI hOdvr : IsDiscreteValuationRing ↥O := by
    let F₂ := ↥(IntermediateField.adjoin L ({j₂} : Set ↥K₂))
    letI : Algebra ↥OE ↥K₂ := ((algebraMap F₂ ↥K₂).comp (algebraMap ↥OE F₂)).toAlgebra
    haveI : IsScalarTower ↥OE F₂ ↥K₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : CharZero F₂ := charZero_of_injective_algebraMap (algebraMap L F₂).injective
    haveI : Algebra.IsSeparable F₂ ↥K₂ := Algebra.IsSeparable.of_integral _ _
    haveI : IsDedekindDomain ↥(integralClosure ↥OE ↥K₂) := integralClosure.isDedekindDomain ↥OE F₂ ↥K₂
    haveI : IsFractionRing ↥(integralClosure ↥OE ↥K₂) ↥K₂ := integralClosure.isFractionRing_of_finite_extension F₂ ↥K₂
    have hOEO : ∀ x : ↥OE, algebraMap ↥OE ↥K₂ x ∈ O := fun x => by
      rw [hOU]; exact (hOE2 _).mp x.2
    have hRO : ∀ r : ↥(integralClosure ↥OE ↥K₂), algebraMap _ ↥K₂ r ∈ O := fun r =>
      GsAux.mem_of_isIntegral O hOEO r.2
    obtain ⟨v₁, hOeq, -⟩ := ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem O hRO hOtop
    have : IsDiscreteValuationRing ↥(v₁.valuationSubringAtPrime ↥K₂) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ↥(integralClosure ↥OE ↥K₂) v₁.ne_bot _
    rw [hOeq]; exact this

  letI algK : Algebra ↥K₂ ↥K₁ := ι₂.toAlgebra
  have halgK : ∀ y : ↥K₂, algebraMap ↥K₂ ↥K₁ y = ι₂ y := fun _ => rfl
  letI algOK : Algebra ↥O ↥K₁ := ((algebraMap ↥K₂ ↥K₁).comp (algebraMap ↥O ↥K₂)).toAlgebra
  haveI : IsScalarTower ↥O ↥K₂ ↥K₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul ↥O ↥K₁ := (faithfulSMul_iff_algebraMap_injective ↥O ↥K₁).mpr
    ((IntermediateField.inclusion hle).injective.comp Subtype.val_injective)
  haveI : FiniteDimensional ↥K₂ ↥K₁ := by
    obtain ⟨G', iG, iF, iA, -, hfix, hinv⟩ :=
      ModularCurve.exists_mulSemiringAction_faithful_fixed_iff_x1x0FunctionFieldC_gamma0 p M hM hpM L K₁ hK₁ K₂ hK₂ hle
    letI := iG; letI := iF; letI := iA
    haveI : Finite G' := Finite.of_fintype G'
    let S : Subfield ↥K₁ := FixedPoints.subfield G' ↥K₁
    haveI hSfin : FiniteDimensional ↥S ↥K₁ := inferInstance

    let e : ↥K₂ →+* ↥S :=
      { toFun := fun y => ⟨ι₂ y, fun g' => hfix g' (ι₂ y) (by rw [hι₂]; exact y.2)⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun a b => Subtype.ext (map_mul _ a b)
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun a b => Subtype.ext (map_add _ a b) }
    have hesurj : Function.Surjective e := by
      intro x
      have hx : ((x : ↥K₁) : LaurentSeries L) ∈ K₂ := hinv x (fun g' => x.2 g')
      exact ⟨⟨_, hx⟩, Subtype.ext (Subtype.ext rfl)⟩
    letI : Algebra ↥K₂ ↥S := e.toAlgebra
    haveI : IsScalarTower ↥K₂ ↥S ↥K₁ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : Module.Finite ↥K₂ ↥S := Module.Finite.of_surjective (Algebra.linearMap ↥K₂ ↥S) hesurj
    exact Module.Finite.trans ↥S ↥K₁
  haveI : CharZero ↥K₂ := charZero_of_injective_algebraMap (algebraMap L ↥K₂).injective
  haveI : Algebra.IsSeparable ↥K₂ ↥K₁ := Algebra.IsSeparable.of_integral _ _

  have hOW : ∀ x : ↥O, algebraMap ↥O ↥K₁ x ∈ W₀ := fun x => (hmemO _).mp x.2
  have hmW : ∀ x ∈ IsLocalRing.maximalIdeal ↥O, algebraMap ↥O ↥K₁ x ∈ W₀.nonunits := by
    intro x hx
    have hxO : ((x : ↥K₂) : ↥K₂) ∈ O.nonunits := ValuationSubring.coe_mem_nonunits_iff.mpr hx
    rw [ValuationSubring.mem_nonunits_iff] at hxO ⊢
    by_cases hx0 : (x : ↥K₂) = 0
    · have : algebraMap ↥O ↥K₁ x = 0 := by
        show ι₂ (x : ↥K₂) = 0
        rw [hx0, map_zero]
      rw [this, map_zero]; exact zero_lt_one
    by_contra hge
    push_neg at hge
    have hinv : (x : ↥K₂)⁻¹ ∉ O := GsAux.inv_not_mem_of_mem_nonunits O ((ValuationSubring.mem_nonunits_iff O).mpr hxO) hx0
    apply hinv
    rw [hmemO, map_inv₀, ← W₀.valuation_le_one_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hge
  have hW₀top : W₀ ≠ ⊤ := by
    intro h
    have := hmW ⟨algebraMap A ↥K₂ (p : A), hAO _⟩ ((ValuationSubring.coe_mem_nonunits_iff).mp hpO)
    rw [h, ValuationSubring.mem_nonunits_iff] at this

    have hne : algebraMap ↥O ↥K₁ ⟨algebraMap A ↥K₂ (p : A), hAO _⟩ ≠ 0 := by
      show ι₂ (algebraMap A ↥K₂ (p : A)) ≠ 0
      exact fun h0 => hp0 ((injective_iff_map_eq_zero ι₂).mp (IntermediateField.inclusion hle).injective _ h0)
    have h1 : ((⊤ : ValuationSubring ↥K₁)).valuation (algebraMap ↥O ↥K₁ ⟨algebraMap A ↥K₂ (p : A), hAO _⟩)⁻¹ ≤ 1 :=
      ((⊤ : ValuationSubring ↥K₁).valuation_le_one_iff _).mpr (Subring.mem_top _)
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((map_ne_zero _).mpr hne))] at h1
    exact absurd this (not_lt.mpr h1)

  let ψ : ↥O →+* ↥K₁ := ι₂.comp O.subtype
  have hψ : ∀ u : ↥O, ψ u = ι₂ (u : ↥K₂) := fun _ => rfl
  let φOW : ↥O →+* ↥W₀ :=
    { toFun := fun u => ⟨ψ u, (hmemO _).mp u.2⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun a b => Subtype.ext (map_mul ψ a b)
      map_zero' := Subtype.ext (map_zero ψ)
      map_add' := fun a b => Subtype.ext (map_add ψ a b) }
  haveI : IsLocalHom φOW := by
    refine ⟨fun u hu => ?_⟩
    by_contra hnu
    have hmem : u ∈ IsLocalRing.maximalIdeal ↥O := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h1 : ι₂ (u : ↥K₂) ∈ W₀.nonunits := hmW u hmem
    have h2 : ((φOW u : ↥W₀) : ↥K₁) ∈ W₀.nonunits := h1
    rw [ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal] at h2
    exact h2 hu
  letI algOW : Algebra ↥O ↥W₀ := φOW.toAlgebra
  have halg : ∀ x : ↥O, ((algebraMap ↥O ↥W₀ x : ↥W₀) : ↥K₁) = algebraMap ↥O ↥K₁ x := fun _ => rfl
  letI algRes : Algebra (IsLocalRing.ResidueField ↥O) (IsLocalRing.ResidueField ↥W₀) :=
    (IsLocalRing.ResidueField.map φOW).toAlgebra
  have hres : ∀ x : ↥O, algebraMap (IsLocalRing.ResidueField ↥O) (IsLocalRing.ResidueField ↥W₀)
      (IsLocalRing.residue ↥O x) = IsLocalRing.residue ↥W₀ (algebraMap ↥O ↥W₀ x) := fun _ => rfl

  obtain ⟨U₁, hU₁1, hU₁2, hU₁3, hU₁4, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
      (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p) L K₁ (by rw [hK₁]; rfl) A j₁ hj₁
  have hWU : W₀ = U₁ := ValuationSubring.ext _ _ (fun f => (hW₀ f).trans (hU₁1 f).symm)
  have hVA : ∀ a : A, algebraMap A ↥K₁ a ∈ W₀ := fun a => hWU ▸ hU₁2 a
  have hVm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K₁ a ∈ W₀.nonunits := fun a ha => hWU ▸ hU₁3 a ha
  have hVj : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j₁ P ∈ W₀ ∧ (Polynomial.aeval j₁ P)⁻¹ ∈ W₀ := fun P hP => hWU ▸ hU₁4 P hP
  have halgV : ∀ y : ↥O, (((algebraMap ↥O ↥W₀ y : ↥W₀) : ↥K₁)) = ι₂ (y : ↥K₂) := fun _ => rfl
  obtain ⟨hfin, -⟩ :=
    ModularCurve.XOneGammaZeroP.finrank_residueField_valuationSubring_eq_finrank_and_isSeparable_of_gauss_x1x0_gamma0
      p M hM hpM L ζ hζ K₁ hK₁ K₂ hK₂ ι₂ hι₂ A hAp hζA j₁ hj₁ W₀ hVA hVm hVj O hmemO halgV hres

  have hrel : IntermediateField.relfinrank K₂ K₁ = Module.finrank ↥K₂ ↥K₁ := by
    rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
    let eKE : ↥(IntermediateField.extendScalars hle) ≃ₗ[↥K₂] ↥K₁ :=
      { toFun := fun x => ⟨(x : LaurentSeries L), (IntermediateField.mem_extendScalars hle).mp x.2⟩
        invFun := fun x => ⟨(x : LaurentSeries L), (IntermediateField.mem_extendScalars hle).mpr x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact eKE.finrank_eq
  have hfr : Module.finrank ↥K₂ ↥K₁ ≤ Module.finrank (IsLocalRing.ResidueField ↥O) (IsLocalRing.ResidueField ↥W₀) := by
    rw [hfin, hrel]

  have huniq := IsDiscreteValuationRing.valuationSubring_eq_of_finrank_le_finrank_residueField
    (O := ↥O) (F := ↥K₁) ↥K₂ W₀ hW₀top hOW hmW halg hres hfr
  have hgW_O : ∀ x : ↥O, algebraMap ↥O ↥K₁ x ∈ g • W₀ := by
    intro x
    show ι₂ (x : ↥K₂) ∈ g • W₀
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have : g⁻¹ • ι₂ (x : ↥K₂) = ι₂ x := by rw [inv_smul_eq_iff, hgι]
    rw [this]
    exact (hmemO _).mp x.2
  have hgWnu : ∀ x ∈ IsLocalRing.maximalIdeal ↥O, algebraMap ↥O ↥K₁ x ∈ (g • W₀).nonunits := by
    intro x hx
    show ι₂ (x : ↥K₂) ∈ (g • W₀).nonunits
    rw [GsAux.mem_nonunits_pointwise_smul_iff]
    have : g⁻¹ • ι₂ (x : ↥K₂) = ι₂ x := by rw [inv_smul_eq_iff, hgι]
    rw [this]
    exact hmW x hx
  have hgWtop : g • W₀ ≠ ⊤ := by
    intro h
    apply hW₀top
    have := congrArg (fun W : ValuationSubring ↥K₁ => g⁻¹ • W) h
    simp only [inv_smul_smul] at this
    rw [this]
    ext x
    simp [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_top]
  have hEq : g • W₀ = W₀ := huniq (g • W₀) hgWtop hgW_O hgWnu
  have : g • f ∈ g • W₀ := ValuationSubring.smul_mem_pointwise_smul g f W₀ hf
  rwa [hEq] at this

end S_ModularCurve_XOneGammaZeroP_smul_mem_gaussValuationSubring_of_forall_smul_eq_x1x0_gamma0
end P2MW
export P2MW.S_ModularCurve_XOneGammaZeroP_smul_mem_gaussValuationSubring_of_forall_smul_eq_x1x0_gamma0 (solution)
