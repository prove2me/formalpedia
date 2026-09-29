-- Prove2me | solution 1 for ModularCurve.XOneGammaZeroP.finrank_residueField_valuationSubring_eq_finrank_and_isSeparable_of_gauss_x1x0_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8cde9181-82ce-5c5e-8a55-c059de9589ba

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_XOneGammaZeroP_valuationSubring_eq_or_eq_comap_and_uniformizer_and_gaussReduction_eq_x1x0
import Theorems.Thm_ModularCurve_XZeroP_valuationSubring_eq_or_eq_comap_and_uniformizer_and_gaussReduction_eq_gamma0_mul
import Theorems.Thm_ModularCurve_chartAlgFin_iff_and_comap_ne_and_aeval_mem_comap_of_algEquiv_map_j_eq_qExpand
import Theorems.Thm_ModularCurve_XOneGammaZeroP_exists_algEquiv_pair_map_j_eq_qExpand_and_coe_comp_eq_x1x0_gamma0
import Theorems.Thm_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
import Theorems.Thm_ModularCurve_exists_mulSemiringAction_faithful_fixed_iff_card_eq_index_qExpFunctionFieldC_gamma1_gamma0_charP
import Theorems.Thm_ModularCurve_relfinrank_laurentBaseChange_gamma0_mul_x1x0FunctionFieldC_eq_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneGammaZeroP_finrank_residueField_valuationSubring_eq_finrank_and_isSeparable_of_gauss_x1x0_gamma0
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.CurveModel.algebraAdjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit"
p2m_attr_erase "simp" "ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false

open IsLocalRing in

theorem T5vCore.finrank_residueField_eq_card_and_isSeparable
    {κ E : Type*} [Field κ] [Field E] [Algebra κ E]
    {R₂ R₁ : Type*} [CommRing R₂] [IsLocalRing R₂] [CommRing R₁] [IsLocalRing R₁]
    [Algebra R₂ R₁] [Algebra (ResidueField R₂) (ResidueField R₁)]
    (hres : ∀ y : R₂, algebraMap (ResidueField R₂) (ResidueField R₁) (residue R₂ y) = residue R₁ (algebraMap R₂ R₁ y))
    (red₁ : R₁ →+* E) (hker₁ : RingHom.ker red₁ = maximalIdeal R₁)
    (red₂ : R₂ →+* E) (hker₂ : RingHom.ker red₂ = maximalIdeal R₂)
    (hcomp : ∀ y : R₂, red₁ (algebraMap R₂ R₁ y) = red₂ y)
    (F₀ F₁ : IntermediateField κ E) (hle : F₀ ≤ F₁)
    (hF₁ : ∀ z : E, z ∈ F₁ ↔ ∃ r : R₁, red₁ r = z) (hF₀ : ∀ z : E, z ∈ F₀ ↔ ∃ r : R₂, red₂ r = z)
    (G : Type*) [Group G] [Fintype G] [MulSemiringAction G ↥F₁] [FaithfulSMul G ↥F₁]
    (hGfix : ∀ (g : G) (x : ↥F₁), (x : E) ∈ F₀ → g • x = x)
    (hGinv : ∀ x : ↥F₁, (∀ g : G, g • x = x) → (x : E) ∈ F₀) :
    Module.finrank (ResidueField R₂) (ResidueField R₁) = Fintype.card G ∧
      Algebra.IsSeparable (ResidueField R₂) (ResidueField R₁) := by
  classical

  have hk₁ : ∀ a ∈ maximalIdeal R₁, red₁ a = 0 := fun a ha => by
    rw [← RingHom.mem_ker, hker₁]; exact ha
  have hk₂ : ∀ a ∈ maximalIdeal R₂, red₂ a = 0 := fun a ha => by
    rw [← RingHom.mem_ker, hker₂]; exact ha
  let l₁ : ResidueField R₁ →+* E := Ideal.Quotient.lift (maximalIdeal R₁) red₁ hk₁
  let l₂ : ResidueField R₂ →+* E := Ideal.Quotient.lift (maximalIdeal R₂) red₂ hk₂
  have hl₁ : ∀ r : R₁, l₁ (residue R₁ r) = red₁ r := fun r => Ideal.Quotient.lift_mk _ _ _
  have hl₂ : ∀ r : R₂, l₂ (residue R₂ r) = red₂ r := fun r => Ideal.Quotient.lift_mk _ _ _
  have hl₁mem : ∀ w, l₁ w ∈ F₁ := fun w => by
    obtain ⟨r, rfl⟩ := residue_surjective w
    rw [hl₁]; exact (hF₁ _).mpr ⟨r, rfl⟩
  have hl₂mem : ∀ w, l₂ w ∈ F₀ := fun w => by
    obtain ⟨r, rfl⟩ := residue_surjective w
    rw [hl₂]; exact (hF₀ _).mpr ⟨r, rfl⟩
  let c₁ : ResidueField R₁ →+* ↥F₁ := (l₁).codRestrict F₁ hl₁mem
  let c₂ : ResidueField R₂ →+* ↥F₀ := (l₂).codRestrict F₀ hl₂mem
  have hc₁ : Function.Bijective c₁ := by
    refine ⟨c₁.injective, fun z => ?_⟩
    obtain ⟨r, hr⟩ := (hF₁ _).mp z.2
    exact ⟨residue R₁ r, Subtype.ext (by rw [← hr, ← hl₁ r]; rfl)⟩
  have hc₂ : Function.Bijective c₂ := by
    refine ⟨c₂.injective, fun z => ?_⟩
    obtain ⟨r, hr⟩ := (hF₀ _).mp z.2
    exact ⟨residue R₂ r, Subtype.ext (by rw [← hr, ← hl₂ r]; rfl)⟩
  let eκ₁ : ResidueField R₁ ≃+* ↥F₁ := RingEquiv.ofBijective c₁ hc₁
  let eκ₂ : ResidueField R₂ ≃+* ↥F₀ := RingEquiv.ofBijective c₂ hc₂
  have heκ₁ : ∀ r : R₁, ((eκ₁ (residue R₁ r) : ↥F₁) : E) = red₁ r := fun r => hl₁ r
  have heκ₂ : ∀ r : R₂, ((eκ₂ (residue R₂ r) : ↥F₀) : E) = red₂ r := fun r => hl₂ r

  have hcompat : ∀ w : ResidueField R₂, ((eκ₁ (algebraMap (ResidueField R₂) (ResidueField R₁) w) : ↥F₁) : E) = ((eκ₂ w : ↥F₀) : E) := by
    intro w
    obtain ⟨y, rfl⟩ := residue_surjective w
    rw [hres, heκ₁, heκ₂, hcomp]

  let incl : ↥F₀ →ₐ[κ] ↥F₁ := IntermediateField.inclusion hle
  have hincl : ∀ z : ↥F₀, ((incl z : ↥F₁) : E) = (z : E) := fun _ => rfl
  let m : ↥F₀ →+* ↥(FixedPoints.subfield G ↥F₁) :=
    { toFun := fun z => ⟨incl z, fun g => hGfix g (incl z) (by rw [hincl]; exact z.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have hm : Function.Bijective m := by
    refine ⟨m.injective, fun x => ?_⟩
    have hx : ((x : ↥F₁) : E) ∈ F₀ := hGinv x (fun g => x.2 g)
    exact ⟨⟨_, hx⟩, Subtype.ext (Subtype.ext rfl)⟩
  let eG : ↥F₀ ≃+* ↥(FixedPoints.subfield G ↥F₁) := RingEquiv.ofBijective m hm
  have heG : ∀ z : ↥F₀, ((eG z : ↥(FixedPoints.subfield G ↥F₁)) : ↥F₁) = incl z := fun _ => rfl

  let e₁ : ↥(FixedPoints.subfield G ↥F₁) ≃+* ResidueField R₂ := eG.symm.trans eκ₂.symm
  let e₂ : ↥F₁ ≃+* ResidueField R₁ := eκ₁.symm
  have he : (algebraMap (ResidueField R₂) (ResidueField R₁)).comp (e₁ : ↥(FixedPoints.subfield G ↥F₁) →+* ResidueField R₂) =
      (e₂ : ↥F₁ →+* ResidueField R₁).comp (algebraMap ↥(FixedPoints.subfield G ↥F₁) ↥F₁) := by
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    apply eκ₁.injective
    apply Subtype.ext
    rw [hcompat]

    obtain ⟨z, rfl⟩ : ∃ z : ↥F₀, eG z = x := ⟨eG.symm x, eG.apply_symm_apply x⟩
    show ((eκ₂ ((eG.symm.trans eκ₂.symm) (eG z)) : ↥F₀) : E) = ((eκ₁ (eκ₁.symm (algebraMap _ ↥F₁ (eG z))) : ↥F₁) : E)
    rw [RingEquiv.trans_apply, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    show (z : E) = (((eG z : ↥(FixedPoints.subfield G ↥F₁)) : ↥F₁) : E)
    rw [heG, hincl]
  refine ⟨?_, ?_⟩
  · rw [← Algebra.finrank_eq_of_equiv_equiv e₁ e₂ he]
    exact FixedPoints.finrank_eq_card G ↥F₁
  · haveI : Algebra.IsSeparable ↥(FixedPoints.subfield G ↥F₁) ↥F₁ := inferInstance
    exact Algebra.IsSeparable.of_equiv_equiv e₁ e₂ he

namespace T5vAux
open IsLocalRing

theorem exists_intermediateField_mem_iff
    {κ E : Type*} [Field κ] [Field E] [Algebra κ E]
    {R : Type*} [CommRing R] [IsLocalRing R]
    (red : R →+* E) (hker : RingHom.ker red = maximalIdeal R)
    (hconst : ∀ c : κ, ∃ r : R, red r = algebraMap κ E c) :
    ∃ R₀ : IntermediateField κ E, ∀ z : E, z ∈ R₀ ↔ ∃ r : R, red r = z := by
  classical
  let S : Subfield E :=
    { red.range with
      inv_mem' := by
        rintro _ ⟨r, rfl⟩
        by_cases hr : red r = 0
        · exact ⟨0, by rw [hr, inv_zero, map_zero]⟩
        have hu : IsUnit r := by
          by_contra h
          exact hr (by rw [← RingHom.mem_ker, hker]; exact (mem_maximalIdeal _).mpr h)
        obtain ⟨u, rfl⟩ := hu
        exact ⟨((u⁻¹ : Rˣ) : R), eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])⟩ }
  refine ⟨S.toIntermediateField (fun c => ?_), fun z => ?_⟩
  · obtain ⟨r, hr⟩ := hconst c
    exact ⟨r, hr⟩
  · show z ∈ S ↔ _
    exact ⟨fun ⟨r, hr⟩ => ⟨r, hr⟩, fun ⟨r, hr⟩ => ⟨r, hr⟩⟩

theorem ker_comp_ringEquiv_eq_maximalIdeal
    {V W E : Type*} [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [CommRing E]
    (e : V ≃+* W) (red : W →+* E) (hker : RingHom.ker red = maximalIdeal W) :
    RingHom.ker (red.comp (e : V →+* W)) = maximalIdeal V := by
  ext x
  rw [RingHom.mem_ker, RingHom.comp_apply, RingHom.coe_coe, ← RingHom.mem_ker, hker, mem_maximalIdeal, mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff, not_iff_not]
  exact (isUnit_map_iff e x)

end T5vAux

theorem T5vAux.red_algebraMap
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (W₀ : ValuationSubring ↥K)
    (red : ↥W₀ →+* LaurentSeries (IsLocalRing.ResidueField A))
    (hred : ∀ (f : ↥W₀) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        ((f : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        red f = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)))
    (a : A) (ha : algebraMap A ↥K a ∈ W₀) :
    red ⟨algebraMap A ↥K a, ha⟩ = algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a) := by
  have h1 : (1 : PowerSeries A).map (IsLocalRing.residue A) ≠ 0 := by rw [map_one]; exact one_ne_zero
  have hcoe : (((algebraMap A ↥K a : ↥K)) : LaurentSeries L) = algebraMap L (LaurentSeries L) (algebraMap A L a) := by
    rw [IsScalarTower.algebraMap_apply A L ↥K a]
    exact (IsScalarTower.algebraMap_apply L ↥K (LaurentSeries L) _).symm
  have := hred ⟨algebraMap A ↥K a, ha⟩ (PowerSeries.C a) 1 h1 (by
    change (((algebraMap A ↥K a : ↥K)) : LaurentSeries L) * _ = _
    rw [hcoe, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    simp only [map_one, mul_one, PowerSeries.map_C])
  rw [this, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  simp only [map_one, div_one, PowerSeries.map_C]

theorem T5vAux.exists_apply_eq_iff
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (red : ↥W₀ →+* LaurentSeries (IsLocalRing.ResidueField A))
    (hred : ∀ (f : ↥W₀) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        ((f : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        red f = HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)))
    (z : LaurentSeries (IsLocalRing.ResidueField A)) :
    (∃ w : ↥W₀, red w = z) ↔ ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
          (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
          HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
            HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z := by
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨x, y, hy, hxy⟩ := (hW₀ w).mp w.2
    exact ⟨w, x, y, hy, hxy, (hred w x y hy hxy).symm⟩
  · rintro ⟨f, x, y, hy, hxy, hz⟩
    have hf : f ∈ W₀ := (hW₀ f).mpr ⟨x, y, hy, hxy⟩
    exact ⟨⟨f, hf⟩, (hred ⟨f, hf⟩ x y hy hxy).trans hz⟩

theorem T5vAux.exists_ringEquiv_of_forall_mem_iff
    {L : Type} [Field L] {F : Type} [Field F] [Algebra L F]
    (σ : F ≃ₐ[L] F) (V W₀ : ValuationSubring F) (h : ∀ f : F, f ∈ V ↔ σ f ∈ W₀) :
    ∃ e : ↥V ≃+* ↥W₀, (∀ v : ↥V, ((e v : ↥W₀) : F) = σ v) ∧ (∀ w : ↥W₀, ((e.symm w : ↥V) : F) = σ.symm w) := by
  refine ⟨{ toFun := fun v => ⟨σ v, (h _).mp v.2⟩
            invFun := fun w => ⟨σ.symm w, (h _).mpr (by rw [σ.apply_symm_apply]; exact w.2)⟩
            left_inv := fun v => Subtype.ext (σ.symm_apply_apply _)
            right_inv := fun w => Subtype.ext (σ.apply_symm_apply _)
            map_mul' := fun a b => Subtype.ext (map_mul σ _ _)
            map_add' := fun a b => Subtype.ext (map_add σ _ _) }, fun _ => rfl, fun _ => rfl⟩

open IsLocalRing in

theorem T5vAux.engine
    {κ E : Type*} [Field κ] [Field E] [Algebra κ E]
    {R₂ R₁ : Type*} [CommRing R₂] [IsLocalRing R₂] [CommRing R₁] [IsLocalRing R₁]
    [Algebra R₂ R₁] [Algebra (ResidueField R₂) (ResidueField R₁)]
    (hres : ∀ y : R₂, algebraMap (ResidueField R₂) (ResidueField R₁) (residue R₂ y) = residue R₁ (algebraMap R₂ R₁ y))
    (r₁ : R₁ →+* E) (hk₁ : RingHom.ker r₁ = maximalIdeal R₁)
    (r₂ : R₂ →+* E) (hk₂ : RingHom.ker r₂ = maximalIdeal R₂)
    (hc : ∀ y : R₂, r₁ (algebraMap R₂ R₁ y) = r₂ y)
    (hc₁ : ∀ c : κ, ∃ v, r₁ v = algebraMap κ E c) (hc₂ : ∀ c : κ, ∃ v, r₂ v = algebraMap κ E c)
    (Φ₁ Φ₂ : E → Prop) (hr₁ : ∀ z, (∃ v, r₁ v = z) ↔ Φ₁ z) (hr₂ : ∀ z, (∃ v, r₂ v = z) ↔ Φ₂ z)
    (F₁ F₀ : IntermediateField κ E)
    (hiii₁ : ∀ R : IntermediateField κ E, (∀ z, z ∈ R ↔ Φ₁ z) → R = F₁)
    (hiii₂ : ∀ R : IntermediateField κ E, (∀ z, z ∈ R ↔ Φ₂ z) → R = F₀)
    (n : ℕ)
    (hIg : ∀ (R₁' : IntermediateField κ E), R₁' = F₁ → ∀ (R₀' : IntermediateField κ E), R₀' = F₀ → R₀' ≤ R₁' →
      ∃ (G : Type) (_ : Group G) (_ : Fintype G) (_ : MulSemiringAction G ↥R₁'),
        FaithfulSMul G ↥R₁' ∧ (∀ (g : G) (x : ↥R₁'), (x : E) ∈ R₀' → g • x = x) ∧
        (∀ x : ↥R₁', (∀ g : G, g • x = x) → (x : E) ∈ R₀') ∧ Fintype.card G = n) :
    Module.finrank (ResidueField R₂) (ResidueField R₁) = n ∧ Algebra.IsSeparable (ResidueField R₂) (ResidueField R₁) := by
  classical
  obtain ⟨R₁', hR₁⟩ := T5vAux.exists_intermediateField_mem_iff r₁ hk₁ hc₁
  obtain ⟨R₀', hR₀⟩ := T5vAux.exists_intermediateField_mem_iff r₂ hk₂ hc₂
  have h₁ : R₁' = F₁ := hiii₁ R₁' (fun z => (hR₁ z).trans (hr₁ z))
  have h₀ : R₀' = F₀ := hiii₂ R₀' (fun z => (hR₀ z).trans (hr₂ z))
  have hle : R₀' ≤ R₁' := fun z hz => by
    obtain ⟨v, rfl⟩ := (hR₀ z).mp hz
    exact (hR₁ _).mpr ⟨_, hc v⟩
  obtain ⟨G, _iG1, _iG2, _iG3, hGf, hGfix, hGinv, hGcard⟩ := hIg R₁' h₁ R₀' h₀ hle
  haveI := hGf
  obtain ⟨hfin, hsep⟩ := T5vCore.finrank_residueField_eq_card_and_isSeparable hres r₁ hk₁ r₂ hk₂ hc R₀' R₁' hle
    hR₁ hR₀ G hGfix hGinv
  exact ⟨hfin.trans hGcard, hsep⟩

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (K₂ : IntermediateField L (LaurentSeries L))
    (hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))))

    (ι₂ : ↥K₂ →+* ↥K₁) (hι₂ : ∀ y : ↥K₂, (((ι₂ y : ↥K₁) : LaurentSeries L)) = ((y : ↥K₂) : LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (V : ValuationSubring ↥K₁)
    (hVA : ∀ a : A, algebraMap A ↥K₁ a ∈ V)
    (hVm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K₁ a ∈ V.nonunits)
    (hVj : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)

    (V₂ : ValuationSubring ↥K₂) (hV₂ : ∀ y : ↥K₂, y ∈ V₂ ↔ ι₂ y ∈ V)
    [Algebra ↥V₂ ↥V] (halgV : ∀ y : ↥V₂, (((algebraMap ↥V₂ ↥V y : ↥V) : ↥K₁)) = ι₂ (y : ↥K₂))
    [Algebra (IsLocalRing.ResidueField ↥V₂) (IsLocalRing.ResidueField ↥V)]
    (hres : ∀ y : ↥V₂, algebraMap (IsLocalRing.ResidueField ↥V₂) (IsLocalRing.ResidueField ↥V)
      (IsLocalRing.residue ↥V₂ y) = IsLocalRing.residue ↥V (algebraMap ↥V₂ ↥V y)) :
    Module.finrank (IsLocalRing.ResidueField ↥V₂) (IsLocalRing.ResidueField ↥V) = IntermediateField.relfinrank K₂ K₁ ∧
      Algebra.IsSeparable (IsLocalRing.ResidueField ↥V₂) (IsLocalRing.ResidueField ↥V) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr
  haveI : CharP (IsLocalRing.ResidueField A) p := by
    have h0 : ((p : ℕ) : (IsLocalRing.ResidueField A)) = 0 := by
      rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]; exact hAp
    exact ringChar.of_eq (CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) h0)
  letI algAK₂ : Algebra A ↥K₂ := ((algebraMap L ↥K₂).comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L ↥K₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hjK₂ : ((j : ↥K₁) : LaurentSeries L) ∈ K₂ := by
    rw [hj, hK₂]
    apply ModularCurve.coeffEmb_mem_laurentBaseChange
    show ModularCurve.jq ∈ ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))
    rw [← ModularCurve.jqModC_rat]
    exact ModularCurve.intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
  obtain ⟨j₂, hj₂K⟩ : ∃ j₂ : ↥K₂, ((j₂ : LaurentSeries L)) = ((j : ↥K₁) : LaurentSeries L) := ⟨⟨_, hjK₂⟩, rfl⟩
  have hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq := hj₂K.trans hj
  haveI : Fact (j₂ ≠ 0) := ⟨fun h => (Fact.out : j ≠ 0) (by
    apply Subtype.ext; have := hj₂K; rw [h] at this; simpa using this.symm)⟩
  have hιj₂ : ι₂ j₂ = j := Subtype.ext ((hι₂ j₂).trans hj₂K)
  have hK₁' : K₁ = ModularCurve.laurentBaseChange L
      (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p)) := by rw [hK₁]; rfl

  obtain ⟨W₀, hW₀, hW₀A, -, -, hnu₁⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
      (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p) L K₁ hK₁' A j hj
  obtain ⟨U₀, hU₀, hU₀A, -, -, hnu₂⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
      (CongruenceSubgroup.Gamma0 (M * p)) L K₂ hK₂ A j₂ hj₂
  obtain ⟨red₁, hred₁, hker₁⟩ :=
    ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries L K₁ A W₀ hW₀ hnu₁
  obtain ⟨red₂, hred₂, hker₂⟩ :=
    ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries L K₂ A U₀ hU₀ hnu₂
  have hc₁ : ∀ a : A, red₁ ⟨algebraMap A ↥K₁ a, hW₀A a⟩ = algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a) :=
    fun a => T5vAux.red_algebraMap L K₁ A W₀ red₁ hred₁ a (hW₀A a)
  have hc₂ : ∀ a : A, red₂ ⟨algebraMap A ↥K₂ a, hU₀A a⟩ = algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a) :=
    fun a => T5vAux.red_algebraMap L K₂ A U₀ red₂ hred₂ a (hU₀A a)
  have hr₁ := T5vAux.exists_apply_eq_iff L K₁ A W₀ hW₀ red₁ hred₁
  have hr₂ := T5vAux.exists_apply_eq_iff L K₂ A U₀ hU₀ red₂ hred₂

  obtain ⟨σ, σ₂, hσ, hcompat⟩ :=
    ModularCurve.XOneGammaZeroP.exists_algEquiv_pair_map_j_eq_qExpand_and_coe_comp_eq_x1x0_gamma0 p M hpM L K₁ hK₁ K₂ hK₂ ι₂ hι₂ j hj
  have hσ₂ : ((σ₂ j₂ : ↥K₂) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq) := by
    rw [← hcompat j₂, hιj₂]; exact hσ
  obtain ⟨-, hσcl⟩ := ModularCurve.chartAlgFin_iff_and_comap_ne_and_aeval_mem_comap_of_algEquiv_map_j_eq_qExpand p L K₁ A hAp j hj σ hσ
  obtain ⟨hσW, hσj'⟩ := hσcl W₀ hW₀
  obtain ⟨-, hσ₂cl⟩ := ModularCurve.chartAlgFin_iff_and_comap_ne_and_aeval_mem_comap_of_algEquiv_map_j_eq_qExpand p L K₂ A hAp j₂ hj₂ σ₂ hσ₂
  obtain ⟨hσ₂W, hσ₂j'⟩ := hσ₂cl U₀ hU₀

  obtain ⟨hcases, -, hiii₁, -⟩ :=
    ModularCurve.XOneGammaZeroP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_gaussReduction_eq_x1x0
      p M hM hpM L ζ hζ K₁ hK₁ A hAp hζA j hj ϖ hϖ W₀ hW₀ σ hσ hσW hσj'
  obtain ⟨-, -, hiii₂, -⟩ :=
    ModularCurve.XZeroP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_gaussReduction_eq_gamma0_mul
      p M hM hpM L ζ hζ K₂ hK₂ A hAp hζA j₂ hj₂ ϖ hϖ U₀ hU₀ σ₂ hσ₂ hσ₂W hσ₂j'
  have hdeg := ModularCurve.relfinrank_laurentBaseChange_gamma0_mul_x1x0FunctionFieldC_eq_index p M hM hpM L K₁ hK₁ K₂ hK₂
  have hIg := ModularCurve.exists_mulSemiringAction_faithful_fixed_iff_card_eq_index_qExpFunctionFieldC_gamma1_gamma0_charP p M hpM (IsLocalRing.ResidueField A)
  rw [hdeg]

  rcases hcases V hVA hVm hVj with hV | hV
  ·
    subst hV
    have hVU : V₂ = U₀ := by
      ext y
      rw [hV₂ y, hW₀, hU₀, hι₂ y]
    subst hVU
    refine T5vAux.engine hres red₁ hker₁ red₂ hker₂ (fun y => ?_) (fun c => ?_) (fun c => ?_) _ _ hr₁ hr₂ _ _ hiii₁ hiii₂ _ hIg
    · obtain ⟨x, yy, hyy, hxy⟩ := (hU₀ y).mp y.2
      rw [hred₂ y x yy hyy hxy]
      refine hred₁ _ x yy hyy ?_
      have : (((algebraMap ↥V₂ ↥V y : ↥V) : ↥K₁) : LaurentSeries L) = ((y : ↥K₂) : LaurentSeries L) := by rw [halgV, hι₂]
      rw [this]; exact hxy
    · obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      exact ⟨_, hc₁ a⟩
    · obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      exact ⟨_, hc₂ a⟩
  ·
    have hmemV : ∀ f : ↥K₁, f ∈ V ↔ σ f ∈ W₀ := fun f => by rw [hV]; exact ValuationSubring.mem_comap
    have hmemV₂ : ∀ y : ↥K₂, y ∈ V₂ ↔ σ₂ y ∈ U₀ := fun y => by
      rw [hV₂ y, hmemV, hW₀, hU₀, hcompat y]
    obtain ⟨eσ, heσ, -⟩ := T5vAux.exists_ringEquiv_of_forall_mem_iff σ V W₀ hmemV
    obtain ⟨eσ₂, heσ₂, -⟩ := T5vAux.exists_ringEquiv_of_forall_mem_iff σ₂ V₂ U₀ hmemV₂
    have hσa : ∀ a : A, σ (algebraMap A ↥K₁ a) = algebraMap A ↥K₁ a := fun a => by
      rw [IsScalarTower.algebraMap_apply A L ↥K₁]; exact σ.commutes _
    have hσ₂a : ∀ a : A, σ₂ (algebraMap A ↥K₂ a) = algebraMap A ↥K₂ a := fun a => by
      rw [IsScalarTower.algebraMap_apply A L ↥K₂]; exact σ₂.commutes _
    have hVA₂ : ∀ a : A, algebraMap A ↥K₂ a ∈ V₂ := fun a => by rw [hmemV₂, hσ₂a]; exact hU₀A a
    refine T5vAux.engine hres (red₁.comp (eσ : ↥V →+* ↥W₀)) (T5vAux.ker_comp_ringEquiv_eq_maximalIdeal eσ red₁ hker₁)
      (red₂.comp (eσ₂ : ↥V₂ →+* ↥U₀)) (T5vAux.ker_comp_ringEquiv_eq_maximalIdeal eσ₂ red₂ hker₂)
      (fun y => ?_) (fun c => ?_) (fun c => ?_) _ _ (fun z => ?_) (fun z => ?_) _ _ hiii₁ hiii₂ _ hIg
    ·
      obtain ⟨x, yy, hyy, hxy⟩ := (hU₀ _).mp ((hmemV₂ _).mp y.2)
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [hred₂ (eσ₂ y) x yy hyy (by rw [heσ₂]; exact hxy)]
      refine hred₁ _ x yy hyy ?_
      rw [heσ, show (((algebraMap ↥V₂ ↥V y : ↥V) : ↥K₁)) = ι₂ (y : ↥K₂) from halgV y, hcompat]
      exact hxy
    · obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      refine ⟨⟨algebraMap A ↥K₁ a, hVA a⟩, ?_⟩
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [show eσ ⟨algebraMap A ↥K₁ a, hVA a⟩ = ⟨algebraMap A ↥K₁ a, hW₀A a⟩ from Subtype.ext ((heσ _).trans (hσa a))]
      exact hc₁ a
    · obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
      refine ⟨⟨algebraMap A ↥K₂ a, hVA₂ a⟩, ?_⟩
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [show eσ₂ ⟨algebraMap A ↥K₂ a, hVA₂ a⟩ = ⟨algebraMap A ↥K₂ a, hU₀A a⟩ from Subtype.ext ((heσ₂ _).trans (hσ₂a a))]
      exact hc₂ a
    · rw [← hr₁ z]
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      constructor
      · rintro ⟨v, rfl⟩; exact ⟨eσ v, rfl⟩
      · rintro ⟨w, rfl⟩; exact ⟨eσ.symm w, by rw [RingEquiv.apply_symm_apply]⟩
    · rw [← hr₂ z]
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      constructor
      · rintro ⟨v, rfl⟩; exact ⟨eσ₂ v, rfl⟩
      · rintro ⟨w, rfl⟩; exact ⟨eσ₂.symm w, by rw [RingEquiv.apply_symm_apply]⟩

end S_ModularCurve_XOneGammaZeroP_finrank_residueField_valuationSubring_eq_finrank_and_isSeparable_of_gauss_x1x0_gamma0
end P2MW
export P2MW.S_ModularCurve_XOneGammaZeroP_finrank_residueField_valuationSubring_eq_finrank_and_isSeparable_of_gauss_x1x0_gamma0 (solution)
