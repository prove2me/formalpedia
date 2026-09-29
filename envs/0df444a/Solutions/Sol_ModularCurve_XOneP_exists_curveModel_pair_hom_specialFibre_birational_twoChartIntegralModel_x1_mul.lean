-- Prove2me | solution 1 for ModularCurve.XOneP.exists_curveModel_pair_hom_specialFibre_birational_twoChartIntegralModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/baa4c1dd-2fb9-5760-aa6c-3d35c9bc41fc

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_glued_hom_pullback_of_compatible
import Theorems.Thm_ModularCurve_XOneP_exists_tensorProduct_chartAlg_to_chartRing_igusaFunctionFieldX1C_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_tensorProduct_chartAlg_to_chartRing_igusaFunctionFieldX1C_of_algEquiv_x1_mul
import Theorems.Thm_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_igusaFunctionFieldX1C
import Theorems.Thm_AlgebraicCurve_CurveModel_isProper_smooth_places_affineCover_glued
import Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_pair_x1_mul
import Theorems.Thm_ModularCurve_XOneP_coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_setOf_not_subsingleton_minimalPrimes_span_germ
import Theorems.Thm_AlgebraicGeometry_finite_setOf_pullback_fst_eq_of_isClosed_singleton

import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq

import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair
import Theorems.Thm_AlgebraicGeometry_not_subsingleton_minimalPrimes_span_germ_iff_exists_two_minimalPrimes_le_of_chart
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_setOf_pullback_fst_mem_not_subsingleton_minimalPrimes_span_germ
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_range_glued_hom_iff_ker_le_of_chart_eq
import Theorems.Thm_ModularCurve_XOneP_isReduced_pullback_toBase_twoChartIntegralModel_x1_mul
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIso_stalkMap_genericPoint_glued_hom_of_ker_mem_minimalPrimes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_curveModel_pair_hom_specialFibre_birational_twoChartIntegralModel_x1_mul
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP"
p2m_attr_erase "simp" "ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel IntermediateField
open scoped TensorProduct IntermediateField MatrixGroups

universe u

namespace CompNuSeam

theorem frac
    (L : Type) [Field L] (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [Algebra A ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    (Ω₀ : Type) [Field Ω₀] [Algebra A Ω₀]
    (Ig : IntermediateField Ω₀ (LaurentSeries Ω₀))
    (t : ↥Ig)
    (θ : Ω₀ ⊗[A] ↥(chartAlgFin A (↥K) j) →ₐ[Ω₀] ↥(CurveModel.chartRing Ω₀ ({t} : Set ↥Ig)))
    (τ : ↥K → ↥K)
    (hread : ∀ (b : ↥(chartAlgFin A (↥K) j)) (x y : PowerSeries A),
        y.map (IsLocalRing.residue A) ≠ 0 →
        (((τ (b : ↥K) : ↥K) : LaurentSeries L)) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (((θ ((1 : Ω₀) ⊗ₜ[A] b)) : ↥Ig) : LaurentSeries Ω₀) =
          HahnSeries.ofPowerSeries ℤ Ω₀ (x.map (algebraMap A Ω₀)) /
            HahnSeries.ofPowerSeries ℤ Ω₀ (y.map (algebraMap A Ω₀)))
    (hadj : ∀ z : ↥Ig, ((z : ↥Ig) : LaurentSeries Ω₀) ∈
        IntermediateField.adjoin Ω₀ {r : LaurentSeries Ω₀ |
          ∃ (b : ↥(chartAlgFin A (↥K) j)) (x y : PowerSeries A),
            y.map (IsLocalRing.residue A) ≠ 0 ∧
            (((τ (b : ↥K) : ↥K) : LaurentSeries L)) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
              = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
            r = HahnSeries.ofPowerSeries ℤ Ω₀ (x.map (algebraMap A Ω₀)) /
                  HahnSeries.ofPowerSeries ℤ Ω₀ (y.map (algebraMap A Ω₀))}) :
    ∀ z : ↥Ig, ∃ a b : Ω₀ ⊗[A] ↥(chartAlgFin A (↥K) j),
      ((θ b : ↥(CurveModel.chartRing Ω₀ ({t} : Set ↥Ig))) : ↥Ig) ≠ 0 ∧
        z * ((θ b : ↥(CurveModel.chartRing Ω₀ ({t} : Set ↥Ig))) : ↥Ig) =
          ((θ a : ↥(CurveModel.chartRing Ω₀ ({t} : Set ↥Ig))) : ↥Ig) := by
  classical

  let f : ↥(CurveModel.chartRing Ω₀ ({t} : Set ↥Ig)) →ₐ[Ω₀] LaurentSeries Ω₀ :=
    (IsScalarTower.toAlgHom Ω₀ ↥Ig (LaurentSeries Ω₀)).comp (CurveModel.chartRing Ω₀ ({t} : Set ↥Ig)).val
  have hf : ∀ u, f u = ((u : ↥Ig) : LaurentSeries Ω₀) := fun u => rfl
  let T' : Subalgebra Ω₀ (LaurentSeries Ω₀) := θ.range.map f
  have hT' : ∀ y, y ∈ T' ↔ ∃ v, f (θ v) = y := by
    intro y
    simp only [T', Subalgebra.mem_map, AlgHom.mem_range]
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, h⟩; exact ⟨v, h⟩
    · rintro ⟨v, h⟩; exact ⟨_, ⟨v, rfl⟩, h⟩
  let Tset : Set (LaurentSeries Ω₀) := (T' : Set (LaurentSeries Ω₀))

  have hconst : ∀ c : Ω₀, algebraMap Ω₀ (LaurentSeries Ω₀) c ∈ Subfield.closure Tset :=
    fun c => Subfield.subset_closure (T'.algebraMap_mem c)
  let Tf : IntermediateField Ω₀ (LaurentSeries Ω₀) := (Subfield.closure Tset).toIntermediateField hconst
  have hTf : ∀ r : LaurentSeries Ω₀, r ∈ Tf ↔ r ∈ Subfield.closure Tset := fun r => Iff.rfl
  have hgen : {r : LaurentSeries Ω₀ |
          ∃ (b : ↥(chartAlgFin A (↥K) j)) (x y : PowerSeries A),
            y.map (IsLocalRing.residue A) ≠ 0 ∧
            (((τ (b : ↥K) : ↥K) : LaurentSeries L)) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
              = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
            r = HahnSeries.ofPowerSeries ℤ Ω₀ (x.map (algebraMap A Ω₀)) /
                  HahnSeries.ofPowerSeries ℤ Ω₀ (y.map (algebraMap A Ω₀))} ⊆ (Tf : Set (LaurentSeries Ω₀)) := by
    rintro r ⟨b, x, y, hy, hbxy, rfl⟩
    show _ ∈ Tf
    rw [hTf]
    refine Subfield.subset_closure ((hT' _).mpr ⟨(1 : Ω₀) ⊗ₜ[A] b, ?_⟩)
    rw [hf, hread b x y hy hbxy]
  have hle := IntermediateField.adjoin_le_iff.mpr hgen
  have hcl : ∀ y : LaurentSeries Ω₀, y ∈ Subring.closure Tset → ∃ v, f (θ v) = y := by
    intro y hy
    exact (hT' y).mp ((Subring.closure_le (t := T'.toSubring)).mpr (fun _ h => h) hy)

  intro z
  have hz : ((z : ↥Ig) : LaurentSeries Ω₀) ∈ Subfield.closure Tset := (hTf _).mp (hle (hadj z))
  rw [Subfield.mem_closure_iff] at hz
  obtain ⟨y, hy, w, hw, hyw⟩ := hz
  obtain ⟨a', rfl⟩ := hcl y hy
  obtain ⟨b', rfl⟩ := hcl w hw
  by_cases hw0 : f (θ b') = 0
  ·
    have hz0 : z = 0 := by
      apply Subtype.ext
      rw [← hyw, hw0, div_zero]; rfl
    have hb0 : ((θ b' : ↥(CurveModel.chartRing Ω₀ ({t} : Set ↥Ig))) : ↥Ig) = 0 := by
      apply Subtype.ext; exact hw0

    obtain ⟨u, hu⟩ := hcl 1 (Subring.subset_closure (T'.one_mem))
    refine ⟨b', u, ?_, ?_⟩
    · intro h0
      have : f (θ u) = 0 := by rw [hf, h0]; rfl
      rw [hu] at this
      exact one_ne_zero this
    · rw [hz0, zero_mul, hb0]
  · refine ⟨a', b', ?_, ?_⟩
    · intro h0
      apply hw0
      rw [hf, h0]; rfl
    · apply Subtype.ext
      have : ((z : ↥Ig) : LaurentSeries Ω₀) * f (θ b') = f (θ a') := by
        rw [← hyw, div_mul_cancel₀ _ hw0]
      simpa [hf] using this

end CompNuSeam

namespace S2Cover

theorem ker_algebraMap_eq_maximalIdeal
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (L : Type) [Field L] [CharZero L] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (k : Type) [Field k] [CharP k p] [Algebra A k] :
    RingHom.ker (algebraMap A k) = IsLocalRing.maximalIdeal A := by
  have hprime : (RingHom.ker (algebraMap A k)).IsPrime := RingHom.ker_isPrime _
  have hp : (p : A) ∈ RingHom.ker (algebraMap A k) := by
    rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
  have hne : RingHom.ker (algebraMap A k) ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hp
    have : (p : L) = 0 := by
      have := congrArg (algebraMap A L) hp
      simpa using this
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.IsPrime.isMaximal hprime hne)

theorem map_algebraMap_eq_zero_iff
    (p : ℕ) [Fact p.Prime]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (L : Type) [Field L] [CharZero L] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (k : Type) [Field k] [CharP k p] [Algebra A k] (z : PowerSeries A) :
    z.map (algebraMap A k) = 0 ↔ z.map (IsLocalRing.residue A) = 0 := by
  have hker := ker_algebraMap_eq_maximalIdeal p A L hAp k
  constructor
  · intro h
    ext n
    have hn := congrArg (PowerSeries.coeff n) h
    rw [PowerSeries.coeff_map, map_zero, ← RingHom.mem_ker, hker] at hn
    rw [PowerSeries.coeff_map, map_zero, IsLocalRing.residue_eq_zero_iff]
    exact hn
  · intro h
    ext n
    have hn := congrArg (PowerSeries.coeff n) h
    rw [PowerSeries.coeff_map, map_zero, IsLocalRing.residue_eq_zero_iff] at hn
    rw [PowerSeries.coeff_map, map_zero, ← RingHom.mem_ker, hker]
    exact hn

theorem read_eq_zero_iff_mem_nonunits
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (k : Type) [Field k] [CharP k p] [Algebra A k]
    (W₀ : ValuationSubring ↥K)
    (hW₀mem : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (hW₀nu : ∀ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        (f ∈ W₀.nonunits ↔ x.map (IsLocalRing.residue A) = 0))
    (f : ↥K) (hf : f ∈ W₀) (r : LaurentSeries k)
    (hread : ∀ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 →
        (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
          = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
        r = HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) /
              HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k))) :
    r = 0 ↔ f ∈ W₀.nonunits := by
  obtain ⟨x, y, hy, hxy⟩ := (hW₀mem f).mp hf
  have hr := hread x y hy hxy
  have hinj : Function.Injective (HahnSeries.ofPowerSeries ℤ k) := HahnSeries.ofPowerSeries_injective
  have hyk : HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)) ≠ 0 := by
    intro h0
    apply hy
    rw [← map_algebraMap_eq_zero_iff p A L hAp k]
    apply hinj
    rw [h0, map_zero]
  rw [hW₀nu f x y hy hxy, hr, div_eq_zero_iff, or_iff_left hyk, ← map_algebraMap_eq_zero_iff p A L hAp k]
  constructor
  · intro h
    apply hinj
    rw [h, map_zero]
  · intro h
    rw [h, map_zero]

open scoped TensorProduct in

theorem ker_comp_comm_le_iff
    (A : Type) [CommRing A] (k : Type) [Field k] [Algebra A k]
    (C : Type) [CommRing C] [Algebra A C] (T : Type) [CommRing T] [Algebra k T]
    (θ : k ⊗[A] C →ₐ[k] T)
    (hker : RingHom.ker θ.toRingHom = Ideal.span {z | ∃ b, z = (1 : k) ⊗ₜ[A] b ∧ θ z = 0})
    (𝔮 : Ideal (C ⊗[A] k)) :
    RingHom.ker (θ.toRingHom.comp (Algebra.TensorProduct.comm A C k).toRingHom) ≤ 𝔮 ↔
      ∀ b : C, θ ((1 : k) ⊗ₜ[A] b) = 0 → b ⊗ₜ[A] (1 : k) ∈ 𝔮 := by
  have hk : RingHom.ker (θ.toRingHom.comp (Algebra.TensorProduct.comm A C k).toRingHom) =
      Ideal.span {z | ∃ b : C, z = b ⊗ₜ[A] (1 : k) ∧ θ ((1 : k) ⊗ₜ[A] b) = 0} := by
    rw [← RingHom.comap_ker, hker]
    apply le_antisymm
    ·
      intro z hz
      rw [Ideal.mem_comap] at hz
      have : z = (Algebra.TensorProduct.comm A C k).symm ((Algebra.TensorProduct.comm A C k) z) := by simp
      rw [this]
      refine Submodule.span_induction (p := fun w _ => (Algebra.TensorProduct.comm A C k).symm w ∈
          Ideal.span {z | ∃ b : C, z = b ⊗ₜ[A] (1 : k) ∧ θ ((1 : k) ⊗ₜ[A] b) = 0}) ?_ ?_ ?_ ?_ hz
      · rintro w ⟨b, rfl, hb⟩
        apply Ideal.subset_span
        exact ⟨b, by simp, hb⟩
      · simp
      · intro x y _ _ hx hy
        simpa using Ideal.add_mem _ hx hy
      · intro a x _ hx
        simpa [smul_eq_mul] using Ideal.mul_mem_left _ _ hx
    · rw [Ideal.span_le]
      rintro z ⟨b, rfl, hb⟩
      rw [SetLike.mem_coe, Ideal.mem_comap]
      apply Ideal.subset_span
      exact ⟨b, by simp, hb⟩
  rw [hk, Ideal.span_le]
  constructor
  · intro h b hb
    exact h ⟨b, rfl, hb⟩
  · rintro h z ⟨b, rfl, hb⟩
    exact h b hb

noncomputable def weightOneFormResidueField
    (p : ℕ) [Fact p.Prime] (M : ℕ)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (L : Type) [Field L] [CharZero L] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (k : Type) [Field k] [CharP k p] [Algebra A k]
    (w : ModularCurve.IntegralWeightOneForm k M) :
    ModularCurve.IntegralWeightOneForm (IsLocalRing.ResidueField A) M where
  form := w.form
  series := w.series
  isIntegralQExp := w.isIntegralQExp
  intSeriesC_ne_zero := by
    have hker := ker_algebraMap_eq_maximalIdeal p A L hAp k
    haveI : IsLocalHom (algebraMap A k) := ⟨fun a ha => by
      by_contra hna
      have hmem : a ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal a).mpr hna
      rw [← hker, RingHom.mem_ker] at hmem
      exact ha.ne_zero hmem⟩
    let ι : IsLocalRing.ResidueField A →+* k := IsLocalRing.ResidueField.lift (algebraMap A k)
    have hcast : Int.castRingHom k = ι.comp (Int.castRingHom (IsLocalRing.ResidueField A)) :=
      RingHom.ext_int _ _
    intro h0
    apply w.intSeriesC_ne_zero
    have hκ : PowerSeries.map (Int.castRingHom (IsLocalRing.ResidueField A)) w.series = 0 := by
      apply (HahnSeries.ofPowerSeries_injective : Function.Injective (HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A)))
      rw [map_zero]
      exact h0
    unfold ModularCurve.intSeriesC
    rw [hcast, PowerSeries.map_comp]
    show HahnSeries.ofPowerSeries ℤ k ((PowerSeries.map ι)
      (PowerSeries.map (Int.castRingHom (IsLocalRing.ResidueField A)) w.series)) = 0
    rw [hκ, map_zero, map_zero]

theorem mem_nonunits_comap_iff
    {L K : Type} [Field L] [Field K] [Algebra L K]
    (σ : K ≃ₐ[L] K) (W : ValuationSubring K) (x : K) :
    x ∈ (W.comap (σ : K ≃ₐ[L] K).toAlgHom.toRingHom).nonunits ↔ σ x ∈ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap]
  simp [map_inv₀]

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel in

theorem coe_mem_of_mem_chartAlgFin
    (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (V : ValuationSubring F) (hVA : ∀ a : R, algebraMap R F a ∈ V) (hVj : j ∈ V)
    (b : ↥(chartAlgFin R F j)) : (b : F) ∈ V := by

  have hadj : ∀ x : ↥(Algebra.adjoin R ({j} : Set F)), (x : F) ∈ V := by
    intro x
    refine Algebra.adjoin_induction (p := fun y _ => y ∈ V) ?_ ?_ ?_ ?_ x.2
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]; exact hVj
    · intro a; exact hVA a
    · intro x y _ _ hx hy; exact V.add_mem _ _ hx hy
    · intro x y _ _ hx hy; exact V.mul_mem _ _ hx hy

  let φ : ↥(Algebra.adjoin R ({j} : Set F)) →+* ↥V :=
    { toFun := fun x => ⟨x, hadj x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hb : IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) (b : F) := b.2
  obtain ⟨P, hPm, hPe⟩ := hb
  have hint : IsIntegral ↥V (b : F) := by
    refine ⟨P.map φ, hPm.map φ, ?_⟩
    rw [Polynomial.eval₂_map]
    convert hPe using 2 <;> first | rfl | exact RingHom.ext fun _ => rfl

  have hV : V.valuation.Integers ↥V :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun a => V.valuation_le_one a
      exists_of_le_one := fun x hx => ⟨⟨x, V.mem_of_valuation_le_one x hx⟩, rfl⟩ }
  have := hV.mem_of_integral hint
  exact V.mem_of_valuation_le_one _ this

theorem levelData
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) :
    Transcendental A j ∧ FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by
  refine ⟨ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj, ?_⟩
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  exact ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma1 (M * p)) hT L K hK j hj

theorem core
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (W₀ W₁ : ValuationSubring ↥K)
    (hcomplete : ∀ V : ValuationSubring ↥K,
        (∀ a : A, algebraMap A ↥K a ∈ V) → (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits) →
        (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
          Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁) :
    ∀ 𝔯 : Ideal ↥(chartAlgFin A (↥K) j), 𝔯.IsPrime →
      (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥(chartAlgFin A (↥K) j) a ∈ 𝔯) →
      (∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ 𝔯) ∨
      (∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ W₁.nonunits → b ∈ 𝔯) := by
  intro 𝔯 h𝔯 hm
  obtain ⟨htj, hFD⟩ := levelData p M L K hK A j hj
  haveI := hFD
  haveI : Algebra.IsIntegral ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsSeparable.of_integral _ _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖp : Prime ϖ := hϖ.prime

  have hϖ𝔯 : Ideal.span {algebraMap A ↥(chartAlgFin A (↥K) j) ϖ} ≤ 𝔯 := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hm ϖ (by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
      exact Ideal.mem_span_singleton_self ϖ)
  obtain ⟨𝔭, h𝔭min, h𝔭le⟩ := Ideal.exists_minimalPrimes_le hϖ𝔯
  obtain ⟨V, hVdvr, hAV, hcentre, hϖV, hVj⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
      A L (↥K) j htj hFD inferInstance ϖ hϖp 𝔭 h𝔭min

  have h1 : ∀ a : A, algebraMap A ↥K a ∈ V := by
    intro a
    have := hAV (algebraMap A ↥(chartAlgFin A (↥K) j) a)
    simpa using this
  have h1' : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits := by
    intro a ha
    have hmem : algebraMap A ↥(chartAlgFin A (↥K) j) a ∈ 𝔭 := by
      apply h𝔭min.1.2
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ] at ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have := (hcentre _).mp hmem
    simpa using this
  have h2 : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V := by
    intro P hP
    refine hVj P ?_
    rintro ⟨Q, rfl⟩
    apply hP
    rw [Polynomial.map_mul, Polynomial.map_C, (IsLocalRing.residue_eq_zero_iff ϖ).mpr ?_, map_zero, zero_mul]
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  rcases hcomplete V h1 h1' h2 with rfl | rfl
  · exact Or.inl fun b hb => h𝔭le ((hcentre b).mpr hb)
  · exact Or.inr fun b hb => h𝔭le ((hcentre b).mpr hb)

theorem core_inf
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (W₀ W₁ : ValuationSubring ↥K)
    (hcomplete : ∀ V : ValuationSubring ↥K,
        (∀ a : A, algebraMap A ↥K a ∈ V) → (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits) →
        (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
          Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁) :
    ∀ 𝔯 : Ideal ↥(chartAlgInf A (↥K) j), 𝔯.IsPrime →
      (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥(chartAlgInf A (↥K) j) a ∈ 𝔯) →
      (∀ b : ↥(chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ 𝔯) ∨
      (∀ b : ↥(chartAlgInf A (↥K) j), (b : ↥K) ∈ W₁.nonunits → b ∈ 𝔯) := by
  intro 𝔯 h𝔯 hm
  obtain ⟨htj, hFD⟩ := levelData p M L K hK A j hj
  haveI : Fact ((j : ↥K)⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out : j ≠ 0)⟩

  have htj' : Transcendental A (j⁻¹ : ↥K) := fun h => htj (IsAlgebraic.inv_iff.mp h)
  have hadj : IntermediateField.adjoin L ({j⁻¹} : Set ↥K) = IntermediateField.adjoin L ({j} : Set ↥K) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self L j)
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have := IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self L (j⁻¹ : ↥K))
      simpa using this
  have hFD' : FiniteDimensional ↥(IntermediateField.adjoin L ({j⁻¹} : Set ↥K)) ↥K := by
    rw [hadj]; exact hFD
  haveI := hFD'
  haveI : Algebra.IsIntegral ↥(IntermediateField.adjoin L ({j⁻¹} : Set ↥K)) ↥K := Algebra.IsIntegral.of_finite _ _
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j⁻¹} : Set ↥K)) ↥K := Algebra.IsSeparable.of_integral _ _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖp : Prime ϖ := hϖ.prime
  have hϖmax : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖ𝔯 : Ideal.span {algebraMap A ↥(chartAlgInf A (↥K) j) ϖ} ≤ 𝔯 := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact hm ϖ (by rw [hϖmax]; exact Ideal.mem_span_singleton_self ϖ)
  obtain ⟨𝔭, h𝔭min, h𝔭le⟩ := Ideal.exists_minimalPrimes_le hϖ𝔯
  obtain ⟨V, hVdvr, hAV, hcentre, hϖV, hVj⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
      A L (↥K) (j⁻¹ : ↥K) htj' hFD' inferInstance ϖ hϖp 𝔭 h𝔭min
  have h1 : ∀ a : A, algebraMap A ↥K a ∈ V := by
    intro a
    have := hAV (algebraMap A ↥(chartAlgInf A (↥K) j) a)
    simpa using this
  have h1' : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits := by
    intro a ha
    have hmem : algebraMap A ↥(chartAlgInf A (↥K) j) a ∈ 𝔭 := by
      apply h𝔭min.1.2
      rw [hϖmax] at ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    have := (hcentre _).mp hmem
    simpa using this

  have hnd : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 → ¬ (Polynomial.C ϖ ∣ P) := by
    rintro P hP ⟨Q, rfl⟩
    apply hP
    rw [Polynomial.map_mul, Polynomial.map_C, (IsLocalRing.residue_eq_zero_iff ϖ).mpr
      (by rw [hϖmax]; exact Ideal.mem_span_singleton_self ϖ), map_zero, zero_mul]
  have hjV : (j : ↥K) ∈ V ∧ (j⁻¹ : ↥K) ∈ V := by
    have := hVj Polynomial.X (fun h => by
      have := hnd Polynomial.X (by simp) h; exact this)
    simp only [Polynomial.aeval_X, inv_inv] at this
    exact ⟨this.2, this.1⟩
  have h2 : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V := by
    intro P hP

    have hrev : ¬ (Polynomial.C ϖ ∣ P.reverse) := by
      intro hdvd
      apply hnd P hP
      rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvd ⊢
      intro n
      by_cases hn : n ≤ P.natDegree
      · have := hdvd (Polynomial.revAt P.natDegree n)
        rwa [Polynomial.coeff_reverse, Polynomial.revAt_invol] at this
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hn)]
        exact dvd_zero _
    obtain ⟨hQ, hQinv⟩ := hVj P.reverse hrev

    haveI : Invertible (j : ↥K) := invertibleOfNonzero (Fact.out : j ≠ 0)
    have hmul : Polynomial.aeval (j⁻¹ : ↥K) P.reverse * (j : ↥K) ^ P.natDegree = Polynomial.aeval j P := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, ← invOf_eq_inv]
      exact Polynomial.eval₂_reverse_mul_pow _ _ _
    constructor
    · rw [← hmul]
      exact V.mul_mem _ _ hQ (V.pow_mem hjV.1 _)
    · rw [← hmul, mul_inv, ← inv_pow]
      exact V.mul_mem _ _ hQinv (V.pow_mem hjV.2 _)
  rcases hcomplete V h1 h1' h2 with rfl | rfl
  · exact Or.inl fun b hb => h𝔭le ((hcentre b).mpr hb)
  · exact Or.inr fun b hb => h𝔭le ((hcentre b).mpr hb)

end S2Cover

namespace CompNuBranch

theorem exists_two_minimalPrimes_le_iff {B : Type*} [CommRing B] (I q : Ideal B) (C₀ C₁ : B → Prop)
    (hi : ∀ 𝔭 ∈ I.minimalPrimes, (∀ b, b ∈ 𝔭 ↔ C₀ b) ∨ (∀ b, b ∈ 𝔭 ↔ C₁ b))
    (hii₀ : ∃ 𝔭 ∈ I.minimalPrimes, ∀ b, b ∈ 𝔭 ↔ C₀ b) (hii₁ : ∃ 𝔭 ∈ I.minimalPrimes, ∀ b, b ∈ 𝔭 ↔ C₁ b)
    (hiii : ∃ b, C₀ b ∧ ¬ C₁ b) :
    (∃ 𝔭 ∈ I.minimalPrimes, ∃ 𝔭' ∈ I.minimalPrimes, 𝔭 ≠ 𝔭' ∧ 𝔭 ≤ q ∧ 𝔭' ≤ q) ↔
      (∀ b, C₀ b → b ∈ q) ∧ (∀ b, C₁ b → b ∈ q) := by
  constructor
  · rintro ⟨𝔭, h𝔭, 𝔭', h𝔭', hne, hle, hle'⟩
    have key : ∀ (P P' : Ideal B), P ≠ P' → P ≤ q → P' ≤ q →
        (∀ b, b ∈ P ↔ C₀ b) → ((∀ b, b ∈ P' ↔ C₀ b) ∨ (∀ b, b ∈ P' ↔ C₁ b)) →
        (∀ b, C₀ b → b ∈ q) ∧ (∀ b, C₁ b → b ∈ q) := by
      intro P P' hne hle hle' hP hP'
      rcases hP' with hP' | hP'
      · exact absurd (Ideal.ext fun b => (hP b).trans (hP' b).symm) hne
      · exact ⟨fun b hb => hle ((hP b).mpr hb), fun b hb => hle' ((hP' b).mpr hb)⟩
    rcases hi 𝔭 h𝔭 with h0 | h1
    · exact key 𝔭 𝔭' hne hle hle' h0 (hi 𝔭' h𝔭')
    · rcases hi 𝔭' h𝔭' with h0' | h1'
      · exact key 𝔭' 𝔭 hne.symm hle' hle h0' (Or.inr h1)
      · exact absurd (Ideal.ext fun b => (h1 b).trans (h1' b).symm) hne
  · rintro ⟨h0, h1⟩
    obtain ⟨𝔭₀, h𝔭₀, hP₀⟩ := hii₀
    obtain ⟨𝔭₁, h𝔭₁, hP₁⟩ := hii₁
    obtain ⟨b, hb0, hb1⟩ := hiii
    refine ⟨𝔭₀, h𝔭₀, 𝔭₁, h𝔭₁, fun h => hb1 ((hP₁ b).mp (h ▸ (hP₀ b).mpr hb0)),
      fun x hx => h0 x ((hP₀ x).mp hx), fun x hx => h1 x ((hP₁ x).mp hx)⟩

theorem aeval_inv_mem_of_aeval_mem
    {A : Type} [CommRing A] [IsLocalRing A] {K : Type} [Field K] [Algebra A K]
    (V : ValuationSubring K) (j : K) (hj : j ≠ 0)
    (h : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) :
    ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j⁻¹ P ∈ V ∧ (Polynomial.aeval j⁻¹ P)⁻¹ ∈ V := by
  intro P hP
  have hrev : P.reverse.map (IsLocalRing.residue A) ≠ 0 := by
    intro h0
    apply hP
    ext n
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    by_cases hn : n ≤ P.natDegree
    · have := congrArg (fun Q => Q.coeff (Polynomial.revAt P.natDegree n)) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_reverse, Polynomial.revAt_invol,
        Polynomial.coeff_zero] at this
      exact this
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hn), map_zero]
  obtain ⟨hQ, hQinv⟩ := h P.reverse hrev
  have hjV : j ∈ V ∧ j⁻¹ ∈ V := by
    have := h Polynomial.X (by simp)
    simpa using this
  haveI : Invertible (j⁻¹ : K) := invertibleOfNonzero (inv_ne_zero hj)
  have hmul : Polynomial.aeval j P.reverse * (j⁻¹) ^ P.natDegree = Polynomial.aeval j⁻¹ P := by
    have e : (⅟ (j⁻¹ : K)) = j := by rw [invOf_eq_inv, inv_inv]
    rw [Polynomial.aeval_def, Polynomial.aeval_def]
    have := Polynomial.eval₂_reverse_mul_pow (algebraMap A K) (j⁻¹ : K) P
    rwa [e] at this
  constructor
  · rw [← hmul]
    exact V.mul_mem _ _ hQ (V.pow_mem hjV.2 _)
  · rw [← hmul, mul_inv, ← inv_pow, inv_inv]
    exact V.mul_mem _ _ hQinv (V.pow_mem hjV.1 _)

end CompNuBranch

noncomputable section

namespace CompNu

@[reducible] def curveModelOfGlued (K : Type) [Field K] [Infinite K] [PerfectField K] {L : Type} [Field L] [Algebra K L]
    (t : L) [Fact (t ≠ 0)] (ht : Transcendental K t) [FiniteDimensional ↥K⟮t⟯ L]
    [Algebra.IsSeparable ↥K⟮t⟯ L] : CurveModel K L :=
  let h := CurveModel.isProper_smooth_places_affineCover_glued K t ht
  { C := CurveModel.glued K t
    toBase := CurveModel.gluedToBase K t
    isIntegral := inferInstance
    isProper := h.1
    smooth := h.2.1
    ffEquiv := CurveModel.gluedFunctionFieldEquiv K t
    ffEquiv_algebraMap := CurveModel.gluedFunctionFieldEquiv_algebraMap K t
    placeOfPoint := h.2.2.1.choose
    placeOfPoint_bijective := h.2.2.1.choose_spec.1
    range_stalk_eq := h.2.2.1.choose_spec.2
    finset_subset_affineOpen := h.2.2.2 }

theorem curveModelOfGlued_C (K : Type) [Field K] [Infinite K] [PerfectField K] {L : Type} [Field L] [Algebra K L]
    (t : L) [Fact (t ≠ 0)] (ht : Transcendental K t) [FiniteDimensional ↥K⟮t⟯ L]
    [Algebra.IsSeparable ↥K⟮t⟯ L] : (curveModelOfGlued K t ht).C = CurveModel.glued K t := rfl

end CompNu

end

set_option maxHeartbeats 25600000 in
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
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (Ω₀ : Type) [Field Ω₀] [IsAlgClosed Ω₀] [CharP Ω₀ p] [Algebra A Ω₀]
    (w : ModularCurve.IntegralWeightOneForm Ω₀ M) :
    ∃ (M₁ M₂ : AlgebraicCurve.CurveModel Ω₀ ↥(ModularCurve.igusaFunctionFieldX1C Ω₀ M w))
      (ν₁ : M₁.C ⟶ pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
        (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))))
      (ν₂ : M₂.C ⟶ pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
        (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))),
      ν₁ ≫ pullback.snd _ _ = M₁.toBase ∧ ν₂ ≫ pullback.snd _ _ = M₂.toBase ∧
      Set.range ν₁.base ∪ Set.range ν₂.base = Set.univ ∧
      (Set.range ν₁.base ∩ Set.range ν₂.base).Finite ∧
      IsIso (ν₁.stalkMap (genericPoint M₁.C)) ∧ IsIso (ν₂.stalkMap (genericPoint M₂.C)) ∧

      (∀ z : ↥(pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
          (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))),
        (z ∈ Set.range ν₁.base ∧ z ∈ Set.range ν₂.base) ↔
          ¬ (Ideal.span {((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤
                ((pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
                  (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))).base z) trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ))} :
            Ideal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk
              ((pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
                (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))).base z))).minimalPrimes.Subsingleton) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨t, ht_coe, ht_tr, ht_fd, ht_sep⟩ :=
    ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_igusaFunctionFieldX1C
      p M hM hpM Ω₀ w
  haveI := ht_fd; haveI := ht_sep
  haveI hFt : Fact (t ≠ 0) := ⟨fun h => by
    have := ht_tr; rw [h] at this; exact this isAlgebraic_zero⟩

  obtain ⟨t', θFin, θInf, ht'_coe, hjFin, hjInf, hcompat, hreadF₀, hreadI₀, hkerF₀, hkerI₀⟩ :=
    ModularCurve.XOneP.exists_tensorProduct_chartAlg_to_chartRing_igusaFunctionFieldX1C_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj Ω₀ w
  obtain rfl : t = t' := Subtype.ext (ht_coe.trans ht'_coe.symm)

  obtain ⟨c₀, hc₀_over, hc₀F, hc₀I, hc₀match⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_glued_hom_pullback_of_compatible
      A (↥K) j Ω₀ t 1 one_pos θFin θInf (by simpa using hjFin) (by simpa using hjInf)
      (by intro b b' n h; simpa using hcompat b b' n h)

  obtain ⟨σ, hσ1, hσ2, hσ3⟩ :=
    ModularCurve.XOneP.exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj
  obtain ⟨t'', θFin₁, θInf₁, ht''_coe, hjFin₁, hjInf₁, hcompat₁, hreadF₁, hreadI₁, hkerF₁, hkerI₁⟩ :=
    ModularCurve.XOneP.exists_tensorProduct_chartAlg_to_chartRing_igusaFunctionFieldX1C_of_algEquiv_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj Ω₀ w σ hσ1 hσ2 hσ3
  obtain rfl : t = t'' := Subtype.ext (ht_coe.trans ht''_coe.symm)
  obtain ⟨c₁, hc₁_over, hc₁F, hc₁I, hc₁match⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_glued_hom_pullback_of_compatible
      A (↥K) j Ω₀ t p (Fact.out : p.Prime).pos θFin₁ θInf₁ hjFin₁ hjInf₁ hcompat₁

  haveI : Infinite Ω₀ := IsAlgClosed.instInfinite
  let Mg : AlgebraicCurve.CurveModel Ω₀ ↥(ModularCurve.igusaFunctionFieldX1C Ω₀ M w) :=
    CompNu.curveModelOfGlued Ω₀ t ht_tr

  obtain ⟨himF₀, himI₀⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.mem_range_glued_hom_iff_ker_le_of_chart_eq
      A (↥K) j Ω₀ t 1 one_pos θFin θInf (by simpa using hjFin) (by simpa using hjInf)
      c₀ hc₀_over hc₀F hc₀I hc₀match
  obtain ⟨himF₁, himI₁⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.mem_range_glued_hom_iff_ker_le_of_chart_eq
      A (↥K) j Ω₀ t p (Fact.out : p.Prime).pos θFin₁ θInf₁ hjFin₁ hjInf₁
      c₁ hc₁_over hc₁F hc₁I hc₁match

  obtain ⟨W₀', W₁', hS1_1, hS1_2, hS1_ne, hS1_4, hS1_5, hS1_6, -⟩ :=
    ModularCurve.XOneP.exists_valuationSubring_pair_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj (S2Cover.weightOneFormResidueField p M A L hAp Ω₀ w)
  have hcore := S2Cover.core p M L K hK A j hj W₀' W₁' hS1_5
  have hW₁ : W₀'.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom = W₁' := by
    obtain ⟨hne', h2'⟩ := hσ3 W₀' hS1_4
    have h1a : ∀ a : A, algebraMap A ↥K a ∈ W₀'.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom := by
      intro a
      rw [ValuationSubring.mem_comap]
      show σ (algebraMap A ↥K a) ∈ W₀'
      rw [IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes]
      simpa [← IsScalarTower.algebraMap_apply] using (hS1_1 0).1 a
    have h1b : ∀ a ∈ IsLocalRing.maximalIdeal A,
        algebraMap A ↥K a ∈ (W₀'.comap (σ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom).nonunits := by
      intro a ha
      rw [S2Cover.mem_nonunits_comap_iff, IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes,
        ← IsScalarTower.algebraMap_apply]
      simpa using (hS1_1 0).2 a ha
    rcases hS1_5 _ h1a h1b h2' with h | h
    · exact absurd h hne'
    · exact h

  have H3F : ∀ 𝔮 : Ideal (↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) ⊗[A] Ω₀), 𝔮.IsPrime →
      RingHom.ker (θFin.toRingHom.comp
          (Algebra.TensorProduct.comm A ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) Ω₀).toRingHom) ≤ 𝔮 ∨
      RingHom.ker (θFin₁.toRingHom.comp
          (Algebra.TensorProduct.comm A ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) Ω₀).toRingHom) ≤ 𝔮 := by
    intro 𝔮 h𝔮

    let 𝔯 : Ideal ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) :=
      𝔮.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A)
        (A := ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j)) (B := Ω₀)).toRingHom
    have h𝔯 : 𝔯.IsPrime := Ideal.comap_isPrime _ _
    have hm : ∀ a ∈ IsLocalRing.maximalIdeal A,
        algebraMap A ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) a ∈ 𝔯 := by
      intro a ha
      have ha0 : algebraMap A Ω₀ a = 0 := by
        rw [← RingHom.mem_ker, S2Cover.ker_algebraMap_eq_maximalIdeal p A L hAp Ω₀]; exact ha
      show (Algebra.TensorProduct.includeLeft (R := A) (S := A)
        (A := ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j)) (B := Ω₀))
          (algebraMap A _ a) ∈ 𝔮
      rw [Algebra.TensorProduct.includeLeft_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one, ha0, TensorProduct.tmul_zero]
      exact 𝔮.zero_mem

    have hW₀A : ∀ a : A, algebraMap A ↥K a ∈ W₀' := by simpa using (hS1_1 0).1
    have hW₀j : (j : ↥K) ∈ W₀' := by
      have := (hS1_2 0 Polynomial.X (by simp)).1
      simpa using this
    have hbW : ∀ b : ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀' :=
      S2Cover.coe_mem_of_mem_chartAlgFin A (↥K) j W₀' hW₀A hW₀j
    rcases hcore 𝔯 h𝔯 hm with h | h
    · left
      rw [S2Cover.ker_comp_comm_le_iff A Ω₀ _ _ θFin hkerF₀]
      intro b hb0
      apply h b

      rw [← S2Cover.read_eq_zero_iff_mem_nonunits p L K A hAp Ω₀ W₀' hS1_4 (fun f x y hy hxy => (hS1_6 f x y hy hxy).2)
        (b : ↥K) (hbW b) _ (hreadF₀ b)]
      rw [hb0]; rfl
    · right
      rw [S2Cover.ker_comp_comm_le_iff A Ω₀ _ _ θFin₁ hkerF₁]
      intro b hb0
      apply h b
      rw [← hW₁, S2Cover.mem_nonunits_comap_iff]
      rw [← S2Cover.read_eq_zero_iff_mem_nonunits p L K A hAp Ω₀ W₀' hS1_4 (fun f x y hy hxy => (hS1_6 f x y hy hxy).2)
        (σ (b : ↥K)) (hbW ⟨σ b, (hσ2 b).mp b.2⟩) _ (hreadF₁ b)]
      rw [hb0]; rfl
  have H3I : ∀ 𝔮 : Ideal (↥(TwoChartIntegralModel.chartAlgInf A (↥K) j) ⊗[A] Ω₀), 𝔮.IsPrime →
      RingHom.ker (θInf.toRingHom.comp
          (Algebra.TensorProduct.comm A ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j) Ω₀).toRingHom) ≤ 𝔮 ∨
      RingHom.ker (θInf₁.toRingHom.comp
          (Algebra.TensorProduct.comm A ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j) Ω₀).toRingHom) ≤ 𝔮 := by
    intro 𝔮 h𝔮
    let 𝔯 : Ideal ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j) :=
      𝔮.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A)
        (A := ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j)) (B := Ω₀)).toRingHom
    have h𝔯 : 𝔯.IsPrime := Ideal.comap_isPrime _ _
    have hm : ∀ a ∈ IsLocalRing.maximalIdeal A,
        algebraMap A ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j) a ∈ 𝔯 := by
      intro a ha
      have ha0 : algebraMap A Ω₀ a = 0 := by
        rw [← RingHom.mem_ker, S2Cover.ker_algebraMap_eq_maximalIdeal p A L hAp Ω₀]; exact ha
      show (Algebra.TensorProduct.includeLeft (R := A) (S := A)
        (A := ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j)) (B := Ω₀))
          (algebraMap A _ a) ∈ 𝔮
      rw [Algebra.TensorProduct.includeLeft_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one, ha0, TensorProduct.tmul_zero]
      exact 𝔮.zero_mem
    haveI : Fact ((j : ↥K)⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out : j ≠ 0)⟩
    have hW₀A : ∀ a : A, algebraMap A ↥K a ∈ W₀' := by simpa using (hS1_1 0).1
    have hW₁A : ∀ a : A, algebraMap A ↥K a ∈ W₁' := by simpa using (hS1_1 1).1
    have hW₀ji : (j : ↥K)⁻¹ ∈ W₀' := by
      have := (hS1_2 0 Polynomial.X (by simp)).2
      simpa using this
    have hW₁ji : (j : ↥K)⁻¹ ∈ W₁' := by
      have := (hS1_2 1 Polynomial.X (by simp)).2
      simpa using this
    have hbW : ∀ b : ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀' :=
      S2Cover.coe_mem_of_mem_chartAlgFin A (↥K) (j⁻¹ : ↥K) W₀' hW₀A hW₀ji
    have hbW₁ : ∀ b : ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₁' :=
      S2Cover.coe_mem_of_mem_chartAlgFin A (↥K) (j⁻¹ : ↥K) W₁' hW₁A hW₁ji
    have hσbW : ∀ b : ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j), σ (b : ↥K) ∈ W₀' := by
      intro b
      have := hbW₁ b
      rw [← hW₁, ValuationSubring.mem_comap] at this
      exact this
    have hcoreI := S2Cover.core_inf p M L K hK A j hj W₀' W₁' hS1_5
    rcases hcoreI 𝔯 h𝔯 hm with h | h
    · left
      rw [S2Cover.ker_comp_comm_le_iff A Ω₀ _ _ θInf hkerI₀]
      intro b hb0
      apply h b
      rw [← S2Cover.read_eq_zero_iff_mem_nonunits p L K A hAp Ω₀ W₀' hS1_4 (fun f x y hy hxy => (hS1_6 f x y hy hxy).2)
        (b : ↥K) (hbW b) _ (hreadI₀ b)]
      rw [hb0]; rfl
    · right
      rw [S2Cover.ker_comp_comm_le_iff A Ω₀ _ _ θInf₁ hkerI₁]
      intro b hb0
      apply h b
      rw [← hW₁, S2Cover.mem_nonunits_comap_iff]
      rw [← S2Cover.read_eq_zero_iff_mem_nonunits p L K A hAp Ω₀ W₀' hS1_4 (fun f x y hy hxy => (hS1_6 f x y hy hxy).2)
        (σ (b : ↥K)) (hσbW b) _ (hreadI₁ b)]
      rw [hb0]; rfl

  have H5 : ∀ z : ↥(pullback (TwoChartIntegralModel.toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))),
      (∃ zz : ↥(pullback (TwoChartIntegralModel.ιFin A (↥K) j)
          (pullback.fst (TwoChartIntegralModel.toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))))),
        (pullback.snd (TwoChartIntegralModel.ιFin A (↥K) j) _).base zz = z) ∨
      (∃ zz : ↥(pullback (TwoChartIntegralModel.ιInf A (↥K) j)
          (pullback.fst (TwoChartIntegralModel.toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))))),
        (pullback.snd (TwoChartIntegralModel.ιInf A (↥K) j) _).base zz = z) := by
    intro z
    rcases TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf A (↥K) j
        ((pullback.fst (TwoChartIntegralModel.toBase A (↥K) j)
          (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))).base z) with h | h
    · left
      have hz : z ∈ Set.range (pullback.snd (TwoChartIntegralModel.ιFin A (↥K) j)
          (pullback.fst (TwoChartIntegralModel.toBase A (↥K) j)
            (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))))).base := by
        erw [Scheme.Pullback.range_snd]
        exact h
      exact hz
    · right
      have hz : z ∈ Set.range (pullback.snd (TwoChartIntegralModel.ιInf A (↥K) j)
          (pullback.fst (TwoChartIntegralModel.toBase A (↥K) j)
            (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))))).base := by
        erw [Scheme.Pullback.range_snd]
        exact h
      exact hz
  have coverAll : ∀ z : ↥(pullback (TwoChartIntegralModel.toBase A (↥K) j)
        (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))), z ∈ Set.range c₀.base ∨ z ∈ Set.range c₁.base := by
    intro z
    rcases H5 z with ⟨zz, rfl⟩ | ⟨zz, rfl⟩
    · rcases H3F _ (inferInstance : ((pullbackRightPullbackFstIso (TwoChartIntegralModel.toBase A (↥K) j)
          (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))) (TwoChartIntegralModel.ιFin A (↥K) j) ≪≫
          pullback.congrHom (TwoChartIntegralModel.ιFin_toBase A (↥K) j) rfl ≪≫
          pullbackSpecIso A ↥(TwoChartIntegralModel.chartAlgFin A (↥K) j) Ω₀).hom.base zz).asIdeal.IsPrime) with h | h
      · exact Or.inl ((himF₀ zz).mpr h)
      · exact Or.inr ((himF₁ zz).mpr h)
    · rcases H3I _ (inferInstance : ((pullbackRightPullbackFstIso (TwoChartIntegralModel.toBase A (↥K) j)
          (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))) (TwoChartIntegralModel.ιInf A (↥K) j) ≪≫
          pullback.congrHom (TwoChartIntegralModel.ιInf_toBase A (↥K) j) rfl ≪≫
          pullbackSpecIso A ↥(TwoChartIntegralModel.chartAlgInf A (↥K) j) Ω₀).hom.base zz).asIdeal.IsPrime) with h | h
      · exact Or.inl ((himI₀ zz).mpr h)
      · exact Or.inr ((himI₁ zz).mpr h)

  obtain ⟨htj, hFD⟩ := S2Cover.levelData p M L K hK A j hj
  haveI := hFD
  haveI : Algebra.IsIntegral ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsIntegral.of_finite _ _
  have hsepK : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsSeparable.of_integral _ _
  haveI : Fact ((j : ↥K)⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out : j ≠ 0)⟩
  have htj' : Transcendental A (j⁻¹ : ↥K) := fun h => htj (IsAlgebraic.inv_iff.mp h)
  have hadj : IntermediateField.adjoin L ({j⁻¹} : Set ↥K) = IntermediateField.adjoin L ({j} : Set ↥K) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self L j)
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have := IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self L (j⁻¹ : ↥K))
      simpa using this
  have hFD' : FiniteDimensional ↥(IntermediateField.adjoin L ({j⁻¹} : Set ↥K)) ↥K := by rw [hadj]; exact hFD
  have hsepK' : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j⁻¹} : Set ↥K)) ↥K := by rw [hadj]; exact hsepK

  obtain ⟨hKM1, hKM2, hKM3a, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_span_iff_of_valuationSubring_pair
      A L (↥K) j htj hFD hsepK ϖ hϖ W₀' W₁' hS1_1 hS1_2 hS1_ne hS1_5
  have hS1_2' : ∀ i : Fin 2, ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval (j⁻¹ : ↥K) P ∈ (![W₀', W₁'] i) ∧ (Polynomial.aeval (j⁻¹ : ↥K) P)⁻¹ ∈ (![W₀', W₁'] i) :=
    fun i => CompNuBranch.aeval_inv_mem_of_aeval_mem _ (j : ↥K) (Fact.out : j ≠ 0) (hS1_2 i)
  have hS1_5' : ∀ V : ValuationSubring ↥K,
      (∀ a : A, algebraMap A ↥K a ∈ V) → (∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits) →
      (∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
        Polynomial.aeval (j⁻¹ : ↥K) P ∈ V ∧ (Polynomial.aeval (j⁻¹ : ↥K) P)⁻¹ ∈ V) →
      V = W₀' ∨ V = W₁' := by
    intro V hVA hVm hVj
    refine hS1_5 V hVA hVm ?_
    have := CompNuBranch.aeval_inv_mem_of_aeval_mem V (j⁻¹ : ↥K) (inv_ne_zero (Fact.out : j ≠ 0)) hVj
    simpa only [inv_inv] using this
  obtain ⟨hKM1', hKM2', hKM3a', -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_span_iff_of_valuationSubring_pair
      A L (↥K) (j⁻¹ : ↥K) htj' hFD' hsepK' ϖ hϖ W₀' W₁' hS1_1 hS1_2' hS1_ne hS1_5'

  have hW₀A : ∀ a : A, algebraMap A ↥K a ∈ W₀' := by simpa using (hS1_1 0).1
  have hW₁A : ∀ a : A, algebraMap A ↥K a ∈ W₁' := by simpa using (hS1_1 1).1
  have hW₀j : (j : ↥K) ∈ W₀' := by simpa using (hS1_2 0 Polynomial.X (by simp)).1
  have hW₀ji : (j : ↥K)⁻¹ ∈ W₀' := by simpa using (hS1_2 0 Polynomial.X (by simp)).2
  have hW₁ji : (j : ↥K)⁻¹ ∈ W₁' := by simpa using (hS1_2 1 Polynomial.X (by simp)).2
  have hbW : ∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀' :=
    S2Cover.coe_mem_of_mem_chartAlgFin A (↥K) j W₀' hW₀A hW₀j
  have hbWI : ∀ b : ↥(chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀' :=
    S2Cover.coe_mem_of_mem_chartAlgFin A (↥K) (j⁻¹ : ↥K) W₀' hW₀A hW₀ji
  have hbWI₁ : ∀ b : ↥(chartAlgInf A (↥K) j), (b : ↥K) ∈ W₁' :=
    S2Cover.coe_mem_of_mem_chartAlgFin A (↥K) (j⁻¹ : ↥K) W₁' hW₁A hW₁ji
  have hnu := fun f x y hy hxy => (hS1_6 f x y hy hxy).2
  have hD0 : ∀ b : ↥(chartAlgFin A (↥K) j), θFin ((1 : Ω₀) ⊗ₜ[A] b) = 0 ↔ (b : ↥K) ∈ W₀'.nonunits := by
    intro b
    rw [← S2Cover.read_eq_zero_iff_mem_nonunits p L K A hAp Ω₀ W₀' hS1_4 hnu (b : ↥K) (hbW b) _ (hreadF₀ b),
      ← ZeroMemClass.coe_eq_zero, ← ZeroMemClass.coe_eq_zero]
  have hD1 : ∀ b : ↥(chartAlgFin A (↥K) j), θFin₁ ((1 : Ω₀) ⊗ₜ[A] b) = 0 ↔ (b : ↥K) ∈ W₁'.nonunits := by
    intro b
    rw [← hW₁, S2Cover.mem_nonunits_comap_iff,
      ← S2Cover.read_eq_zero_iff_mem_nonunits p L K A hAp Ω₀ W₀' hS1_4 hnu (σ (b : ↥K))
        (hbW ⟨σ b, (hσ2 b).mp b.2⟩) _ (hreadF₁ b),
      ← ZeroMemClass.coe_eq_zero, ← ZeroMemClass.coe_eq_zero]
  have hσbW : ∀ b : ↥(chartAlgInf A (↥K) j), σ (b : ↥K) ∈ W₀' := by
    intro b
    have := hbWI₁ b
    rw [← hW₁, ValuationSubring.mem_comap] at this
    exact this
  have hD0I : ∀ b : ↥(chartAlgInf A (↥K) j), θInf ((1 : Ω₀) ⊗ₜ[A] b) = 0 ↔ (b : ↥K) ∈ W₀'.nonunits := by
    intro b
    rw [← S2Cover.read_eq_zero_iff_mem_nonunits p L K A hAp Ω₀ W₀' hS1_4 hnu (b : ↥K) (hbWI b) _ (hreadI₀ b),
      ← ZeroMemClass.coe_eq_zero, ← ZeroMemClass.coe_eq_zero]
  have hD1I : ∀ b : ↥(chartAlgInf A (↥K) j), θInf₁ ((1 : Ω₀) ⊗ₜ[A] b) = 0 ↔ (b : ↥K) ∈ W₁'.nonunits := by
    intro b
    rw [← hW₁, S2Cover.mem_nonunits_comap_iff,
      ← S2Cover.read_eq_zero_iff_mem_nonunits p L K A hAp Ω₀ W₀' hS1_4 hnu (σ (b : ↥K)) (hσbW b) _ (hreadI₁ b),
      ← ZeroMemClass.coe_eq_zero, ← ZeroMemClass.coe_eq_zero]

  have hisoF : (pullbackRightPullbackFstIso (toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))
        (ιFin A (↥K) j) ≪≫ pullback.congrHom (ιFin_toBase A (↥K) j) rfl ≪≫
        pullbackSpecIso A ↥(chartAlgFin A (↥K) j) Ω₀).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := A) (A := ↥(chartAlgFin A (↥K) j)) (B := Ω₀))) =
      pullback.fst (ιFin A (↥K) j) _ := by
    simp only [Iso.trans_hom, Category.assoc]
    rw [← pullbackSpecIso_inv_fst A ↥(chartAlgFin A (↥K) j) Ω₀, Iso.hom_inv_id_assoc]
    simp only [pullback.congrHom_hom, pullback.lift_fst, Category.comp_id, pullbackRightPullbackFstIso_hom_fst]
  have hisoI : (pullbackRightPullbackFstIso (toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))
        (ιInf A (↥K) j) ≪≫ pullback.congrHom (ιInf_toBase A (↥K) j) rfl ≪≫
        pullbackSpecIso A ↥(chartAlgInf A (↥K) j) Ω₀).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := A) (A := ↥(chartAlgInf A (↥K) j)) (B := Ω₀))) =
      pullback.fst (ιInf A (↥K) j) _ := by
    simp only [Iso.trans_hom, Category.assoc]
    rw [← pullbackSpecIso_inv_fst A ↥(chartAlgInf A (↥K) j) Ω₀, Iso.hom_inv_id_assoc]
    simp only [pullback.congrHom_hom, pullback.lift_fst, Category.comp_id, pullbackRightPullbackFstIso_hom_fst]

  obtain ⟨-, -, hKM3a₀, hKM3b₀⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_span_iff_of_valuationSubring_pair
      A L (↥K) j htj hFD hsepK ϖ hϖ W₀' W₁' hS1_1 hS1_2 hS1_ne hS1_5
  have hcontract : ∀ P : Ideal (↥(chartAlgFin A (↥K) j) ⊗[A] Ω₀), P.IsPrime →
      (∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀'.nonunits → b ⊗ₜ[A] (1 : Ω₀) ∈ P) ∨
      (∀ b : ↥(chartAlgFin A (↥K) j), (b : ↥K) ∈ W₁'.nonunits → b ⊗ₜ[A] (1 : Ω₀) ∈ P) := by
    intro P hP
    let 𝔯 : Ideal ↥(chartAlgFin A (↥K) j) :=
      P.comap (Algebra.TensorProduct.includeLeft (R := A) (S := A)
        (A := ↥(chartAlgFin A (↥K) j)) (B := Ω₀)).toRingHom
    have h𝔯 : 𝔯.IsPrime := Ideal.comap_isPrime _ _
    have hm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥(chartAlgFin A (↥K) j) a ∈ 𝔯 := by
      intro a ha
      have ha0 : algebraMap A Ω₀ a = 0 := by
        rw [← RingHom.mem_ker, S2Cover.ker_algebraMap_eq_maximalIdeal p A L hAp Ω₀]; exact ha
      show (Algebra.TensorProduct.includeLeft (R := A) (S := A)
        (A := ↥(chartAlgFin A (↥K) j)) (B := Ω₀)) (algebraMap A _ a) ∈ P
      rw [Algebra.TensorProduct.includeLeft_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one, ha0, TensorProduct.tmul_zero]
      exact P.zero_mem
    rcases hcore 𝔯 h𝔯 hm with h | h
    · exact Or.inl fun b hb => h b hb
    · exact Or.inr fun b hb => h b hb
  have hmin₀ : RingHom.ker (θFin.toRingHom.comp
      (Algebra.TensorProduct.comm A ↥(chartAlgFin A (↥K) j) Ω₀).toRingHom) ∈
      minimalPrimes (↥(chartAlgFin A (↥K) j) ⊗[A] Ω₀) := by
    have hprime : (RingHom.ker (θFin.toRingHom.comp
        (Algebra.TensorProduct.comm A ↥(chartAlgFin A (↥K) j) Ω₀).toRingHom)).IsPrime := RingHom.ker_isPrime _
    refine ⟨⟨hprime, bot_le⟩, fun P hP hPle => ?_⟩
    rw [S2Cover.ker_comp_comm_le_iff A Ω₀ _ _ θFin hkerF₀]
    rcases hcontract P hP.1 with h | h
    · intro b hb; exact h b ((hD0 b).mp hb)
    · exfalso
      obtain ⟨b, hb1, hb0⟩ := hKM3b₀
      have hmem : b ⊗ₜ[A] (1 : Ω₀) ∈ RingHom.ker (θFin.toRingHom.comp
          (Algebra.TensorProduct.comm A ↥(chartAlgFin A (↥K) j) Ω₀).toRingHom) := hPle (h b hb1)
      rw [RingHom.mem_ker] at hmem
      have : θFin ((1 : Ω₀) ⊗ₜ[A] b) = 0 := by simpa using hmem
      exact hb0 ((hD0 b).mp this)
  have hmin₁ : RingHom.ker (θFin₁.toRingHom.comp
      (Algebra.TensorProduct.comm A ↥(chartAlgFin A (↥K) j) Ω₀).toRingHom) ∈
      minimalPrimes (↥(chartAlgFin A (↥K) j) ⊗[A] Ω₀) := by
    have hprime : (RingHom.ker (θFin₁.toRingHom.comp
        (Algebra.TensorProduct.comm A ↥(chartAlgFin A (↥K) j) Ω₀).toRingHom)).IsPrime := RingHom.ker_isPrime _
    refine ⟨⟨hprime, bot_le⟩, fun P hP hPle => ?_⟩
    rw [S2Cover.ker_comp_comm_le_iff A Ω₀ _ _ θFin₁ hkerF₁]
    rcases hcontract P hP.1 with h | h
    · exfalso
      obtain ⟨b, hb0, hb1⟩ := hKM3a₀
      have hmem : b ⊗ₜ[A] (1 : Ω₀) ∈ RingHom.ker (θFin₁.toRingHom.comp
          (Algebra.TensorProduct.comm A ↥(chartAlgFin A (↥K) j) Ω₀).toRingHom) := hPle (h b hb0)
      rw [RingHom.mem_ker] at hmem
      have : θFin₁ ((1 : Ω₀) ⊗ₜ[A] b) = 0 := by simpa using hmem
      exact hb1 ((hD1 b).mp this)
    · intro b hb; exact h b ((hD1 b).mp hb)

  haveI hredX := ModularCurve.XOneP.isReduced_pullback_toBase_twoChartIntegralModel_x1_mul
    p M hM hpM L ζ hζ K hK A hAp hζA j hj Ω₀

  obtain ⟨hFI, -⟩ := ModularCurve.XOneP.coe_mem_adjoin_gaussReductions_chartAlg_igusaFunctionFieldX1C_x1_mul
    p M hM hpM L ζ hζ K hK A hAp hζA j hj Ω₀ w
  have hfrac₀ := CompNuSeam.frac L K A j Ω₀ (ModularCurve.igusaFunctionFieldX1C Ω₀ M w) t θFin (fun f => f)
    hreadF₀ hFI
  have hFIσ : ∀ z : ↥(ModularCurve.igusaFunctionFieldX1C Ω₀ M w),
      ((z : ↥(ModularCurve.igusaFunctionFieldX1C Ω₀ M w)) : LaurentSeries Ω₀) ∈
      IntermediateField.adjoin Ω₀ {r : LaurentSeries Ω₀ |
        ∃ (b : ↥(chartAlgFin A (↥K) j)) (x y : PowerSeries A),
          y.map (IsLocalRing.residue A) ≠ 0 ∧
          (((σ (b : ↥K) : ↥K) : LaurentSeries L)) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
            = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
          r = HahnSeries.ofPowerSeries ℤ Ω₀ (x.map (algebraMap A Ω₀)) /
                HahnSeries.ofPowerSeries ℤ Ω₀ (y.map (algebraMap A Ω₀))} := by
    intro z
    convert hFI z using 3
    ext r
    constructor
    · rintro ⟨b, x, y, hy, hxy, hr⟩
      exact ⟨⟨σ b, (hσ2 b).mp b.2⟩, x, y, hy, hxy, hr⟩
    · rintro ⟨b, x, y, hy, hxy, hr⟩
      refine ⟨⟨σ.symm b, (hσ2 (σ.symm b)).mpr (by simpa using b.2)⟩, x, y, hy, ?_, hr⟩
      simpa using hxy
  have hfrac₁ := CompNuSeam.frac L K A j Ω₀ (ModularCurve.igusaFunctionFieldX1C Ω₀ M w) t θFin₁ (fun f => σ f)
    hreadF₁ hFIσ
  have hbranch : ∀ z : ↥(pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
          (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))),
        (z ∈ Set.range c₀.base ∧ z ∈ Set.range c₁.base) ↔
          ¬ (Ideal.span {((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤
                ((pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
                  (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))).base z) trivial).hom
              (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ))} :
            Ideal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk
              ((pullback.fst (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
                (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))).base z))).minimalPrimes.Subsingleton := by
    intro z
    rcases H5 z with ⟨zz, rfl⟩ | ⟨zz, rfl⟩
    ·
      obtain ⟨q, hqdef⟩ : ∃ q, q = (pullback.fst (ιFin A (↥K) j) (pullback.fst (toBase A (↥K) j)
        (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))))).base zz := ⟨_, rfl⟩
      have hq : ∀ b : ↥(chartAlgFin A (↥K) j), b ∈ q.asIdeal ↔
          b ⊗ₜ[A] (1 : Ω₀) ∈ ((pullbackRightPullbackFstIso (toBase A (↥K) j)
            (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))) (ιFin A (↥K) j) ≪≫
            pullback.congrHom (ιFin_toBase A (↥K) j) rfl ≪≫
            pullbackSpecIso A ↥(chartAlgFin A (↥K) j) Ω₀).hom.base zz).asIdeal := by
        intro b
        have h : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
            (R := A) (A := ↥(chartAlgFin A (↥K) j)) (B := Ω₀)))).base
            ((pullbackRightPullbackFstIso (toBase A (↥K) j)
              (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))) (ιFin A (↥K) j) ≪≫
              pullback.congrHom (ιFin_toBase A (↥K) j) rfl ≪≫
              pullbackSpecIso A ↥(chartAlgFin A (↥K) j) Ω₀).hom.base zz) = q := by
          rw [hqdef, ← hisoF]; rfl
        rw [← h]
        rfl
      have hx : (pullback.fst (toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))).base
          ((pullback.snd (ιFin A (↥K) j) _).base zz) = (ιFin A (↥K) j).base q := by
        rw [hqdef]
        change ((pullback.snd (ιFin A (↥K) j) _) ≫ pullback.fst (toBase A (↥K) j) _).base zz =
          ((pullback.fst (ιFin A (↥K) j) _) ≫ ιFin A (↥K) j).base zz
        rw [pullback.condition]
      rw [hx]
      refine (and_congr (himF₀ zz) (himF₁ zz)).trans ?_
      refine Iff.trans ?_ (AlgebraicGeometry.not_subsingleton_minimalPrimes_span_germ_iff_exists_two_minimalPrimes_le_of_chart
        (toBase A (↥K) j) (ιFin A (↥K) j) (ιFin_toBase A (↥K) j) ϖ q).symm
      refine Iff.trans ?_ (CompNuBranch.exists_two_minimalPrimes_le_iff _ q.asIdeal
        (fun b => (b : ↥K) ∈ W₀'.nonunits) (fun b => (b : ↥K) ∈ W₁'.nonunits) hKM1 (hKM2 0) (hKM2 1) hKM3a).symm
      refine (and_congr (S2Cover.ker_comp_comm_le_iff A Ω₀ _ _ θFin hkerF₀ _)
        (S2Cover.ker_comp_comm_le_iff A Ω₀ _ _ θFin₁ hkerF₁ _)).trans ?_
      refine and_congr (forall_congr' fun b => ?_) (forall_congr' fun b => ?_)
      · rw [hD0 b, hq b]
      · rw [hD1 b, hq b]
    ·
      obtain ⟨q, hqdef⟩ : ∃ q, q = (pullback.fst (ιInf A (↥K) j) (pullback.fst (toBase A (↥K) j)
        (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))))).base zz := ⟨_, rfl⟩
      have hq : ∀ b : ↥(chartAlgInf A (↥K) j), b ∈ q.asIdeal ↔
          b ⊗ₜ[A] (1 : Ω₀) ∈ ((pullbackRightPullbackFstIso (toBase A (↥K) j)
            (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))) (ιInf A (↥K) j) ≪≫
            pullback.congrHom (ιInf_toBase A (↥K) j) rfl ≪≫
            pullbackSpecIso A ↥(chartAlgInf A (↥K) j) Ω₀).hom.base zz).asIdeal := by
        intro b
        have h : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
            (R := A) (A := ↥(chartAlgInf A (↥K) j)) (B := Ω₀)))).base
            ((pullbackRightPullbackFstIso (toBase A (↥K) j)
              (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀))) (ιInf A (↥K) j) ≪≫
              pullback.congrHom (ιInf_toBase A (↥K) j) rfl ≪≫
              pullbackSpecIso A ↥(chartAlgInf A (↥K) j) Ω₀).hom.base zz) = q := by
          rw [hqdef, ← hisoI]; rfl
        rw [← h]
        rfl
      have hx : (pullback.fst (toBase A (↥K) j) (Spec.map (CommRingCat.ofHom (algebraMap A Ω₀)))).base
          ((pullback.snd (ιInf A (↥K) j) _).base zz) = (ιInf A (↥K) j).base q := by
        rw [hqdef]
        change ((pullback.snd (ιInf A (↥K) j) _) ≫ pullback.fst (toBase A (↥K) j) _).base zz =
          ((pullback.fst (ιInf A (↥K) j) _) ≫ ιInf A (↥K) j).base zz
        rw [pullback.condition]
      rw [hx]
      refine (and_congr (himI₀ zz) (himI₁ zz)).trans ?_
      refine Iff.trans ?_ (AlgebraicGeometry.not_subsingleton_minimalPrimes_span_germ_iff_exists_two_minimalPrimes_le_of_chart
        (toBase A (↥K) j) (ιInf A (↥K) j) (ιInf_toBase A (↥K) j) ϖ q).symm
      refine Iff.trans ?_ (CompNuBranch.exists_two_minimalPrimes_le_iff _ q.asIdeal
        (fun b => (b : ↥K) ∈ W₀'.nonunits) (fun b => (b : ↥K) ∈ W₁'.nonunits) hKM1' (hKM2' 0) (hKM2' 1) hKM3a').symm
      refine (and_congr (S2Cover.ker_comp_comm_le_iff A Ω₀ _ _ θInf hkerI₀ _)
        (S2Cover.ker_comp_comm_le_iff A Ω₀ _ _ θInf₁ hkerI₁ _)).trans ?_
      refine and_congr (forall_congr' fun b => ?_) (forall_congr' fun b => ?_)
      · rw [hD0I b, hq b]
      · rw [hD1I b, hq b]

  have hΩ : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A Ω₀ a = 0 := fun a ha => by
    rw [← RingHom.mem_ker, S2Cover.ker_algebraMap_eq_maximalIdeal p A L hAp Ω₀]; exact ha
  refine ⟨Mg, Mg, c₀, c₁, hc₀_over, hc₁_over, ?_, ?_, ?_, ?_, hbranch⟩
  ·
    exact Set.eq_univ_of_forall fun z => (coverAll z).elim (fun h => Or.inl h) (fun h => Or.inr h)
  ·
    refine (AlgebraicCurve.TwoChartIntegralModel.finite_setOf_pullback_fst_mem_not_subsingleton_minimalPrimes_span_germ
      A L (↥K) j htj hFD hsepK ϖ hϖ Ω₀ hΩ).subset ?_
    rintro z hz
    exact (hbranch z).mp hz
  ·
    exact AlgebraicCurve.TwoChartIntegralModel.isIso_stalkMap_genericPoint_glued_hom_of_ker_mem_minimalPrimes
      A (↥K) j Ω₀ t 1 one_pos θFin θInf (by simpa using hjFin) (by simpa using hjInf)
      c₀ hc₀_over hc₀F hc₀I hc₀match hmin₀ inferInstance hfrac₀
  ·
    exact AlgebraicCurve.TwoChartIntegralModel.isIso_stalkMap_genericPoint_glued_hom_of_ker_mem_minimalPrimes
      A (↥K) j Ω₀ t p (Fact.out : p.Prime).pos θFin₁ θInf₁ hjFin₁ hjInf₁
      c₁ hc₁_over hc₁F hc₁I hc₁match hmin₁ inferInstance hfrac₁

#print axioms solution

end S_ModularCurve_XOneP_exists_curveModel_pair_hom_specialFibre_birational_twoChartIntegralModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_curveModel_pair_hom_specialFibre_birational_twoChartIntegralModel_x1_mul (solution)
