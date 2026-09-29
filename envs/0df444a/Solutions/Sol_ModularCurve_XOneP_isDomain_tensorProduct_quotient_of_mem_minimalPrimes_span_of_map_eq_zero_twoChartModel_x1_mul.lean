-- Prove2me | solution 1 for ModularCurve.XOneP.isDomain_tensorProduct_quotient_of_mem_minimalPrimes_span_of_map_eq_zero_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/1f521fcc-d9a0-5c97-8e69-ffa1b8a4742b

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_IntermediateField_isDomain_tensorProduct_of_le_laurentSeries
import Theorems.Thm_Algebra_TensorProduct_isDomain_of_injective_of_flat
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_and_coe_eq_atkinLehnerInvolutionFull_x1_mul
import Theorems.Thm_ModularCurve_XOneP_valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
import Theorems.Thm_ModularCurve_XOneP_exists_ringHom_residueField_eq_of_gaussPresentation_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation
import Theorems.Thm_ModularCurve_XOneP_gaussReduction_mem_igusaFunctionFieldX1C_and_surjective_x1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_isDomain_tensorProduct_quotient_of_mem_minimalPrimes_span_of_map_eq_zero_twoChartModel_x1_mul
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qExpandAlgHomC_apply ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg"
p2m_attr_erase "simp" "WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "TwoChart.chartAlgFin qExpFunctionFieldC intFormRatiosC_subset x1FunctionField x1FunctionFieldC_le_of_dvd jq jq_mem coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange igusaFunctionFieldX1C jqModC jqModC_rat map_jqModC exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC XOneP.exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_and_coe_eq_atkinLehnerInvolutionFull_x1_mul XOneP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul nonempty_integralWeightOneForm transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC jqModC_mem_intFormRatiosC XOneP.exists_ringHom_residueField_eq_of_gaussPresentation_x1_mul XOneP.exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation XOneP.gaussReduction_mem_igusaFunctionFieldX1C_and_surjective_x1_mul"
namespace XOneP
p2m_export "ModularCurve.XOneP" "exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_and_coe_eq_atkinLehnerInvolutionFull_x1_mul valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul exists_ringHom_residueField_eq_of_gaussPresentation_x1_mul exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation gaussReduction_mem_igusaFunctionFieldX1C_and_surjective_x1_mul"
namespace GaussGeomInt
p2m_open "ModularCurve.XOneP ModularCurve~coeffEmb_jq"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem isDomain_tensorProduct_quotient_of_ringHom_laurentSeries
    {A : Type} [CommRing A] [IsLocalRing A]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    {B : Type} [CommRing B] [Algebra A B] (𝔓 : Ideal B) [𝔓.IsPrime]
    (θ : B →+* LaurentSeries (IsLocalRing.ResidueField A))
    (hker : ∀ b : B, b ∈ 𝔓 ↔ θ b = 0)
    (hconst : ∀ a : A, θ (algebraMap A B a) =
      algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a))
    (k : Type) [Field k] [Algebra A k] (hϖk : algebraMap A k ϖ = 0) :
    IsDomain (k ⊗[A] (B ⧸ 𝔓)) := by
  classical

  let κ := IsLocalRing.ResidueField A
  let N := B ⧸ 𝔓

  have hmk : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A k a = 0 := by
    intro a ha
    rw [hϖ] at ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hϖk, mul_zero]
  have hϖ𝔓 : algebraMap A B ϖ ∈ 𝔓 := by
    rw [hker, hconst]
    have : IsLocalRing.residue A ϖ = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, hϖ]; exact Ideal.mem_span_singleton_self ϖ
    rw [this, map_zero]
  have hmN : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A N a = 0 := by
    intro a ha
    rw [hϖ] at ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [IsScalarTower.algebraMap_apply A B N, map_mul, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_left _ _ hϖ𝔓)]

  let φk : κ →+* k := Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) (algebraMap A k) hmk
  let φN : κ →+* N := Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) (algebraMap A N) hmN
  letI : Algebra κ k := φk.toAlgebra
  letI : Algebra κ N := φN.toAlgebra
  haveI : IsScalarTower A κ k := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : IsScalarTower A κ N := IsScalarTower.of_algebraMap_eq (fun a => rfl)

  let θN : N →+* LaurentSeries κ := Ideal.Quotient.lift 𝔓 θ (fun b hb => (hker b).mp hb)
  have hθN : Function.Injective θN := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hker b).mpr hx)
  have hθNc : ∀ r : κ, θN (algebraMap κ N r) = algebraMap κ (LaurentSeries κ) r := by
    intro r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    exact hconst a
  let T : IntermediateField κ (LaurentSeries κ) := ⊤
  let f : N →ₐ[κ] ↥T :=
    { toFun := fun n => ⟨θN n, IntermediateField.mem_top⟩
      map_one' := Subtype.ext (map_one θN)
      map_mul' := fun x y => Subtype.ext (map_mul θN x y)
      map_zero' := Subtype.ext (map_zero θN)
      map_add' := fun x y => Subtype.ext (map_add θN x y)
      commutes' := fun r => Subtype.ext (hθNc r) }
  have hf : Function.Injective f := fun x y h => hθN (congrArg Subtype.val h)

  haveI : IsDomain (↥T ⊗[κ] k) := IntermediateField.isDomain_tensorProduct_of_le_laurentSeries κ k T
  haveI : IsDomain (k ⊗[κ] ↥T) := MulEquiv.isDomain (↥T ⊗[κ] k) (Algebra.TensorProduct.comm κ k ↥T).toMulEquiv
  haveI hdom : IsDomain (k ⊗[κ] N) := Algebra.TensorProduct.isDomain_of_injective_of_flat κ k N ↥T f hf

  haveI : SMulCommClass κ A k := ⟨fun r a c => by
    simp only [Algebra.smul_def]; ring⟩
  haveI : SMulCommClass A κ k := ⟨fun a r c => by
    simp only [Algebra.smul_def]; ring⟩
  haveI : TensorProduct.CompatibleSMul A κ k N := ⟨fun r c n => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    have h1 : (IsLocalRing.residue A a) • c = a • c := IsScalarTower.algebraMap_smul κ a c
    have h2 : (IsLocalRing.residue A a) • n = a • n := IsScalarTower.algebraMap_smul κ a n
    rw [h1, h2, TensorProduct.smul_tmul]⟩
  haveI : TensorProduct.CompatibleSMul κ A k N := ⟨fun a c n => by
    rw [← IsScalarTower.algebraMap_smul κ a c, ← IsScalarTower.algebraMap_smul κ a n, TensorProduct.smul_tmul]⟩
  let eL : k ⊗[A] N ≃ₗ[A] k ⊗[κ] N := TensorProduct.equivOfCompatibleSMul κ A A k N
  have heL : ∀ (c : k) (n : N), eL (c ⊗ₜ[A] n) = c ⊗ₜ[κ] n := fun _ _ => rfl
  have hmul : ∀ x y : k ⊗[A] N, eL (x * y) = eL x * eL y := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => rw [zero_mul, map_zero, zero_mul]
    | tmul c n =>
      induction y using TensorProduct.induction_on with
      | zero => rw [mul_zero, map_zero, mul_zero]
      | tmul c' n' => rw [Algebra.TensorProduct.tmul_mul_tmul, heL, heL, heL, Algebra.TensorProduct.tmul_mul_tmul]
      | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add]
    | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, add_mul]
  let eR : k ⊗[A] N ≃* k ⊗[κ] N := { toEquiv := eL.toEquiv, map_mul' := hmul }
  exact MulEquiv.isDomain (k ⊗[κ] N) eR

section Shared
p2m_open "ModularCurve~coeffEmb_jq P2MW.S_ModularCurve_XOneP_isDomain_tensorProduct_quotient_of_mem_minimalPrimes_span_of_map_eq_zero_twoChartModel_x1_mul.ModularCurve"
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

end Shared

end ModularCurve.XOneP.GaussGeomInt

p2m_open "ModularCurve~coeffEmb_jq" in open _root_.P2MW.S_ModularCurve_XOneP_isDomain_tensorProduct_quotient_of_mem_minimalPrimes_span_of_map_eq_zero_twoChartModel_x1_mul.ModularCurve ModularCurve.XOneP.GaussGeomInt in
open scoped MatrixGroups IntermediateField in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
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
    (k : Type) [Field k] [IsAlgClosed k] [Algebra A k] (hϖk : algebraMap A k ϖ = 0)
    (𝔓 : Ideal ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (h𝔓 : 𝔓 ∈ (Ideal.span {algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ϖ}).minimalPrimes) :
    IsDomain (k ⊗[A] (↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ⧸ 𝔓)) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI h𝔓prime : 𝔓.IsPrime := h𝔓.1.1

  obtain ⟨W₀, hW₀, hW₀A, hW₀m, hW₀j, hW₀nu⟩ :=
    exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC (CongruenceSubgroup.Gamma1 (M * p)) L K hK A j hj
  obtain ⟨σw, hσj, -, hσ3, -⟩ :=
    XOneP.exists_algEquiv_map_j_eq_qExpand_and_chartAlgFin_iff_and_comap_ne_and_coe_eq_atkinLehnerInvolutionFull_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj
  obtain ⟨hσW, hσj'⟩ := hσ3 W₀ hW₀
  have hσwA : ∀ a : A, σw (algebraMap A ↥K a) = algebraMap A ↥K a := by
    intro a
    rw [IsScalarTower.algebraMap_apply A L ↥K, AlgEquiv.commutes]
  obtain ⟨w⟩ := nonempty_integralWeightOneForm (IsLocalRing.ResidueField A) M (by omega)
  obtain ⟨hcomplete, -, -, -⟩ :=
    XOneP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj w ϖ hϖ W₀ hW₀ σw hσj hσW hσj'
  have hW₁A : ∀ a : A, algebraMap A ↥K a ∈ (W₀.comap (σw : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) := by
    intro a
    show (σw : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom (algebraMap A ↥K a) ∈ W₀
    rw [show (σw : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom (algebraMap A ↥K a) = σw (algebraMap A ↥K a) from rfl, hσwA]
    exact hW₀A a
  have hW₁m : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ (W₀.comap (σw : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom).nonunits := by
    intro a ha
    have : algebraMap A ↥K a ∈ (W₀.comap ((σw : ↥K ≃ₐ[L] ↥K).toRingEquiv : ↥K →+* ↥K)).nonunits := by
      rw [mem_nonunits_comap_iff]
      show σw (algebraMap A ↥K a) ∈ W₀.nonunits
      rw [hσwA]
      exact hW₀m a ha
    exact this

  have hjL : (j : LaurentSeries L) = jqModC L := by rw [hj, coeffEmb_jq]
  have htf : Transcendental L j ∧ FiniteDimensional L⟮j⟯ ↥K := by
    subst hK
    exact transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC L
      (CongruenceSubgroup.Gamma1 (M * p)) (T_mem_Gamma1 _) j hjL
  haveI := htf.2
  have htj : Transcendental A j := fun h => htf.1 (h.extendScalars (IsFractionRing.injective A L))
  haveI hsep : Algebra.IsSeparable L⟮j⟯ ↥K := Algebra.IsSeparable.of_integral _ _

  obtain ⟨hmin, -, -, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_span_iff_of_valuationSubring_pair
      A L ↥K j htj htf.2 hsep ϖ hϖ W₀ (W₀.comap (σw : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom)
      (by
        intro i
        fin_cases i
        · exact ⟨hW₀A, hW₀m⟩
        · exact ⟨hW₁A, hW₁m⟩)
      (by
        intro i
        fin_cases i
        · exact hW₀j
        · exact hσj')
      (fun h => hσW h.symm) hcomplete
  rcases hmin 𝔓 h𝔓 with h0 | h1
  ·
    obtain ⟨hBW, -, -⟩ :=
      AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
        A L ↥K j htj htf.2 hsep W₀ hW₀A hW₀m hW₀j

    let K' : IntermediateField L (LaurentSeries L) := laurentBaseChange L (x1FunctionField M)
    letI : Algebra A ↥K' := ((algebraMap L ↥K').comp (algebraMap A L)).toAlgebra
    haveI : IsScalarTower A L ↥K' := IsScalarTower.of_algebraMap_eq' rfl
    have hle : K' ≤ K := by
      rw [hK]
      change laurentBaseChange L _ ≤ laurentBaseChange L _
      rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
      rintro _ ⟨y, hy, rfl⟩
      exact coeffEmb_mem_laurentBaseChange L (x1FunctionFieldC_le_of_dvd ℚ (dvd_mul_right M p) hy)
    have hjK' : (j : LaurentSeries L) ∈ K' := by
      rw [hj]; exact coeffEmb_mem_laurentBaseChange L (jq_mem (CongruenceSubgroup.Gamma1 M))
    let j' : ↥K' := ⟨(j : LaurentSeries L), hjK'⟩
    have hj' : ((j' : LaurentSeries L)) = coeffEmb L jq := hj
    haveI : Fact (j' ≠ 0) := ⟨fun h0 => (Fact.out : j ≠ 0) (Subtype.ext (congrArg Subtype.val h0 : (j : LaurentSeries L) = 0))⟩
    let W₀' : ValuationSubring ↥K' := W₀.comap (IntermediateField.inclusion hle).toRingHom
    have hW₀' : ∀ f' : ↥K', f' ∈ W₀' ↔ IntermediateField.inclusion hle f' ∈ W₀ := fun _ => Iff.rfl
    obtain ⟨e, -, he, -, -, -, -, -, heconst, -, -⟩ :=
      XOneP.exists_ringHom_residueField_eq_of_gaussPresentation_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj
        K' rfl hle j' hj' w W₀ hW₀ W₀' hW₀'

    let ι₀ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* ↥W₀ :=
      { toFun := fun b => ⟨(b : ↥K), hBW b⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let θ₀ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* LaurentSeries (IsLocalRing.ResidueField A) := e.comp ((IsLocalRing.residue ↥W₀).comp ι₀)
    refine isDomain_tensorProduct_quotient_of_ringHom_laurentSeries ϖ hϖ 𝔓 θ₀ (fun b => ?_) (fun a => ?_) k hϖk
    · refine (h0 b).trans ?_
      show _ ↔ e (IsLocalRing.residue ↥W₀ (ι₀ b)) = 0
      rw [map_eq_zero_iff e he, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
      rfl
    · show e (IsLocalRing.residue ↥W₀ (ι₀ (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a))) = _
      have : ι₀ (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a) = ⟨algebraMap A ↥K a, hW₀A a⟩ :=
        Subtype.ext (show ((algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) = algebraMap A ↥K a from Subalgebra.coe_algebraMap _ a)
      rw [this]
      exact heconst a (hW₀A a)
  ·
    obtain ⟨hBW, -, -⟩ :=
      AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
        A L ↥K j htj htf.2 hsep (W₀.comap (σw : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) hW₁A hW₁m hσj'
    obtain ⟨hmem, hsurj⟩ := XOneP.gaussReduction_mem_igusaFunctionFieldX1C_and_surjective_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj w
    obtain ⟨θ, -, hθconst⟩ :=
      XOneP.exists_ringEquiv_residueField_comap_igusaFunctionFieldX1C_of_gaussPresentation
        L K A W₀ hW₀ hW₀nu hW₀A M w hmem hsurj σw hσwA hW₁A
    let ι₁ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* ↥(W₀.comap (σw : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom) :=
      { toFun := fun b => ⟨(b : ↥K), hBW b⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let θ₁ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* LaurentSeries (IsLocalRing.ResidueField A) :=
      (algebraMap ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w) (LaurentSeries (IsLocalRing.ResidueField A))).comp
        (θ.toRingHom.comp ((IsLocalRing.residue _).comp ι₁))
    refine isDomain_tensorProduct_quotient_of_ringHom_laurentSeries ϖ hϖ 𝔓 θ₁ (fun b => ?_) (fun a => ?_) k hϖk
    · refine (h1 b).trans ?_
      show _ ↔ algebraMap ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w) (LaurentSeries (IsLocalRing.ResidueField A))
        (θ (IsLocalRing.residue _ (ι₁ b))) = 0
      rw [map_eq_zero_iff _ (algebraMap ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w) (LaurentSeries (IsLocalRing.ResidueField A))).injective,
        map_eq_zero_iff θ θ.injective, IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
      rfl
    · show algebraMap ↥(igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w) (LaurentSeries (IsLocalRing.ResidueField A))
        (θ (IsLocalRing.residue _ (ι₁ (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a)))) = _
      have : ι₁ (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a) = ⟨algebraMap A ↥K a, hW₁A a⟩ :=
        Subtype.ext (show ((algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) = algebraMap A ↥K a from Subalgebra.coe_algebraMap _ a)
      rw [this, hθconst a, ← IsScalarTower.algebraMap_apply]

end S_ModularCurve_XOneP_isDomain_tensorProduct_quotient_of_mem_minimalPrimes_span_of_map_eq_zero_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_isDomain_tensorProduct_quotient_of_mem_minimalPrimes_span_of_map_eq_zero_twoChartModel_x1_mul (solution)
