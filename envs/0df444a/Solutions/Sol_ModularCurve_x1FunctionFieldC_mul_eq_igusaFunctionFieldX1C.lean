-- Prove2me | solution 1 for ModularCurve.x1FunctionFieldC_mul_eq_igusaFunctionFieldX1C
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/22364f32-118c-502c-97c6-4bc5af943a46

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_XOneP_gaussReduction_mem_igusaFunctionFieldX1C_and_surjective_x1_mul
import Theorems.Thm_ModularCurve_adjoin_image_coeffMap_igusaFunctionFieldX1C_eq
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_x1FunctionField
import Theorems.Thm_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
import Theorems.Thm_ModularCurve_mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb
import Theorems.Thm_ModularCurve_coeffEmb_jq_mem_laurentBaseChange_x1FunctionField
import Theorems.Thm_ModularCurve_coeffEmb_jq_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_x1FunctionFieldC_mul_eq_igusaFunctionFieldX1C
p2m_attr_erase "instance" "AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply"
p2m_attr_erase "simp" "TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec"
p2m_attr_erase "simp" "TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MatrixGroups

namespace ResidME96

open ModularCurve UpperHalfPlane

section contentZ
variable (p : ℕ) [hp : Fact p.Prime]

theorem exists_eq_C_mul_of_forall_dvd (P : PowerSeries ℤ) (h : ∀ n, (p : ℤ) ∣ PowerSeries.coeff n P) :
    ∃ P' : PowerSeries ℤ, P = PowerSeries.C (p : ℤ) * P' := by
  choose c hc using h
  refine ⟨PowerSeries.mk c, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc n]

include hp in

theorem exists_eq_C_pow_mul_not_dvd (P : PowerSeries ℤ) (hP : P ≠ 0) :
    ∃ (a : ℕ) (P₁ : PowerSeries ℤ), P = PowerSeries.C ((p : ℤ) ^ a) * P₁ ∧
      ∃ n, ¬ (p : ℤ) ∣ PowerSeries.coeff n P₁ := by
  obtain ⟨n, hn⟩ : ∃ n, PowerSeries.coeff n P ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (PowerSeries.ext fun n => by simpa using h n)
  suffices H : ∀ (N : ℕ) (Q : PowerSeries ℤ), PowerSeries.coeff n Q ≠ 0 → (PowerSeries.coeff n Q).natAbs ≤ N →
      ∃ (a : ℕ) (Q₁ : PowerSeries ℤ), Q = PowerSeries.C ((p : ℤ) ^ a) * Q₁ ∧ ∃ m, ¬ (p : ℤ) ∣ PowerSeries.coeff m Q₁ from
    H _ P hn le_rfl
  intro N
  induction N with
  | zero =>
    intro Q hQ hle
    exact absurd (Int.natAbs_eq_zero.mp (Nat.le_zero.mp hle)) hQ
  | succ N ih =>
    intro Q hQ hle
    by_cases hall : ∀ m, (p : ℤ) ∣ PowerSeries.coeff m Q
    · obtain ⟨Q', rfl⟩ := exists_eq_C_mul_of_forall_dvd p Q hall
      rw [PowerSeries.coeff_C_mul] at hQ hle
      have hQ' : PowerSeries.coeff n Q' ≠ 0 := fun h => hQ (by rw [h, mul_zero])
      have hlt : (PowerSeries.coeff n Q').natAbs ≤ N := by
        rw [Int.natAbs_mul, Int.natAbs_natCast] at hle
        have h2 : 2 * (PowerSeries.coeff n Q').natAbs ≤ p * (PowerSeries.coeff n Q').natAbs :=
          Nat.mul_le_mul_right _ hp.out.two_le
        have h3 : 1 ≤ (PowerSeries.coeff n Q').natAbs := Int.natAbs_pos.mpr hQ'
        have h4 : 2 * (PowerSeries.coeff n Q').natAbs ≤ N + 1 := le_trans h2 hle
        omega
      obtain ⟨a, Q₁, hQ₁, hm⟩ := ih Q' hQ' hlt
      exact ⟨a + 1, Q₁, by rw [hQ₁, ← mul_assoc, ← map_mul, pow_succ'], hm⟩
    · push Not at hall
      exact ⟨0, Q, by simp, hall⟩

end contentZ

section rescale
variable {M : ℕ}

local notation "Γ₁" => ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem strictPeriods_one : (1 : ℝ) ∈ (Γ₁ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]; exact ⟨1, by simp⟩

theorem isIntegralQExp_inv_smul {k : ℤ} (f : ModularForm Γ₁ k) {pf pf' : PowerSeries ℤ} (c : ℤ) (hc : c ≠ 0)
    (hf : IsIntegralQExp f pf) (h : pf = PowerSeries.C c * pf') :
    IsIntegralQExp (⇑(((c : ℂ))⁻¹ • f)) pf' := by
  unfold IsIntegralQExp at *
  have han : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero f one_pos strictPeriods_one
  rw [ModularForm.IsGLPos.coe_smul, qExpansion_smul han, ← hf, h, map_mul, PowerSeries.map_C,
    eq_intCast, PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hc),
    map_one, one_mul]

end rescale

section unif
variable {A : Type*} [CommRing A] [IsDomain A] [IsLocalRing A]

theorem exists_unit_natCast_eq_mul_pow (p : ℕ) [hp : Fact p.Prime] (z : A) (hz : z ^ p = 1) (hz1 : z ≠ 1)
    (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    ∃ u : Aˣ, (p : A) = u * (z - 1) ^ (p - 1) ∧ (z - 1) ∈ IsLocalRing.maximalIdeal A := by
  set π := z - 1 with hπ
  have hπ0 : π ≠ 0 := sub_ne_zero.mpr hz1
  have hp1 : 1 ≤ p := hp.out.one_le
  have hp2 : 2 ≤ p := hp.out.two_le
  have hz' : z = π + 1 := by rw [hπ]; ring

  have hsum : ∑ k ∈ Finset.Ico 0 (p + 1), π ^ k * (p.choose k : A) = 1 := by
    have := add_pow π 1 p
    simp only [one_pow, mul_one] at this
    rw [← Finset.range_eq_Ico, ← this, ← hz', hz]

  have hd : ∀ k ∈ Finset.Ico 2 p, p * (p.choose k / p) = p.choose k := fun k hk => by
    rw [Finset.mem_Ico] at hk
    exact Nat.mul_div_cancel' (hp.out.dvd_choose_self (by omega) hk.2)
  let m : A := ∑ k ∈ Finset.Ico 2 p, π ^ (k - 1) * ((p.choose k / p : ℕ) : A)
  have hmid : ∑ k ∈ Finset.Ico 2 p, π ^ k * (p.choose k : A) = (p : A) * π * m := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := by rw [Finset.mem_Ico] at hk; omega
    have hpow : π ^ k = π ^ (k - 1) * π := by rw [← pow_succ, Nat.sub_add_cancel hk1]
    conv_lhs => rw [← hd k hk, hpow]
    push_cast
    ring

  have hsplit : ∑ k ∈ Finset.Ico 0 (p + 1), π ^ k * (p.choose k : A) = 1 + ((p : A) * π + (p : A) * π * m + π ^ p) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < p + 1), Finset.sum_Ico_succ_top (by omega : 1 ≤ p),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < p), hmid]
    simp [Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self]
    ring
  have hkey : π * ((p : A) * (1 + m) + π ^ (p - 1)) = 0 := by
    have e : (p : A) * π + (p : A) * π * m + π ^ p = 0 := by linear_combination hsum - hsplit
    have hpow : π ^ p = π ^ (p - 1) * π := by rw [← pow_succ, Nat.sub_add_cancel hp1]
    rw [hpow] at e
    linear_combination e
  have hkey' : (p : A) * (1 + m) = -π ^ (p - 1) := by
    have := (mul_eq_zero.mp hkey).resolve_left hπ0
    linear_combination this

  have hπm : π ∈ IsLocalRing.maximalIdeal A := by
    have h1 : π ^ (p - 1) ∈ IsLocalRing.maximalIdeal A := by
      rw [show π ^ (p - 1) = (p : A) * (-(1 + m)) by linear_combination hkey']
      exact Ideal.mul_mem_right _ _ hpA
    exact Ideal.IsPrime.mem_of_pow_mem inferInstance _ h1

  have hm : m ∈ IsLocalRing.maximalIdeal A := by
    refine Ideal.sum_mem _ fun k hk => ?_
    have hk2 : 2 ≤ k := by rw [Finset.mem_Ico] at hk; exact hk.1
    have : π ^ (k - 1) ∈ IsLocalRing.maximalIdeal A :=
      Ideal.pow_mem_of_mem _ hπm _ (by omega)
    exact Ideal.mul_mem_right _ _ this
  have hu : IsUnit (1 + m) := by
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (-m) with h | h
    · exact absurd h ((IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.maximalIdeal A).neg_mem hm))
    · simpa using h
  refine ⟨-(hu.unit⁻¹), ?_, hπm⟩
  calc (p : A) = p * ((1 + m) * ↑hu.unit⁻¹) := by rw [hu.mul_val_inv, mul_one]
    _ = ((p : A) * (1 + m)) * ↑hu.unit⁻¹ := by ring
    _ = -π ^ (p - 1) * ↑hu.unit⁻¹ := by rw [hkey']
    _ = ↑(-hu.unit⁻¹) * π ^ (p - 1) := by rw [Units.val_neg]; ring

end unif

section helpers

theorem coeffEmb_intSeriesC (L : Type*) [Field L] [CharZero L] (q : PowerSeries ℤ) :
    coeffEmb L (intSeriesC ℚ q) = intSeriesC L q := by
  ext n
  rw [coeffEmb_coeff, intSeriesC, intSeriesC, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs <;> simp

theorem map_intCast_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (q : PowerSeries ℤ) :
    (q.map (Int.castRingHom R)).map φ = q.map (Int.castRingHom S) := by
  have h : φ.comp (Int.castRingHom R) = Int.castRingHom S := RingHom.ext_int _ _
  rw [← h, PowerSeries.map_comp, RingHom.comp_apply]

theorem intSeriesC_eq_map_map (F : Type*) [Field F] {R : Type*} [CommRing R] (φ : R →+* F) (q : PowerSeries ℤ) :
    intSeriesC F q = HahnSeries.ofPowerSeries ℤ F ((q.map (Int.castRingHom R)).map φ) := by
  rw [intSeriesC, map_intCast_map]

theorem intSeriesC_C_mul (F : Type*) [Field F] (c : ℤ) (q : PowerSeries ℤ) :
    intSeriesC F (PowerSeries.C c * q) = HahnSeries.C (c : F) * intSeriesC F q := by
  rw [intSeriesC_mul]
  congr 1
  simp [intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]

theorem intSeriesC_ne_zero_of_ne_zero (F : Type*) [Field F] [CharZero F] {q : PowerSeries ℤ} (hq : q ≠ 0) :
    intSeriesC F q ≠ 0 := by
  intro h
  apply hq
  apply PowerSeries.map_injective (Int.castRingHom F) Int.cast_injective
  rw [map_zero]
  exact HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)

theorem map_ne_zero_of_not_dvd (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] {q : PowerSeries ℤ}
    {n : ℕ} (hn : ¬ (p : ℤ) ∣ PowerSeries.coeff n q) : q.map (Int.castRingHom F) ≠ 0 := by
  intro h
  have := congrArg (PowerSeries.coeff n) h
  rw [PowerSeries.coeff_map, map_zero, eq_intCast, CharP.intCast_eq_zero_iff F p] at this
  exact hn this

theorem intSeriesC_ne_zero_of_not_dvd (F : Type*) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] {q : PowerSeries ℤ}
    {n : ℕ} (hn : ¬ (p : ℤ) ∣ PowerSeries.coeff n q) : intSeriesC F q ≠ 0 := by
  intro h
  exact map_ne_zero_of_not_dvd F p hn (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))

theorem algebraMap_laurent_eq_C (F : Type*) [Field F] (a : F) : algebraMap F (LaurentSeries F) a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply']; simp

theorem exists_content (p : ℕ) [Fact p.Prime] (P : PowerSeries ℤ) :
    ∃ (a : ℕ) (P₁ : PowerSeries ℤ), P = PowerSeries.C ((p : ℤ) ^ a) * P₁ ∧
      (P ≠ 0 → ∃ n, ¬ (p : ℤ) ∣ PowerSeries.coeff n P₁) := by
  by_cases hP : P = 0
  · exact ⟨0, P, by simp, fun h => absurd hP h⟩
  · obtain ⟨a, P₁, h1, h2⟩ := exists_eq_C_pow_mul_not_dvd p P hP
    exact ⟨a, P₁, h1, fun _ => h2⟩

theorem exp_inj {d : ℕ} (hd : 0 < d) {i i' n n' : ℕ} (hi : i < d) (hi' : i' < d)
    (h : i + d * n = i' + d * n') : i = i' ∧ n = n' := by
  have h1 : (i + d * n) % d = (i' + d * n') % d := by rw [h]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at h1
  subst h1
  refine ⟨rfl, ?_⟩
  have h2 : d * n = d * n' := by omega
  exact Nat.eq_of_mul_eq_mul_left hd h2

end helpers

end ResidME96

set_option maxHeartbeats 16000000 in

theorem descent_Mp
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (f : ↥K) (x y : PowerSeries A) (hy : y.map (IsLocalRing.residue A) ≠ 0)
    (hxy : (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
      = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :
    HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A))
      ∈ ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * p) := by
  haveI hMp0 : NeZero (M * p) := ⟨mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  classical
  haveI hp := (inferInstance : Fact p.Prime)

  let κ := IsLocalRing.ResidueField A

  have hpk : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A) p, IsLocalRing.residue_eq_zero_iff]; exact hAp
  haveI : CharP (IsLocalRing.ResidueField A) p :=
    ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp.out hpk)
  have hinjAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  have hinjAK : Function.Injective (algebraMap A ↥K) := by
    rw [IsScalarTower.algebraMap_eq A L ↥K]
    exact (algebraMap L ↥K).injective.comp hinjAL
  have hcoeA : ∀ a : A, ((algebraMap A ↥K a : ↥K) : LaurentSeries L) = HahnSeries.C (algebraMap A L a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply A L ↥K]
    show algebraMap L (LaurentSeries L) (algebraMap A L a) = _
    exact ResidME96.algebraMap_laurent_eq_C L _

  obtain ⟨W₀, h1, h2, h3, h4, h5⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_x1FunctionField (M * p) L K hK A j hj
  obtain ⟨red, hred, hker⟩ :=
    ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries L K A W₀ h1 h5
  have hfW : f ∈ W₀ := (h1 f).mpr ⟨x, y, hy, hxy⟩
  rw [← hred ⟨f, hfW⟩ x y hy hxy]
  set fW : ↥W₀ := ⟨f, hfW⟩ with hfWdef

  let ψ : ↥W₀ →+* LaurentSeries L := (K.toSubfield.subtype).comp W₀.subtype
  have hψ : ∀ w : ↥W₀, ψ w = ((w : ↥K) : LaurentSeries L) := fun w => rfl
  have hψinj : Function.Injective ψ := fun a b hab => Subtype.ext (Subtype.ext hab)

  have hmaxW : ∀ w : ↥W₀, w ∈ IsLocalRing.maximalIdeal ↥W₀ ↔ (w : ↥K) ∈ W₀.nonunits :=
    fun w => (ValuationSubring.coe_mem_nonunits_iff).symm
  have hred0 : ∀ w : ↥W₀, w ∈ IsLocalRing.maximalIdeal ↥W₀ → red w = 0 := fun w hw => by
    rw [← RingHom.mem_ker, hker]; exact hw
  have hred_ne : ∀ w : ↥W₀, red w ≠ 0 → IsUnit w := fun w hw => by
    by_contra hnu
    exact hw (hred0 w ((IsLocalRing.mem_maximalIdeal _).mpr hnu))

  obtain ⟨z, hz⟩ := hζA
  have hzp : z ^ p = 1 := hinjAL (by rw [map_pow, hz, hζ.pow_eq_one, map_one])
  have hz1 : z ≠ 1 := fun h => hζ.ne_one hp.out.one_lt (by rw [← hz, h, map_one])
  obtain ⟨ε, hε, hπm⟩ := ResidME96.exists_unit_natCast_eq_mul_pow p z hzp hz1 hAp
  set π : A := z - 1 with hπdef
  have hπL : algebraMap A L π = ζ - 1 := by rw [hπdef, map_sub, hz, map_one]
  have hpL : (p : L) = algebraMap A L ε * (ζ - 1) ^ (p - 1) := by
    rw [← hπL, ← map_pow, ← map_mul, ← hε, map_natCast]
  have hp0L : (p : L) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  obtain ⟨πW, hπWdef⟩ : ∃ w : ↥W₀, (w : ↥K) = algebraMap A ↥K π := ⟨⟨_, h2 π⟩, rfl⟩
  obtain ⟨εW, hεWdef⟩ : ∃ w : ↥W₀, (w : ↥K) = algebraMap A ↥K (ε : A) := ⟨⟨_, h2 _⟩, rfl⟩
  have hψπ : ψ πW = HahnSeries.C (ζ - 1) := by rw [hψ, hπWdef, hcoeA, hπL]
  have hψε : ψ εW = HahnSeries.C (algebraMap A L ε) := by rw [hψ, hεWdef, hcoeA]
  have hπW0 : πW ≠ 0 := by
    intro h
    have := congrArg ψ h
    rw [hψπ, map_zero] at this
    exact HahnSeries.C_ne_zero (sub_ne_zero.mpr (hζ.ne_one hp.out.one_lt)) this
  have hπmax : πW ∈ IsLocalRing.maximalIdeal ↥W₀ := (hmaxW πW).mpr (by rw [hπWdef]; exact h3 π hπm)
  have hredπ : red πW = 0 := hred0 πW hπmax

  have hredε : red εW = HahnSeries.C (IsLocalRing.residue A ε) := by
    have e1 := hred εW (PowerSeries.C (ε : A)) 1 (by rw [map_one]; exact one_ne_zero) (by
      rw [map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, hεWdef]
      exact hcoeA ε)
    rw [e1, map_one, map_one, div_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]
  have hεbar : IsLocalRing.residue A ε ≠ 0 := ((Units.isUnit ε).map (IsLocalRing.residue A)).ne_zero
  have hredε0 : red εW ≠ 0 := by rw [hredε]; exact HahnSeries.C_ne_zero hεbar
  have hεunit : IsUnit εW := hred_ne εW hredε0

  have hpW : (p : ↥W₀) = εW * πW ^ (p - 1) := by
    apply hψinj
    rw [map_natCast, map_mul, map_pow, hψε, hψπ, ← map_pow, ← map_mul, ← hpL, map_natCast]
  have hpLL : (p : LaurentSeries L) = HahnSeries.C (p : L) := (map_natCast (HahnSeries.C (Γ := ℤ) (R := L)) p).symm
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero

  set pb := hζ.subOnePowerBasis ℚ with hpb
  have hgen : pb.gen = ζ - 1 := by rw [hpb, IsPrimitiveRoot.subOnePowerBasis_gen]
  have hdim : pb.dim = p - 1 := by
    rw [← pb.finrank, IsCyclotomicExtension.finrank L (Polynomial.cyclotomic.irreducible_rat hp.out.pos),
      Nat.totient_prime hp.out]
  have hfK : (f : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)) := hK ▸ f.2
  obtain ⟨h, hfsum⟩ :=
    (ModularCurve.mem_laurentBaseChange_iff_exists_eq_sum_smul_coeffEmb L pb.basis (ModularCurve.x1FunctionField (M * p))
      (f : LaurentSeries L)).mp hfK
  have hb : ∀ i, pb.basis i = (ζ - 1) ^ (i : ℕ) := fun i => by rw [PowerBasis.basis_eq_pow, hgen]

  have hrat : ∀ i, ∃ (k : ℤ) (ff gg : ModularForm ((CongruenceSubgroup.Gamma1 (M * p) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
      (pf pg : PowerSeries ℤ), ModularCurve.IsIntegralQExp ff pf ∧ ModularCurve.IsIntegralQExp gg pg ∧
      ModularCurve.intSeriesC ℚ pg ≠ 0 ∧ ((h i : ↥(ModularCurve.x1FunctionField (M * p))) : LaurentSeries ℚ)
        = ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg :=
    fun i => (ModularCurve.mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC (CongruenceSubgroup.Gamma1 (M * p))
      ResidME96.strictPeriods_one _).mp (h i).2
  choose kw ff gg pf pg hff hgg hpg0 hhi using hrat

  choose a pf' hpfeq hpf'nd using fun i => ResidME96.exists_content p (pf i)
  choose bq pg' hpgeq hpg'nd using fun i => ResidME96.exists_content p (pg i)
  have hpg_ne : ∀ i, pg i ≠ 0 := fun i h0 => hpg0 i (by rw [h0, ModularCurve.intSeriesC_zero])
  have hpg'nd' : ∀ i, ∃ n, ¬ (p : ℤ) ∣ PowerSeries.coeff n (pg' i) := fun i => hpg'nd i (hpg_ne i)
  have hpg'_ne : ∀ i, pg' i ≠ 0 := fun i h0 => hpg_ne i (by rw [hpgeq i, h0, mul_zero])
  have hpf'_of : ∀ i, pf i = 0 → pf' i = 0 := fun i h0 => by
    have h' := hpfeq i
    rw [h0] at h'
    refine PowerSeries.ext fun m => ?_
    have := congrArg (PowerSeries.coeff m) h'
    rw [map_zero, PowerSeries.coeff_C_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ hpZ)

  let ff' := fun i => ((((p : ℤ) ^ a i : ℤ) : ℂ))⁻¹ • ff i
  let gg' := fun i => ((((p : ℤ) ^ bq i : ℤ) : ℂ))⁻¹ • gg i
  have hff' : ∀ i, ModularCurve.IsIntegralQExp (⇑(ff' i)) (pf' i) := fun i =>
    ResidME96.isIntegralQExp_inv_smul (ff i) ((p : ℤ) ^ a i) (pow_ne_zero _ hpZ) (hff i) (hpfeq i)
  have hgg' : ∀ i, ModularCurve.IsIntegralQExp (⇑(gg' i)) (pg' i) := fun i =>
    ResidME96.isIntegralQExp_inv_smul (gg i) ((p : ℤ) ^ bq i) (pow_ne_zero _ hpZ) (hgg i) (hpgeq i)

  let U : Fin pb.dim → LaurentSeries L := fun i => ModularCurve.intSeriesC L (pf' i) / ModularCurve.intSeriesC L (pg' i)
  have hUdef : ∀ i, U i = ModularCurve.intSeriesC L (pf' i) / ModularCurve.intSeriesC L (pg' i) := fun i => rfl
  have hUQ : ∀ i, ModularCurve.intSeriesC ℚ (pf' i) / ModularCurve.intSeriesC ℚ (pg' i) ∈ ModularCurve.x1FunctionField (M * p) :=
    fun i => ModularCurve.div_mem_qExpFunctionFieldC (ff' i) (gg' i) (hff' i) (hgg' i)
      (ResidME96.intSeriesC_ne_zero_of_ne_zero ℚ (hpg'_ne i))
  have hUeq : ∀ i, U i = ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ (pf' i) / ModularCurve.intSeriesC ℚ (pg' i)) :=
    fun i => by rw [map_div₀, ResidME96.coeffEmb_intSeriesC, ResidME96.coeffEmb_intSeriesC]
  have hUK : ∀ i, U i ∈ K := fun i => by
    rw [hK, hUeq]; exact ModularCurve.coeffEmb_mem_laurentBaseChange L (hUQ i)
  let uK : Fin pb.dim → ↥K := fun i => ⟨U i, hUK i⟩

  have hYbar : ∀ i, ((pg' i).map (Int.castRingHom A)).map (IsLocalRing.residue A) ≠ 0 := fun i => by
    rw [ResidME96.map_intCast_map]
    obtain ⟨n, hn⟩ := hpg'nd' i
    exact ResidME96.map_ne_zero_of_not_dvd _ p hn
  have hpres : ∀ i, ((uK i : ↥K) : LaurentSeries L) *
      HahnSeries.ofPowerSeries ℤ L (((pg' i).map (Int.castRingHom A)).map (algebraMap A L))
      = HahnSeries.ofPowerSeries ℤ L (((pf' i).map (Int.castRingHom A)).map (algebraMap A L)) := fun i => by
    rw [← ResidME96.intSeriesC_eq_map_map L (algebraMap A L), ← ResidME96.intSeriesC_eq_map_map L (algebraMap A L)]
    exact div_mul_cancel₀ _ (ResidME96.intSeriesC_ne_zero_of_ne_zero L (hpg'_ne i))
  have huW : ∀ i, uK i ∈ W₀ := fun i => (h1 _).mpr ⟨_, _, hYbar i, hpres i⟩
  let uW : Fin pb.dim → ↥W₀ := fun i => ⟨uK i, huW i⟩
  have hψu : ∀ i, ψ (uW i) = U i := fun i => rfl
  have hredu : ∀ i, red (uW i) = ModularCurve.intSeriesC (IsLocalRing.ResidueField A) (pf' i) /
      ModularCurve.intSeriesC (IsLocalRing.ResidueField A) (pg' i) := fun i => by
    rw [hred (uW i) _ _ (hYbar i) (hpres i), ← ResidME96.intSeriesC_eq_map_map _ (IsLocalRing.residue A),
      ← ResidME96.intSeriesC_eq_map_map _ (IsLocalRing.residue A)]
  have hredu_mem : ∀ i, red (uW i) ∈ ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * p) := fun i => by
    rw [hredu]
    obtain ⟨n, hn⟩ := hpg'nd' i
    exact ModularCurve.div_mem_qExpFunctionFieldC (ff' i) (gg' i) (hff' i) (hgg' i)
      (ResidME96.intSeriesC_ne_zero_of_not_dvd _ p hn)
  have hredu_ne : ∀ i, pf i ≠ 0 → red (uW i) ≠ 0 := fun i hi => by
    rw [hredu]
    obtain ⟨n, hn⟩ := hpf'nd i hi
    obtain ⟨n', hn'⟩ := hpg'nd' i
    exact div_ne_zero (ResidME96.intSeriesC_ne_zero_of_not_dvd _ p hn) (ResidME96.intSeriesC_ne_zero_of_not_dvd _ p hn')

  let B : ℕ := ∑ i, bq i
  have hbB : ∀ i, bq i ≤ B := fun i => Finset.single_le_sum (fun i _ => Nat.zero_le (bq i)) (Finset.mem_univ i)
  let n : Fin pb.dim → ℕ := fun i => a i + (B - bq i)
  let e : Fin pb.dim → ℕ := fun i => (i : ℕ) + (p - 1) * n i

  have hE1 : ∀ i, (HahnSeries.C (p : L)) ^ B * (pb.basis i • ModularCurve.coeffEmb L ((h i : ↥(ModularCurve.x1FunctionField (M * p))) : LaurentSeries ℚ))
      = HahnSeries.C (algebraMap A L ((ε : A) ^ n i * π ^ e i)) * U i := fun i => by
    rw [hb i, ← HahnSeries.C_mul_eq_smul, hhi i, map_div₀, ResidME96.coeffEmb_intSeriesC,
      ResidME96.coeffEmb_intSeriesC, hpfeq i, hpgeq i, ResidME96.intSeriesC_C_mul, ResidME96.intSeriesC_C_mul, hUdef]
    have hG : ModularCurve.intSeriesC L (pg' i) ≠ 0 := ResidME96.intSeriesC_ne_zero_of_ne_zero L (hpg'_ne i)
    have hCpb : (HahnSeries.C ((((p : ℤ) ^ bq i : ℤ) : L)) : LaurentSeries L) ≠ 0 :=
      HahnSeries.C_ne_zero (by exact_mod_cast pow_ne_zero _ hp.out.ne_zero)

    have hscal : (p : L) ^ B * ((ζ - 1) ^ (i : ℕ) * (((p : ℤ) ^ a i : ℤ) : L)) =
        algebraMap A L ((ε : A) ^ n i * π ^ e i) * (((p : ℤ) ^ bq i : ℤ) : L) := by
      rw [map_mul, map_pow, map_pow, hπL]
      simp only [Int.cast_pow, Int.cast_natCast]
      have hsplit : (p : L) ^ B = (p : L) ^ (B - bq i) * (p : L) ^ (bq i) := by
        rw [← pow_add, Nat.sub_add_cancel (hbB i)]
      rw [hsplit]
      simp only [e, n, pow_add, pow_mul, mul_pow]
      rw [hpL]
      ring
    have hscalC := congrArg (HahnSeries.C (Γ := ℤ) (R := L)) hscal
    simp only [map_mul, map_pow] at hscalC
    have hs' : HahnSeries.C (algebraMap A L ((ε : A) ^ n i * π ^ e i)) =
        (HahnSeries.C (p : L)) ^ B * ((HahnSeries.C (ζ - 1)) ^ (i : ℕ) * HahnSeries.C (((p : ℤ) ^ a i : ℤ) : L)) *
          (HahnSeries.C ((((p : ℤ) ^ bq i : ℤ) : L)) : LaurentSeries L)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hCpb, hscalC]
      simp only [map_mul, map_pow]
    rw [hs', map_pow]
    field_simp
  have hE1sum : (HahnSeries.C (p : L)) ^ B * (f : LaurentSeries L)
      = ∑ i, HahnSeries.C (algebraMap A L ((ε : A) ^ n i * π ^ e i)) * U i := by
    rw [hfsum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => hE1 i)

  set I := Finset.univ.filter (fun i => pf i ≠ 0) with hI
  have hUzero : ∀ i, i ∉ I → U i = 0 := fun i hi => by
    have : pf i = 0 := by simpa [hI] using hi
    rw [hUdef, hpf'_of i this, ModularCurve.intSeriesC_zero, zero_div]
  by_cases hIe : I = ∅
  ·
    have hall : ∀ i, U i = 0 := fun i => hUzero i (by rw [hIe]; exact Finset.notMem_empty _)
    have hf0 : (HahnSeries.C (p : L)) ^ B * (f : LaurentSeries L) = 0 := by
      rw [hE1sum]; exact Finset.sum_eq_zero (fun i _ => by rw [hall i, mul_zero])
    have hf0' : (f : LaurentSeries L) = 0 :=
      (mul_eq_zero.mp hf0).resolve_left (pow_ne_zero _ (HahnSeries.C_ne_zero hp0L))
    have : fW = 0 := Subtype.ext (Subtype.ext hf0')
    rw [this, map_zero]; exact zero_mem _
  · obtain ⟨i₀, hi₀I, hmin⟩ := Finset.exists_min_image I e (Finset.nonempty_iff_ne_empty.mpr hIe)
    have hpf0 : pf i₀ ≠ 0 := (Finset.mem_filter.mp hi₀I).2
    have hlt : ∀ i ∈ I, i ≠ i₀ → e i₀ < e i := fun i hi hne => by
      refine lt_of_le_of_ne (hmin i hi) (fun heq => hne ?_)
      have hh := ResidME96.exp_inj (d := p - 1) (by omega) (by rw [← hdim]; exact i.isLt) (by rw [← hdim]; exact i₀.isLt) heq.symm
      exact Fin.ext hh.1

    let gW : ↥W₀ := ∑ i ∈ I, εW ^ n i * πW ^ (e i - e i₀) * uW i

    have hE2 : (p : ↥W₀) ^ B * fW = πW ^ e i₀ * gW := by
      apply hψinj
      rw [map_mul, map_pow, map_natCast, hψ fW, hpLL]
      show (HahnSeries.C (p : L)) ^ B * (f : LaurentSeries L) = _
      rw [hE1sum, map_mul, map_pow, hψπ, map_sum,
        ← Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by rw [hUzero i hi, mul_zero]), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [map_mul, map_pow, hψε, hψπ, hψu, hπL]
      have hsplit : e i = e i₀ + (e i - e i₀) := (Nat.add_sub_cancel' (hmin i hi)).symm
      conv_lhs => rw [hsplit, pow_add]
      ring

    have hredg : red gW = (HahnSeries.C (IsLocalRing.residue A ε)) ^ n i₀ * red (uW i₀) := by
      rw [map_sum, Finset.sum_eq_single_of_mem i₀ hi₀I (fun i hi hne => by
        rw [map_mul, map_mul, map_pow, map_pow, hredπ, zero_pow (Nat.sub_ne_zero_of_lt (hlt i hi hne)),
          mul_zero, zero_mul])]
      rw [map_mul, map_mul, map_pow, map_pow, hredε, Nat.sub_self, pow_zero, mul_one]
    have hredg0 : red gW ≠ 0 := by
      rw [hredg]; exact mul_ne_zero (pow_ne_zero _ (HahnSeries.C_ne_zero hεbar)) (hredu_ne i₀ hpf0)
    have hgunit : IsUnit gW := hred_ne gW hredg0

    have hE3 : εW ^ B * πW ^ ((p - 1) * B) * fW = πW ^ e i₀ * gW := by
      rw [← hE2, hpW, mul_pow, ← pow_mul]
    rcases Nat.lt_trichotomy (e i₀) ((p - 1) * B) with hlt' | heq' | hgt'
    · exfalso
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt hlt'
      have hg : gW = εW ^ B * πW ^ (t + 1) * fW := by
        apply mul_left_cancel₀ (pow_ne_zero (e i₀) hπW0)
        rw [← hE3, ht, show e i₀ + t + 1 = e i₀ + (t + 1) by ring, pow_add]; ring
      apply (IsLocalRing.mem_maximalIdeal _).mp _ hgunit
      rw [hg]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hπmax _ (Nat.succ_pos t)))
    ·
      have hfg : εW ^ B * fW = gW := by
        apply mul_left_cancel₀ (pow_ne_zero ((p - 1) * B) hπW0)
        rw [← mul_assoc, mul_comm (πW ^ _) (εW ^ B), hE3, heq']
      have hval : red fW = ((HahnSeries.C (IsLocalRing.residue A ε)) ^ B)⁻¹ *
          ((HahnSeries.C (IsLocalRing.residue A ε)) ^ n i₀ * red (uW i₀)) := by
        rw [← hredg, ← hfg, map_mul, map_pow, hredε, ← mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero _ (HahnSeries.C_ne_zero hεbar)), one_mul]
      rw [hval]
      have hCmem : HahnSeries.C (IsLocalRing.residue A ε) ∈ ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * p) := by
        rw [← ResidME96.algebraMap_laurent_eq_C]; exact IntermediateField.algebraMap_mem _ _
      exact mul_mem (inv_mem (pow_mem hCmem _)) (mul_mem (pow_mem hCmem _) (hredu_mem i₀))
    ·
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_lt hgt'
      have hft : εW ^ B * fW = πW ^ (t + 1) * gW := by
        apply mul_left_cancel₀ (pow_ne_zero ((p - 1) * B) hπW0)
        rw [← mul_assoc, mul_comm (πW ^ _) (εW ^ B), hE3, ht,
          show (p - 1) * B + t + 1 = (p - 1) * B + (t + 1) by ring, pow_add, mul_assoc]
      have hmem : εW ^ B * fW ∈ IsLocalRing.maximalIdeal ↥W₀ := by
        rw [hft]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hπmax _ (Nat.succ_pos t))
      have hfmem : fW ∈ IsLocalRing.maximalIdeal ↥W₀ :=
        (Ideal.IsPrime.mem_or_mem inferInstance hmem).resolve_left
          (fun hh => (IsLocalRing.mem_maximalIdeal _).mp hh (hεunit.pow B))
      rw [hred0 fW hfmem]; exact zero_mem _

open ModularCurve in
theorem surj_Mp
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (z : LaurentSeries (IsLocalRing.ResidueField A))
    (hz : z ∈ ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * p)) :
    ∃ (f : ↥K) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
      HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (x.map (IsLocalRing.residue A)) /
        HahnSeries.ofPowerSeries ℤ (IsLocalRing.ResidueField A) (y.map (IsLocalRing.residue A)) = z := by
  haveI hMp0 : NeZero (M * p) := ⟨mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  classical
  subst hK

  set κ := IsLocalRing.ResidueField A with hκ
  let Pres : LaurentSeries κ → Prop := fun z =>
    ∃ (f : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) (x y : PowerSeries A),
      y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
      HahnSeries.ofPowerSeries ℤ κ (x.map (IsLocalRing.residue A)) /
        HahnSeries.ofPowerSeries ℤ κ (y.map (IsLocalRing.residue A)) = z
  change Pres z

  set redA : PowerSeries A →+* LaurentSeries κ :=
    (HahnSeries.ofPowerSeries ℤ κ).comp (PowerSeries.map (IsLocalRing.residue A)) with hredA
  set upA : PowerSeries A →+* LaurentSeries L :=
    (HahnSeries.ofPowerSeries ℤ L).comp (PowerSeries.map (algebraMap A L)) with hupA
  have hred : ∀ x : PowerSeries A, redA x = HahnSeries.ofPowerSeries ℤ κ (x.map (IsLocalRing.residue A)) :=
    fun _ => rfl
  have hup : ∀ x : PowerSeries A, upA x = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) :=
    fun _ => rfl
  have hup_ne : ∀ y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 → upA y ≠ 0 := by
    intro y hy h
    apply hy
    have h1 : y.map (algebraMap A L) = 0 := HahnSeries.ofPowerSeries_injective (by rw [← hup, h, map_zero])
    have h2 : y = 0 := by
      apply PowerSeries.map_injective (algebraMap A L) (IsFractionRing.injective A L)
      rw [h1, map_zero]
    rw [h2, map_zero]
  have hred_ne : ∀ y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 → redA y ≠ 0 := by
    intro y hy h
    exact hy (HahnSeries.ofPowerSeries_injective (by rw [← hred, h, map_zero]))

  have mkPres : ∀ (z : LaurentSeries κ) (f : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))))
      (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (f : LaurentSeries L) * upA y = upA x → redA x / redA y = z → Pres z :=
    fun z f x y hy h1 h2 => ⟨f, x, y, hy, h1, h2⟩

  have P_add : ∀ z₁ z₂, Pres z₁ → Pres z₂ → Pres (z₁ + z₂) := by
    rintro z₁ z₂ ⟨f₁, x₁, y₁, hy₁, h₁, hz₁⟩ ⟨f₂, x₂, y₂, hy₂, h₂, hz₂⟩
    rw [← hup, ← hup] at h₁ h₂
    rw [← hred, ← hred] at hz₁ hz₂
    refine mkPres _ (f₁ + f₂) (x₁ * y₂ + x₂ * y₁) (y₁ * y₂) ?_ ?_ ?_
    · rw [map_mul]; exact mul_ne_zero hy₁ hy₂
    · push_cast
      rw [map_mul, map_add, map_mul, map_mul]
      linear_combination (upA y₂) * h₁ + (upA y₁) * h₂
    · rw [map_mul, map_add, map_mul, map_mul, ← hz₁, ← hz₂, div_add_div _ _ (hred_ne y₁ hy₁) (hred_ne y₂ hy₂)]
      ring
  have P_mul : ∀ z₁ z₂, Pres z₁ → Pres z₂ → Pres (z₁ * z₂) := by
    rintro z₁ z₂ ⟨f₁, x₁, y₁, hy₁, h₁, hz₁⟩ ⟨f₂, x₂, y₂, hy₂, h₂, hz₂⟩
    rw [← hup, ← hup] at h₁ h₂
    rw [← hred, ← hred] at hz₁ hz₂
    refine mkPres _ (f₁ * f₂) (x₁ * x₂) (y₁ * y₂) ?_ ?_ ?_
    · rw [map_mul]; exact mul_ne_zero hy₁ hy₂
    · push_cast
      rw [map_mul, map_mul]
      linear_combination (f₂ : LaurentSeries L) * (upA y₂) * h₁ + (upA x₁) * h₂
    · rw [map_mul, map_mul, ← hz₁, ← hz₂, div_mul_div_comm]
  have P_neg : ∀ z, Pres z → Pres (-z) := by
    rintro z ⟨f, x, y, hy, h, hz⟩
    rw [← hup, ← hup] at h
    rw [← hred, ← hred] at hz
    refine mkPres _ (-f) (-x) y hy ?_ ?_
    · push_cast
      rw [map_neg, neg_mul, h]
    · rw [map_neg, neg_div, hz]
  have P_one : Pres 1 := by
    refine mkPres _ 1 1 1 (by rw [map_one]; exact one_ne_zero) ?_ ?_
    · push_cast; rw [map_one, one_mul]
    · rw [map_one, div_one]
  have P_zero : Pres 0 := by
    refine mkPres _ 0 0 1 (by rw [map_one]; exact one_ne_zero) ?_ ?_
    · push_cast; rw [map_one, map_zero, zero_mul]
    · rw [map_zero, zero_div]
  have P_inv : ∀ z, Pres z → Pres z⁻¹ := by
    rintro z ⟨f, x, y, hy, h, hz⟩
    rw [← hup, ← hup] at h
    rw [← hred, ← hred] at hz
    by_cases hx : x.map (IsLocalRing.residue A) = 0
    ·
      have : z = 0 := by
        rw [← hz, hred x, hx, map_zero, zero_div]
      rw [this, inv_zero]; exact P_zero
    · refine mkPres _ f⁻¹ y x hx ?_ ?_
      · have hX : upA x ≠ 0 := hup_ne x hx
        have hf : (f : LaurentSeries L) ≠ 0 := by
          intro h0; rw [h0, zero_mul] at h; exact hX h.symm
        push_cast
        rw [← h, mul_comm (f : LaurentSeries L), ← mul_assoc, mul_comm ((f : LaurentSeries L)⁻¹), mul_assoc,
          inv_mul_cancel₀ hf, mul_one]
      · rw [← hz, inv_div]

  have algebraMap_laurent : ∀ (F : Type) [Field F] (c : F), algebraMap F (LaurentSeries F) c = HahnSeries.C c := by
    intro F _ c
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    show HahnSeries.ofPowerSeries ℤ F (algebraMap F (PowerSeries F) c) = _
    rw [← PowerSeries.C_eq_algebraMap, HahnSeries.ofPowerSeries_C]
  have hcoe : ∀ l : L, ((algebraMap L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) l :
      ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L) =
      algebraMap L (LaurentSeries L) l := fun _ => rfl
  have P_const : ∀ c : κ, Pres (algebraMap κ (LaurentSeries κ) c) := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    refine mkPres _ (algebraMap A _ a) (PowerSeries.C a) 1 (by rw [map_one]; exact one_ne_zero) ?_ ?_
    · rw [map_one, mul_one, hup, PowerSeries.map_C, HahnSeries.ofPowerSeries_C,
        IsScalarTower.algebraMap_apply A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))),
        hcoe, algebraMap_laurent]
    · rw [map_one, div_one, hred, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, algebraMap_laurent]

  have P_gen : ∀ g ∈ ModularCurve.intFormRatiosC κ (CongruenceSubgroup.Gamma1 (M * p)), Pres g := by
    rintro g ⟨k, F, G, pf, pg, hF, hG, hg0, rfl⟩

    set x : PowerSeries A := pf.map (Int.castRingHom A) with hxdef
    set y : PowerSeries A := pg.map (Int.castRingHom A) with hydef
    have hxr : x.map (IsLocalRing.residue A) = pf.map (Int.castRingHom κ) := by
      ext n; simp [hxdef, PowerSeries.coeff_map]
    have hyr : y.map (IsLocalRing.residue A) = pg.map (Int.castRingHom κ) := by
      ext n; simp [hydef, PowerSeries.coeff_map]
    have hxu : x.map (algebraMap A L) = pf.map (Int.castRingHom L) := by
      ext n; simp [hxdef, PowerSeries.coeff_map]
    have hyu : y.map (algebraMap A L) = pg.map (Int.castRingHom L) := by
      ext n; simp [hydef, PowerSeries.coeff_map]
    have hredx : redA x = ModularCurve.intSeriesC κ pf := by rw [hred, hxr]; rfl
    have hredy : redA y = ModularCurve.intSeriesC κ pg := by rw [hred, hyr]; rfl
    have hy : y.map (IsLocalRing.residue A) ≠ 0 := by
      intro h; apply hg0; rw [← hredy, hred, h, map_zero]

    have hemb : ∀ q : PowerSeries ℤ, ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ q) =
        HahnSeries.ofPowerSeries ℤ L (q.map (Int.castRingHom L)) := by
      intro q
      ext n
      rw [ModularCurve.coeffEmb_coeff, ModularCurve.intSeriesC]
      rcases le_or_gt 0 n with hn | hn
      · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
        rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
          PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
      · rw [ofPowerSeries_coeff_of_neg _ hn, ofPowerSeries_coeff_of_neg _ hn, map_zero]
    have hgℚ : ModularCurve.intSeriesC ℚ pg ≠ 0 := by
      intro h
      apply hup_ne y hy
      rw [hup, hyu, ← hemb, h, map_zero]
    have hmemℚ : ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg ∈ ModularCurve.x1FunctionField (M * p) :=
      ModularCurve.div_mem_qExpFunctionFieldC F G hF hG hgℚ
    let f : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))) :=
      ⟨ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg),
        ModularCurve.coeffEmb_mem_laurentBaseChange L hmemℚ⟩
    refine mkPres _ f x y hy ?_ ?_
    · show ModularCurve.coeffEmb L (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg) * upA y = upA x
      rw [map_div₀, hemb, hemb, hup, hup, hxu, hyu]
      have hY : HahnSeries.ofPowerSeries ℤ L (pg.map (Int.castRingHom L)) ≠ 0 := by
        rw [← hyu, ← hup]; exact hup_ne y hy
      rw [div_mul_cancel₀ _ hY]
    · rw [hredx, hredy]

  have hz' : z ∈ Subfield.closure (Set.range (algebraMap κ (LaurentSeries κ)) ∪
      ModularCurve.intFormRatiosC κ (CongruenceSubgroup.Gamma1 (M * p))) := by
    rw [← IntermediateField.adjoin_toSubfield]; exact hz
  clear hz
  induction hz' using Subfield.closure_induction with
  | mem w hw =>
    rcases hw with ⟨c, rfl⟩ | hw
    · exact P_const c
    · exact P_gen w hw
  | one => exact P_one
  | add w₁ w₂ _ _ h₁ h₂ => exact P_add _ _ h₁ h₂
  | neg w _ h => exact P_neg _ h
  | inv w _ h => exact P_inv _ h
  | mul w₁ w₂ _ _ h₁ h₂ => exact P_mul _ _ h₁ h₂

namespace F0b
open ModularCurve

theorem adjoin_image_coeffMap_x1FunctionFieldC_eq
    (κ : Type*) [Field κ] (k : Type*) [Field k] [Algebra κ k] (N : ℕ) :
    IntermediateField.adjoin k
        (⇑(coeffMap (algebraMap κ k)) '' (x1FunctionFieldC κ N : Set (LaurentSeries κ))) = x1FunctionFieldC k N := by
  classical
  set g : κ →+* k := algebraMap κ k with hg
  set Φ : LaurentSeries κ →+* LaurentSeries k := coeffMap g with hΦ
  have hΦapp : ∀ x : LaurentSeries κ, Φ x = x.map g := fun x => rfl
  have hint : ∀ p : PowerSeries ℤ, Φ (intSeriesC κ p) = intSeriesC k p := by
    intro p
    ext n
    change g ((HahnSeries.ofPowerSeries ℤ κ (p.map (Int.castRingHom κ))).coeff n) =
      (HahnSeries.ofPowerSeries ℤ k (p.map (Int.castRingHom k))).coeff n
    rcases le_or_gt 0 n with hn | hn
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
        PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]
    · have hr : n ∉ Set.range (fun m : ℕ => (m : ℤ)) := by
        rintro ⟨m, hm⟩
        simp only at hm
        omega
      rw [HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_notin_range hr, HahnSeries.ofPowerSeries_apply,
        HahnSeries.embDomain_notin_range hr, map_zero]
  have hinj : Function.Injective Φ := Φ.injective
  have hrat : ⇑Φ '' intFormRatiosC κ (CongruenceSubgroup.Gamma1 N) = intFormRatiosC k (CongruenceSubgroup.Gamma1 N) := by
    ext x
    constructor
    · rintro ⟨y, ⟨wt, f, f', pf, pg, hf, hg', hg0, rfl⟩, rfl⟩
      refine ⟨wt, f, f', pf, pg, hf, hg', ?_, ?_⟩
      · rw [← hint]; exact fun h0 => hg0 (hinj (by rw [h0, map_zero]))
      · rw [map_div₀, hint, hint]
    · rintro ⟨wt, f, f', pf, pg, hf, hg', hg0, rfl⟩
      refine ⟨intSeriesC κ pf / intSeriesC κ pg, ⟨wt, f, f', pf, pg, hf, hg', ?_, rfl⟩, ?_⟩
      · intro h0; apply hg0; rw [← hint, h0, map_zero]
      · rw [map_div₀, hint, hint]
  have hC : ∀ c : κ, Φ (algebraMap κ (LaurentSeries κ) c) = algebraMap k (LaurentSeries k) (g c) := by
    intro c
    have h1 : algebraMap κ (LaurentSeries κ) c = HahnSeries.C c := by
      first
        | rfl
        | (rw [HahnSeries.algebraMap_apply']; simp)
        | (rw [HahnSeries.algebraMap_apply]; simp)
        | simp
    have h2 : algebraMap k (LaurentSeries k) (g c) = HahnSeries.C (g c) := by
      first
        | rfl
        | (rw [HahnSeries.algebraMap_apply']; simp)
        | (rw [HahnSeries.algebraMap_apply]; simp)
        | simp
    rw [h1, h2, hΦapp, HahnSeries.map_C]
  have hadj : ∀ T : Set (LaurentSeries κ),
      IntermediateField.adjoin k (⇑Φ '' (IntermediateField.adjoin κ T : Set (LaurentSeries κ))) =
        IntermediateField.adjoin k (⇑Φ '' T) := by
    intro T
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨z, hz, rfl⟩
      have hz' : z ∈ Subfield.closure (Set.range (algebraMap κ (LaurentSeries κ)) ∪ T) := hz
      have hΦz : Φ z ∈ (Subfield.closure (Set.range (algebraMap κ (LaurentSeries κ)) ∪ T)).map Φ := ⟨z, hz', rfl⟩
      rw [RingHom.map_field_closure] at hΦz
      refine (Subfield.closure_le (t := (IntermediateField.adjoin k (⇑Φ '' T)).toSubfield)).mpr ?_ hΦz
      rintro _ ⟨y, hy | hy, rfl⟩
      · obtain ⟨c, rfl⟩ := hy
        rw [hC]
        exact (IntermediateField.adjoin k (⇑Φ '' T)).algebraMap_mem (g c)
      · exact IntermediateField.subset_adjoin k _ ⟨y, hy, rfl⟩
    · exact IntermediateField.adjoin.mono _ _ _ (Set.image_mono (IntermediateField.subset_adjoin κ T))
  change IntermediateField.adjoin k (⇑Φ '' (IntermediateField.adjoin κ (intFormRatiosC κ (CongruenceSubgroup.Gamma1 N)) : Set _)) =
    IntermediateField.adjoin k (intFormRatiosC k (CongruenceSubgroup.Gamma1 N))
  rw [hadj, hrat]

end F0b

open scoped NumberField

noncomputable section

namespace GaussFrame

variable (p : ℕ) [hp : Fact p.Prime]

scoped instance neZero_of_fact_prime : NeZero p := ⟨hp.out.ne_zero⟩

private abbrev _root_.GaussFrame.L : Type := CyclotomicField p ℚ

p2m_export "GaussFrame" "L"
private scoped instance _root_.GaussFrame.instCyc : IsCyclotomicExtension {p} ℚ (L p) := CyclotomicField.isCyclotomicExtension p ℚ

p2m_export "GaussFrame" "instCyc"
scoped instance instCyc1 : IsCyclotomicExtension {p ^ (0 + 1)} ℚ (L p) := by
  rw [zero_add, pow_one]; infer_instance

scoped instance : NumberField (L p) := IsCyclotomicExtension.numberField {p} ℚ (L p)

private def _root_.GaussFrame.ζ : L p := IsCyclotomicExtension.zeta p ℚ (L p)

p2m_export "GaussFrame" "ζ"
private theorem _root_.GaussFrame.hζ : IsPrimitiveRoot (ζ p) p := IsCyclotomicExtension.zeta_spec p ℚ (L p)

p2m_export "GaussFrame" "hζ"
theorem hζ1 : IsPrimitiveRoot (ζ p) (p ^ (0 + 1)) := by rw [zero_add, pow_one]; exact hζ p

def 𝔓 : Ideal (𝓞 (L p)) := Ideal.span {(hζ1 p).toInteger - 1}

scoped instance 𝔓_isPrime : (𝔓 p).IsPrime := IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one p 0 (hζ1 p)

theorem 𝔓_ne_bot : 𝔓 p ≠ ⊥ := IsCyclotomicExtension.Rat.span_zeta_sub_one_ne_bot p 0 (hζ1 p)

scoped instance 𝔓_isMaximal : (𝔓 p).IsMaximal := (𝔓_isPrime p).isMaximal (𝔓_ne_bot p)

theorem absNorm_𝔓 : Ideal.absNorm (𝔓 p) = p := IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one p 0 (hζ1 p)

theorem p_mem_𝔓 : ((p : ℕ) : 𝓞 (L p)) ∈ 𝔓 p := IsCyclotomicExtension.Rat.p_mem_span_zeta_sub_one p 0 (hζ1 p)

private abbrev _root_.GaussFrame.A : Type := Localization.AtPrime (𝔓 p)

p2m_export "GaussFrame" "A"
scoped instance : IsDomain (A p) := inferInstance

scoped instance : IsDiscreteValuationRing (A p) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 (L p)) (𝔓_ne_bot p) (A p)

theorem isUnit_algebraMap_of_mem_primeCompl (y : (𝔓 p).primeCompl) : IsUnit (algebraMap (𝓞 (L p)) (L p) y) := by
  rw [isUnit_iff_ne_zero, map_ne_zero_iff _ (IsFractionRing.injective (𝓞 (L p)) (L p))]
  exact fun h => y.2 (h ▸ (𝔓 p).zero_mem)

scoped instance algAL : Algebra (A p) (L p) :=
  (IsLocalization.lift (M := (𝔓 p).primeCompl) (isUnit_algebraMap_of_mem_primeCompl p)).toAlgebra

theorem algebraMap_AL_eq : algebraMap (A p) (L p) =
    IsLocalization.lift (M := (𝔓 p).primeCompl) (isUnit_algebraMap_of_mem_primeCompl p) := rfl

scoped instance towerOAL : IsScalarTower (𝓞 (L p)) (A p) (L p) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [algebraMap_AL_eq, IsLocalization.lift_eq]

scoped instance fracAL : IsFractionRing (A p) (L p) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (𝔓 p).primeCompl (A p) (L p)

private theorem _root_.GaussFrame.hζA : ∃ z : A p, algebraMap (A p) (L p) z = ζ p :=
  ⟨algebraMap (𝓞 (L p)) (A p) (hζ1 p).toInteger, by
    rw [← IsScalarTower.algebraMap_apply]; rfl⟩

p2m_export "GaussFrame" "hζA"
private theorem _root_.GaussFrame.hAp : ((p : ℕ) : A p) ∈ IsLocalRing.maximalIdeal (A p) := by
  have : ((p : ℕ) : A p) = algebraMap (𝓞 (L p)) (A p) ((p : ℕ) : 𝓞 (L p)) := by simp
  rw [this, IsLocalization.AtPrime.to_map_mem_maximal_iff (A p) (𝔓 p)]
  exact p_mem_𝔓 p

p2m_export "GaussFrame" "hAp"

scoped instance : Finite (𝓞 (L p) ⧸ 𝔓 p) := Ideal.finiteQuotientOfFreeOfNeBot (𝔓 p) (𝔓_ne_bot p)

scoped instance : Fintype (𝓞 (L p) ⧸ 𝔓 p) := Fintype.ofFinite _

theorem card_quot : Fintype.card (𝓞 (L p) ⧸ 𝔓 p) = p := by
  rw [Fintype.card_eq_nat_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, absNorm_𝔓]

private def _root_.GaussFrame.σ₀ : IsLocalRing.ResidueField (A p) →+* ZMod p :=
  ((ZMod.ringEquivOfPrime (𝓞 (L p) ⧸ 𝔓 p) hp.out (card_quot p)).symm.toRingHom).comp
    (IsLocalization.AtPrime.equivQuotMaximalIdeal (𝔓 p) (A p)).symm.toRingHom

p2m_export "GaussFrame" "σ₀"

variable (N : ℕ) [NeZero N]

private abbrev _root_.GaussFrame.K : IntermediateField (L p) (LaurentSeries (L p)) := ModularCurve.laurentBaseChange (L p) (ModularCurve.x1FunctionField N)

p2m_export "GaussFrame" "K"
scoped instance algAK : Algebra (A p) ↥(K p N) := ((algebraMap (L p) ↥(K p N)).comp (algebraMap (A p) (L p))).toAlgebra

scoped instance towerAK : IsScalarTower (A p) (L p) ↥(K p N) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

private def _root_.GaussFrame.j : ↥(K p N) :=
  ⟨ModularCurve.coeffEmb (L p) ModularCurve.jq, ModularCurve.coeffEmb_jq_mem_laurentBaseChange_x1FunctionField (L p) N⟩

p2m_export "GaussFrame" "j"
omit hp in
private theorem _root_.GaussFrame.hj : ((j p N : ↥(K p N)) : LaurentSeries (L p)) = ModularCurve.coeffEmb (L p) ModularCurve.jq := rfl

p2m_export "GaussFrame" "hj"
scoped instance jFact : Fact (j p N ≠ 0) :=
  ⟨fun h => ModularCurve.coeffEmb_jq_ne_zero (L p) (by rw [← hj p N, h]; rfl)⟩

end GaussFrame
p2m_reactivate "P2MW.S_ModularCurve_x1FunctionFieldC_mul_eq_igusaFunctionFieldX1C.GaussFrame"

structure F0bFrame (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] : Type 1 where
  L : Type
  [instField : Field L]
  [instCharZero : CharZero L]
  [instCyc : IsCyclotomicExtension {p} ℚ L]
  ζ : L
  hζ : IsPrimitiveRoot ζ p
  A : Type
  [instCommRing : CommRing A]
  [instIsDomain : IsDomain A]
  [instDVR : IsDiscreteValuationRing A]
  [instAlgAL : Algebra A L]
  [instFrac : IsFractionRing A L]
  hAp : (p : A) ∈ IsLocalRing.maximalIdeal A
  hζA : ∃ z : A, algebraMap A L z = ζ
  K : IntermediateField L (LaurentSeries L)
  hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField N)
  [instAlgAK : Algebra A ↥K]
  [instTower : IsScalarTower A L ↥K]
  j : ↥K
  hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq
  [instFact : Fact (j ≠ 0)]
  σ₀ : IsLocalRing.ResidueField A →+* ZMod p

theorem F0bFrame.nonempty (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] : Nonempty (F0bFrame p N) :=
  ⟨{ L := GaussFrame.L p
     ζ := GaussFrame.ζ p
     hζ := GaussFrame.hζ p
     A := GaussFrame.A p
     hAp := GaussFrame.hAp p
     hζA := GaussFrame.hζA p
     K := GaussFrame.K p N
     hK := rfl
     j := GaussFrame.j p N
     hj := GaussFrame.hj p N
     σ₀ := GaussFrame.σ₀ p }⟩

end
p2m_reactivate "P2MW.S_ModularCurve_x1FunctionFieldC_mul_eq_igusaFunctionFieldX1C.GaussFrame"

namespace F0b
open ModularCurve

theorem x1FunctionFieldC_mul_eq_igusaFunctionFieldX1C_residueField
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (w : ModularCurve.IntegralWeightOneForm (IsLocalRing.ResidueField A) M) :
    ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) (M * p)
      = ModularCurve.igusaFunctionFieldX1C (IsLocalRing.ResidueField A) M w := by
  obtain ⟨h1, h2⟩ :=
    ModularCurve.XOneP.gaussReduction_mem_igusaFunctionFieldX1C_and_surjective_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj w
  apply le_antisymm
  · intro z hz
    obtain ⟨f, x, y, hy, hxy, rfl⟩ := surj_Mp p M hM hpM L ζ hζ K hK A hAp hζA j hj z hz
    exact h1 f x y hy hxy
  · intro z hz
    obtain ⟨f, x, y, hy, hxy, rfl⟩ := h2 z hz
    exact descent_Mp p M hM hpM L ζ hζ K hK A hAp hζA j hj f x y hy hxy

end F0b
p2m_reactivate "P2MW.S_ModularCurve_x1FunctionFieldC_mul_eq_igusaFunctionFieldX1C.GaussFrame"

open ModularCurve F0b in

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (κ : Type*) [Field κ] [CharP κ p] (w : ModularCurve.IntegralWeightOneForm κ M) :
    ModularCurve.x1FunctionFieldC κ (M * p) = ModularCurve.igusaFunctionFieldX1C κ M w := by
  classical
  haveI hp : Fact p.Prime := inferInstance
  haveI hMp0 : NeZero (M * p) := ⟨mul_ne_zero (NeZero.ne M) hp.out.ne_zero⟩
  obtain ⟨fr⟩ := F0bFrame.nonempty p (M * p)
  letI := fr.instField; letI := fr.instCharZero; letI := fr.instCyc; letI := fr.instCommRing; letI := fr.instIsDomain; letI := fr.instDVR
  letI := fr.instAlgAL; letI := fr.instFrac; letI := fr.instAlgAK; letI := fr.instTower; letI := fr.instFact

  obtain ⟨w₀⟩ := ModularCurve.nonempty_integralWeightOneForm (IsLocalRing.ResidueField fr.A) M (by omega)
  have E₀ := x1FunctionFieldC_mul_eq_igusaFunctionFieldX1C_residueField p M hM hpM fr.L fr.ζ fr.hζ fr.K fr.hK fr.A
    fr.hAp fr.hζA fr.j fr.hj w₀

  let σ : IsLocalRing.ResidueField fr.A →+* κ := (ZMod.castHom (dvd_refl p) κ).comp fr.σ₀
  letI : Algebra (IsLocalRing.ResidueField fr.A) κ := σ.toAlgebra
  calc ModularCurve.x1FunctionFieldC κ (M * p)
      = IntermediateField.adjoin κ (⇑(coeffMap (algebraMap (IsLocalRing.ResidueField fr.A) κ)) ''
          (x1FunctionFieldC (IsLocalRing.ResidueField fr.A) (M * p) : Set (LaurentSeries (IsLocalRing.ResidueField fr.A)))) :=
        (adjoin_image_coeffMap_x1FunctionFieldC_eq (IsLocalRing.ResidueField fr.A) κ (M * p)).symm
    _ = IntermediateField.adjoin κ (⇑(coeffMap (algebraMap (IsLocalRing.ResidueField fr.A) κ)) ''
          (igusaFunctionFieldX1C (IsLocalRing.ResidueField fr.A) M w₀ : Set (LaurentSeries (IsLocalRing.ResidueField fr.A)))) := by
        rw [E₀]
    _ = ModularCurve.igusaFunctionFieldX1C κ M w :=
        ModularCurve.adjoin_image_coeffMap_igusaFunctionFieldX1C_eq (IsLocalRing.ResidueField fr.A) κ M w₀ w

end S_ModularCurve_x1FunctionFieldC_mul_eq_igusaFunctionFieldX1C
end P2MW
export P2MW.S_ModularCurve_x1FunctionFieldC_mul_eq_igusaFunctionFieldX1C (solution)
