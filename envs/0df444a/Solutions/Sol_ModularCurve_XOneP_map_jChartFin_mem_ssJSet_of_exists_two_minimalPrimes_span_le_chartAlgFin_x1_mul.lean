-- Prove2me | solution 1 for ModularCurve.XOneP.map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b12b9258-560e-5b9a-8a75-b5cea5a93f96

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Theorems.Thm_Ideal_le_of_liesOver_of_forall_smul_eq_of_isInvariant
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_pair_x1_mul
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_ModularCurve_mem_ssJSet_map_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_XOneP_comap_eq_of_map_j_eq_of_map_jp_eq_valuationSubring_pair_x1_mul
import Theorems.Thm_ModularCurve_XZeroP_map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_gamma0_mul
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_mulSemiringAction_chartAlg_and_isInvariant_of_isInvariant
import Theorems.Thm_ModularCurve_XOneP_exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_x1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_x1_mul
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "instance" "ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice"
p2m_attr_erase "simp" "PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single"
p2m_attr_erase "simp" "ModularCurve.specializePlace_def AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_baseChangeRingHom ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.cuspCount_one WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

universe u v

open CategoryTheory AlgebraicGeometry
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped Pointwise

namespace SSCrossRingK11

theorem exists_algHom_chartAlgFin
    (R : Type u) [CommRing R] (F F' : Type u) [Field F] [Field F'] [Algebra R F] [Algebra R F']
    (φ : F →ₐ[R] F') (j : F) (j' : F') [Fact (j ≠ 0)] [Fact (j' ≠ 0)] (hj : φ j = j') :
    ∃ ι : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F' j'),
      (∀ x, ((ι x : ↥(chartAlgFin R F' j')) : F') = φ x) ∧ Function.Injective ι := by
  classical
  have hadj : ∀ x ∈ Algebra.adjoin R ({j} : Set F), φ x ∈ Algebra.adjoin R ({j'} : Set F') := by
    intro x hx
    have : (Algebra.adjoin R ({j} : Set F)).map φ ≤ Algebra.adjoin R ({j'} : Set F') := by
      rw [AlgHom.map_adjoin, Set.image_singleton, hj]
    exact this ⟨x, hx, rfl⟩
  let ψ : ↥(Algebra.adjoin R ({j} : Set F)) →+* ↥(Algebra.adjoin R ({j'} : Set F')) :=
    (φ.toRingHom.comp (Algebra.adjoin R ({j} : Set F)).val.toRingHom).codRestrict
      (Algebra.adjoin R ({j'} : Set F')).toSubring (fun x => hadj x x.2)
  have hint : ∀ x : F, IsIntegral ↥(Algebra.adjoin R ({j} : Set F)) x →
      IsIntegral ↥(Algebra.adjoin R ({j'} : Set F')) (φ x) := by
    intro x hx
    exact hx.map_of_comp_eq ψ φ.toRingHom (by ext y; rfl)
  let ι : ↥(chartAlgFin R F j) →ₐ[R] ↥(chartAlgFin R F' j') :=
    (φ.comp (chartAlgFin R F j).val).codRestrict (chartAlgFin R F' j')
      (fun x => (mem_chartAlg_iff R F').mpr (hint x x.2))
  refine ⟨ι, fun x => rfl, ?_⟩
  intro x y hxy
  apply Subtype.ext
  exact φ.toRingHom.injective (congrArg (fun z : ↥(chartAlgFin R F' j') => (z : F')) hxy :)

open _root_.Polynomial _root_.AlgebraicGeometry.Polynomial in

theorem finite_chartAlgFin_of_floor
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (L : Type) [Field L] [Algebra A L]
    [IsFractionRing A L] [CharZero L]
    (K K' : IntermediateField L (LaurentSeries L)) (hle : K' ≤ K)
    [Algebra A ↥K] [IsScalarTower A L ↥K] [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (j : ↥K) (j' : ↥K') [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    (hjj' : (IntermediateField.inclusion hle j' : ↥K) = j)
    (htj : Transcendental A j) (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K)
    [Algebra ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)]
    [IsScalarTower A ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)]
    (hι : ∀ x : ↥(chartAlgFin A (↥K') j'),
      ((algebraMap _ ↥(chartAlgFin A (↥K) j) x : ↥(chartAlgFin A (↥K) j)) : ↥K) =
        IntermediateField.inclusion hle (x : ↥K')) :
    Module.Finite ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) := by
  classical
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsSeparable.of_integral _ _
  obtain ⟨hfin, -⟩ := finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD inferInstance
  letI algP : Algebra A[X] ↥(chartAlgFin A (↥K) j) := (polynomialToChartFin A (↥K) j).toRingHom.toAlgebra
  letI algP' : Algebra A[X] ↥(chartAlgFin A (↥K') j') := (polynomialToChartFin A (↥K') j').toRingHom.toAlgebra
  haveI : Module.Finite A[X] ↥(chartAlgFin A (↥K) j) := hfin
  have key : polynomialToChartFin A (↥K) j =
      (IsScalarTower.toAlgHom A ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j)).comp
        (polynomialToChartFin A (↥K') j') := by
    apply Polynomial.algHom_ext
    simp only [polynomialToChartFin, AlgHom.comp_apply, Polynomial.aeval_X, IsScalarTower.coe_toAlgHom']
    apply Subtype.ext
    rw [hι, coe_jChartFin, coe_jChartFin, hjj']
  haveI : IsScalarTower A[X] ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) :=
    IsScalarTower.of_algebraMap_eq fun P => by
      change polynomialToChartFin A (↥K) j P = algebraMap _ _ (polynomialToChartFin A (↥K') j' P)
      rw [key]
      rfl
  exact Module.Finite.of_restrictScalars_finite A[X] _ _

section SSTransfer
open ModularCurve

private theorem cast_point_nsmul {k₀ : Type*} [Field k₀] [DecidableEq k₀] {W₁ W₂ : WeierstrassCurve k₀} (e : W₁ = W₂)
    (P : W₁.toAffine.Point) (n : ℕ) : e ▸ (n • P) = n • (e ▸ P) := by subst e; rfl

private theorem cast_point_eq_zero_iff {k₀ : Type*} [Field k₀] [DecidableEq k₀] {W₁ W₂ : WeierstrassCurve k₀} (e : W₁ = W₂)
    (P : W₁.toAffine.Point) : e ▸ P = (0 : W₂.toAffine.Point) ↔ P = 0 := by subst e; exact Iff.rfl

private theorem cast_point_zero {k₀ : Type*} [Field k₀] [DecidableEq k₀] {W₁ W₂ : WeierstrassCurve k₀} (e : W₁ = W₂) :
    e ▸ (0 : W₁.toAffine.Point) = (0 : W₂.toAffine.Point) := by subst e; rfl

theorem mem_ssJSet_of_map_mem {q : ℕ} {k₀ k : Type*} [Field k₀] [Field k] [DecidableEq k₀] [DecidableEq k]
    (θ : k₀ →+* k) (a : k₀) (h : θ a ∈ ssJSet q k) : a ∈ ssJSet q k₀ := by
  rw [mem_ssJSet_iff] at h ⊢
  intro W _ hW P hP
  letI : Algebra k₀ k := θ.toAlgebra
  have e : W = W.baseChange k₀ := by
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  let P' : (W.baseChange k₀).toAffine.Point := e ▸ P
  have hP' : q • P' = 0 := by
    change q • (e ▸ P) = 0
    rw [← cast_point_nsmul e P q, hP]; exact cast_point_zero e
  let f : k₀ →ₐ[k₀] k := Algebra.ofId k₀ k
  haveI : (W.baseChange k).IsElliptic := by dsimp only [WeierstrassCurve.baseChange]; infer_instance
  let Pk : (W.baseChange k).toAffine.Point := WeierstrassCurve.Affine.Point.map f P'
  have hPk : q • Pk = 0 := by
    change q • (WeierstrassCurve.Affine.Point.map f P') = 0
    rw [← map_nsmul, hP', map_zero]
  have hj : (W.baseChange k).j = θ a := by
    simp only [WeierstrassCurve.baseChange]
    rw [WeierstrassCurve.map_j, hW]; rfl
  have hzero : Pk = 0 := h (W.baseChange k) hj Pk hPk
  have hP'0 : P' = 0 := WeierstrassCurve.Affine.Point.map_injective f (by rw [map_zero]; exact hzero)
  exact (cast_point_eq_zero_iff e P).mp hP'0

theorem mem_ssJSet_of_ringHom_of_mem_ssJSet {q : ℕ} [Fact q.Prime]
    {κ Ω₀ Ω : Type*} [CommRing κ] [IsDomain κ] [Field Ω₀] [Field Ω] [CharP Ω₀ q] [CharP Ω q]
    [IsAlgClosed Ω₀] [IsAlgClosed Ω] [DecidableEq Ω₀] [DecidableEq Ω]
    (ψ : κ →+* Ω₀) (χ : κ →+* Ω) (hψ : Function.Injective ψ) (hχ : Function.Injective χ)
    (a : κ) (h : ψ a ∈ ssJSet q Ω₀) : χ a ∈ ssJSet q Ω := by
  classical
  haveI : CharP κ q := ψ.charP hψ q
  let F := FractionRing κ
  let k₁ := AlgebraicClosure F
  let ψF : F →+* Ω₀ := IsFractionRing.lift hψ
  let χF : F →+* Ω := IsFractionRing.lift hχ
  letI algψ : Algebra F Ω₀ := ψF.toAlgebra
  letI algχ : Algebra F Ω := χF.toAlgebra
  let e₀ : k₁ →ₐ[F] Ω₀ := IsAlgClosed.lift
  let e : k₁ →ₐ[F] Ω := IsAlgClosed.lift
  let a₁ : k₁ := algebraMap F k₁ (algebraMap κ F a)
  have h₀ : e₀ a₁ = ψ a := by
    change e₀ (algebraMap F k₁ (algebraMap κ F a)) = ψ a
    rw [e₀.commutes]
    exact IsFractionRing.lift_algebraMap hψ a
  have h₁ : e a₁ = χ a := by
    change e (algebraMap F k₁ (algebraMap κ F a)) = χ a
    rw [e.commutes]
    exact IsFractionRing.lift_algebraMap hχ a
  have hk₁ : a₁ ∈ ssJSet q k₁ := mem_ssJSet_of_map_mem e₀.toRingHom a₁ (by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h₀]; exact h)
  have := ModularCurve.mem_ssJSet_map_of_isAlgClosed e.toRingHom a₁ hk₁
  rwa [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h₁] at this

end SSTransfer

theorem mem_nonunits_iff_mem_and {K : Type*} [Field K] (W : ValuationSubring K) (x : K) :
    x ∈ W.nonunits ↔ x ∈ W ∧ (x = 0 ∨ x⁻¹ ∉ W) := by
  rw [ValuationSubring.mem_nonunits_iff]
  constructor
  · intro hx
    refine ⟨(W.valuation_le_one_iff x).mp hx.le, ?_⟩
    by_cases h0 : x = 0
    · exact Or.inl h0
    · right
      rw [← W.valuation_le_one_iff, map_inv₀, not_le]
      exact one_lt_inv_iff₀.mpr ⟨(map_ne_zero _).mpr h0 |>.bot_lt, hx⟩
  · rintro ⟨hxW, h0 | hinv⟩
    · rw [h0, map_zero]; exact zero_lt_one
    · rw [← W.valuation_le_one_iff, map_inv₀, not_le] at hinv
      have hx0 : W.valuation x ≠ 0 := by
        intro h; rw [h, inv_zero] at hinv; exact not_lt_of_ge zero_le_one hinv
      exact (one_lt_inv_iff₀.mp hinv).2

theorem map_mem_nonunits_iff {K K' : Type*} [Field K] [Field K'] (W : ValuationSubring K') (f : K →+* K') (x : K) :
    f x ∈ W.nonunits ↔ x ∈ (W.comap f).nonunits := by
  rw [mem_nonunits_iff_mem_and, mem_nonunits_iff_mem_and, ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero_iff f f.injective]

theorem under_mem_minimalPrimes_of_mem_minimalPrimes
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.HasGoingDown R S]
    (r : R) (𝔭 : Ideal S) (h𝔭 : 𝔭 ∈ (Ideal.span {algebraMap R S r}).minimalPrimes) :
    𝔭.under R ∈ (Ideal.span {r}).minimalPrimes := by
  haveI h𝔭prime : 𝔭.IsPrime := h𝔭.1.1
  have hr𝔭 : algebraMap R S r ∈ 𝔭 := h𝔭.1.2 (Ideal.subset_span rfl)
  have hle : Ideal.span {r} ≤ 𝔭.under R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hr𝔭
  obtain ⟨𝔮₀, h𝔮₀, h𝔮₀le⟩ := Ideal.exists_minimalPrimes_le hle
  haveI : 𝔮₀.IsPrime := h𝔮₀.1.1
  haveI : 𝔭.LiesOver (𝔭.under R) := ⟨rfl⟩
  obtain ⟨𝔭₀, h𝔭₀le, h𝔭₀prime, h𝔭₀over⟩ := Ideal.exists_ideal_le_liesOver_of_le 𝔭 h𝔮₀le
  haveI := h𝔭₀prime
  have hr𝔭₀ : Ideal.span {algebraMap R S r} ≤ 𝔭₀ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have : r ∈ 𝔭₀.under R := by rw [← h𝔭₀over.over]; exact h𝔮₀.1.2 (Ideal.subset_span rfl)
    exact this
  have heq : 𝔭₀ = 𝔭 := le_antisymm h𝔭₀le (h𝔭.2 ⟨h𝔭₀prime, hr𝔭₀⟩ h𝔭₀le)
  have : 𝔭.under R = 𝔮₀ := by rw [← heq]; exact h𝔭₀over.over.symm
  rw [this]; exact h𝔮₀

theorem le_of_mem_minimalPrimes_of_bottom
    {R A₂ B : Type*} [CommRing R] [CommRing A₂] [CommRing B] [Algebra R A₂] [Algebra R B] [Algebra A₂ B] [IsScalarTower R A₂ B]
    [Algebra.HasGoingDown A₂ B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A₂ B] [Algebra.IsInvariant A₂ B G]
    (ϖ : R) (y : Ideal B) [y.IsPrime]
    (hstab : ∀ 𝔭 ∈ (Ideal.span {algebraMap R B ϖ}).minimalPrimes, ∀ g : G, g • 𝔭 = 𝔭)
    (hbottom : ∀ 𝔮 ∈ (Ideal.span {algebraMap R A₂ ϖ}).minimalPrimes, 𝔮 ≤ y.under A₂) :
    ∀ 𝔭 ∈ (Ideal.span {algebraMap R B ϖ}).minimalPrimes, 𝔭 ≤ y := by
  intro 𝔭 h𝔭
  haveI : 𝔭.IsPrime := h𝔭.1.1
  have h𝔭' : 𝔭 ∈ (Ideal.span {algebraMap A₂ B (algebraMap R A₂ ϖ)}).minimalPrimes := by
    rwa [← IsScalarTower.algebraMap_apply]
  have hunder := under_mem_minimalPrimes_of_mem_minimalPrimes (algebraMap R A₂ ϖ) 𝔭 h𝔭'
  haveI : (y.under A₂).IsPrime := Ideal.IsPrime.under A₂ y
  exact (Ideal.le_of_liesOver_of_forall_smul_eq_of_isInvariant G 𝔭 𝔭 (hstab 𝔭 h𝔭) (hstab 𝔭 h𝔭)
    (y.under A₂) (hbottom _ hunder) (hbottom _ hunder) y rfl).1

theorem hasGoingDown_floor
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (L : Type) [Field L] [Algebra A L]
    [IsFractionRing A L] [CharZero L]
    (K K' : IntermediateField L (LaurentSeries L)) (hle : K' ≤ K)
    [Algebra A ↥K] [IsScalarTower A L ↥K] [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (j : ↥K) (j' : ↥K') [Fact (j ≠ 0)] [Fact (j' ≠ 0)]
    (hjj' : (IntermediateField.inclusion hle j' : ↥K) = j)
    (htj : Transcendental A j) (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K)
    (ι : ↥(chartAlgFin A (↥K') j') →ₐ[A] ↥(chartAlgFin A (↥K) j))
    (hι : ∀ x, ((ι x : ↥(chartAlgFin A (↥K) j)) : ↥K) = IntermediateField.inclusion hle (x : ↥K'))
    (hιinj : Function.Injective ι) :
    letI := ι.toRingHom.toAlgebra
    Algebra.HasGoingDown ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) := by
  letI := ι.toRingHom.toAlgebra
  haveI : IsScalarTower A ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) :=
    IsScalarTower.of_algebraMap_eq (fun a => (ι.commutes a).symm)
  haveI : Module.Finite ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) :=
    finite_chartAlgFin_of_floor A L K K' hle j j' hjj' htj hFD hι
  haveI : Algebra.IsIntegral ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) := inferInstance
  haveI : IsIntegrallyClosed ↥(chartAlgFin A (↥K') j') :=
    AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_chartAlg A (↥K') _
  haveI : FaithfulSMul ↥(chartAlgFin A (↥K') j') ↥(chartAlgFin A (↥K) j) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hιinj
  infer_instance

theorem smul_eq_of_mem_minimalPrimes_of_comap_eq
    {A L : Type} [CommRing A] [Field L] [Algebra A L] {K : IntermediateField L (LaurentSeries L)}
    [Algebra A ↥K] (j : ↥K) [Fact (j ≠ 0)] (ϖ : A)
    (G : Type) [Group G] [MulSemiringAction G ↥K] [SMulCommClass G L ↥K]
    [MulSemiringAction G ↥(chartAlgFin A (↥K) j)]
    (hcoe : ∀ (g : G) (x : ↥(chartAlgFin A (↥K) j)), ((g • x : ↥(chartAlgFin A (↥K) j)) : ↥K) = g • (x : ↥K))
    (W₀ W₁ : ValuationSubring ↥K)
    (hi : ∀ 𝔭 ∈ (Ideal.span {algebraMap A ↥(chartAlgFin A (↥K) j) ϖ}).minimalPrimes,
      (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ 𝔭 ↔ (b : ↥K) ∈ W₀.nonunits) ∨
      (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ 𝔭 ↔ (b : ↥K) ∈ W₁.nonunits))
    (jp : ↥K) (hfix : ∀ g : G, g • j = j ∧ g • jp = jp)
    (hbs : ∀ e : ↥K ≃ₐ[L] ↥K, e j = j → e jp = jp →
      W₀.comap (e : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom = W₀ ∧ W₁.comap (e : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom = W₁) :
    ∀ 𝔭 ∈ (Ideal.span {algebraMap A ↥(chartAlgFin A (↥K) j) ϖ}).minimalPrimes, ∀ g : G, g • 𝔭 = 𝔭 := by
  intro 𝔭 h𝔭 g
  have hfixW := hbs (MulSemiringAction.toAlgEquiv L (↥K) g⁻¹) (hfix g⁻¹).1 (hfix g⁻¹).2
  have key : ∀ W : ValuationSubring ↥K,
      W.comap (MulSemiringAction.toAlgEquiv L (↥K) g⁻¹ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom = W →
      (∀ b : ↥(chartAlgFin A (↥K) j), b ∈ 𝔭 ↔ (b : ↥K) ∈ W.nonunits) → g • 𝔭 = 𝔭 := by
    intro W hW hmem
    ext b
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, hmem, hmem, hcoe,
      show g⁻¹ • (b : ↥K) = (MulSemiringAction.toAlgEquiv L (↥K) g⁻¹ : ↥K ≃ₐ[L] ↥K).toAlgHom.toRingHom (b : ↥K) from rfl,
      map_mem_nonunits_iff, hW]
  rcases hi 𝔭 h𝔭 with h𝔭W | h𝔭W
  · exact key W₀ hfixW.1 h𝔭W
  · exact key W₁ hfixW.2 h𝔭W

theorem sstoken_under {p : ℕ} [Fact p.Prime] {A₂ B : Type} [CommRing A₂] [CommRing B] [Algebra A₂ B]
    (j₂ : A₂) (j : B) (hj : algebraMap A₂ B j₂ = j)
    (y : Ideal B) [y.IsPrime] (hpy : ((p : ℕ) : B) ∈ y)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω] (φ : B →+* Ω),
      RingHom.ker φ = y → φ j ∈ ModularCurve.ssJSet p Ω) :
    ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω] (φ₂ : A₂ →+* Ω),
      RingHom.ker φ₂ = y.under A₂ → φ₂ j₂ ∈ ModularCurve.ssJSet p Ω := by
  classical
  intro Ω _ _ _ _ φ₂ hφ₂

  haveI : IsDomain (B ⧸ y) := Ideal.Quotient.isDomain y
  let Ω₀ : Type := AlgebraicClosure (FractionRing (B ⧸ y))
  let ψ₀ : B →+* Ω₀ :=
    (algebraMap (FractionRing (B ⧸ y)) Ω₀).comp ((algebraMap (B ⧸ y) (FractionRing (B ⧸ y))).comp (Ideal.Quotient.mk y))
  have hψ₀inj : Function.Injective ((algebraMap (FractionRing (B ⧸ y)) Ω₀).comp (algebraMap (B ⧸ y) (FractionRing (B ⧸ y)))) :=
    (algebraMap (FractionRing (B ⧸ y)) Ω₀).injective.comp (IsFractionRing.injective _ _)
  have hker₀ : RingHom.ker ψ₀ = y := by
    ext b
    rw [RingHom.mem_ker]
    change ((algebraMap (FractionRing (B ⧸ y)) Ω₀).comp (algebraMap (B ⧸ y) (FractionRing (B ⧸ y)))) (Ideal.Quotient.mk y b) = 0 ↔ _
    rw [map_eq_zero_iff _ hψ₀inj, Ideal.Quotient.eq_zero_iff_mem]
  haveI : CharP Ω₀ p := by
    have h0 : ((p : ℕ) : Ω₀) = 0 := by
      rw [← map_natCast ψ₀, ← RingHom.mem_ker, hker₀]; exact hpy
    exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h0
  have h₀ : ψ₀ j ∈ ModularCurve.ssJSet p Ω₀ := hss Ω₀ ψ₀ hker₀
  haveI : IsDomain (A₂ ⧸ y.under A₂) := Ideal.Quotient.isDomain _
  have hkerψ : RingHom.ker (ψ₀.comp (algebraMap A₂ B)) = y.under A₂ := by
    rw [← RingHom.comap_ker, hker₀]
  let ψ : (A₂ ⧸ y.under A₂) →+* Ω₀ :=
    Ideal.Quotient.lift _ (ψ₀.comp (algebraMap A₂ B)) (fun a ha => by rwa [← hkerψ] at ha)
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.lift_mk] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hkerψ ▸ (RingHom.mem_ker).mpr ha)
  let χ : (A₂ ⧸ y.under A₂) →+* Ω := Ideal.Quotient.lift _ φ₂ (fun a ha => by rwa [← hφ₂] at ha)
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.Quotient.lift_mk] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hφ₂ ▸ (RingHom.mem_ker).mpr ha)
  have key := mem_ssJSet_of_ringHom_of_mem_ssJSet ψ χ hψinj hχinj (Ideal.Quotient.mk _ j₂) (by
    change (ψ₀.comp (algebraMap A₂ B)) j₂ ∈ _
    rw [RingHom.comp_apply, hj]; exact h₀)
  first | simpa using key | exact key

end SSCrossRingK11

set_option maxHeartbeats 12800000 in
open SSCrossRingK11 in

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
    (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) [y.IsPrime]
    (hyϖ : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ y)
    (htwo : ∃ 𝔭 ∈ (Ideal.span {algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ}).minimalPrimes,
        ∃ 𝔭' ∈ (Ideal.span {algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ}).minimalPrimes, 𝔭 ≠ 𝔭' ∧ 𝔭 ≤ y ∧ 𝔭' ≤ y)
    (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
    (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω) (hφ : RingHom.ker φ = y) :
    φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet p Ω := by
  classical
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  let Afin := ↥(chartAlgFin A (↥K) j)

  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  haveI hFD := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma1 (M * p)) hT L K hK j hj
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsSeparable.of_integral _ _

  have h10 : CongruenceSubgroup.Gamma1 (M * p) ≤ CongruenceSubgroup.Gamma0 (M * p) := by
    intro g hg
    rw [CongruenceSubgroup.Gamma1_mem] at hg
    rw [CongruenceSubgroup.Gamma0_mem]
    exact hg.2.2
  let K₂ : IntermediateField L (LaurentSeries L) :=
    ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p)))
  have hK₂ : K₂ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (M * p))) := rfl
  have hle : K₂ ≤ K := by
    rw [hK]
    exact IntermediateField.adjoin.mono L _ _ (Set.image_mono (ModularCurve.qExpFunctionFieldC_mono ℚ h10))
  letI : Algebra A ↥K₂ := ((algebraMap L ↥K₂).comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L ↥K₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hjqmem : ModularCurve.coeffEmb L ModularCurve.jq ∈ K₂ :=
    ModularCurve.coeffEmb_mem_laurentBaseChange L
      (ModularCurve.intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma0 (M * p))))
  let j₂ : ↥K₂ := ⟨ModularCurve.coeffEmb L ModularCurve.jq, hjqmem⟩
  have hj₂ : ((j₂ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq := rfl
  have hjj₂ : (IntermediateField.inclusion hle j₂ : ↥K) = j := Subtype.ext (by rw [hj]; rfl)
  haveI : Fact (j₂ ≠ 0) := ⟨fun h0 => (Fact.out : j ≠ 0) (by rw [← hjj₂, h0, map_zero])⟩

  have hjpmem₂ : ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq) ∈ K₂ := by
    apply ModularCurve.coeffEmb_mem_laurentBaseChange L
    have h := ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ (M * p)
      (ModularCurve.jqModCd_mem_full ℚ (M * p) (dvd_mul_left p M))
    exact h
  let jp : ↥K := ⟨ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq), hle hjpmem₂⟩
  have hjp : ((jp : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq) := rfl

  obtain ⟨ιF, hιF, hιFinj⟩ := SSCrossRingK11.exists_algHom_chartAlgFin A (↥K₂) (↥K)
    ((IntermediateField.inclusion hle).restrictScalars A) j₂ j hjj₂
  letI algι : Algebra ↥(chartAlgFin A (↥K₂) j₂) Afin := ιF.toRingHom.toAlgebra
  haveI : IsScalarTower A ↥(chartAlgFin A (↥K₂) j₂) Afin :=
    IsScalarTower.of_algebraMap_eq (fun a => (ιF.commutes a).symm)
  have hιFj : algebraMap ↥(chartAlgFin A (↥K₂) j₂) Afin (jChartFin A (↥K₂) j₂) = jChartFin A (↥K) j := by
    apply Subtype.ext
    change ((ιF (jChartFin A (↥K₂) j₂) : Afin) : ↥K) = _
    rw [hιF, coe_jChartFin]
    exact hjj₂

  obtain ⟨G, _instG, _instF, _instAct, ⟨hsmc₂, hinvK⟩, hsmcL, hfix⟩ :=
    ModularCurve.XOneP.exists_mulSemiringAction_isInvariant_laurentBaseChange_gamma0_smul_j_eq_x1_mul
      p M hM hpM L K hK j hj jp hjp K₂ hK₂ hle
  letI algK : Algebra ↥K₂ ↥K := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI istAK₂K : IsScalarTower A ↥K₂ ↥K := IsScalarTower.of_algebraMap_eq (fun a => by
    change algebraMap A ↥K a = IntermediateField.inclusion hle (algebraMap L ↥K₂ (algebraMap A L a))
    rw [IsScalarTower.algebraMap_apply A L ↥K a]
    rfl)
  haveI := hsmc₂
  haveI := hinvK
  have hS : algebraMap ↥K₂ ↥K '' ({j₂} : Set ↥K₂) = ({j} : Set ↥K) := by
    rw [Set.image_singleton]; congr 1
  obtain ⟨act, hcoe, hsmcA, ⟨hsmcA₂, hinvA⟩, -⟩ :=
    @AlgebraicCurve.TwoChartIntegralModel.exists_mulSemiringAction_chartAlg_and_isInvariant_of_isInvariant
      A _ (↥K₂) _ _ (↥K) _ _ algK istAK₂K G _instG _instAct hsmc₂ hinvK ({j₂} : Set ↥K₂) ({j} : Set ↥K) hS ιF hιF
  letI := act
  haveI := hsmcA₂
  haveI := hinvA

  obtain ⟨w⟩ := ModularCurve.nonempty_integralWeightOneForm (IsLocalRing.ResidueField A) M (by omega)
  obtain ⟨W₀, W₁, h1, h2, h3, h4, h5, -⟩ :=
    ModularCurve.XOneP.exists_valuationSubring_pair_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj w
  obtain ⟨hi, -, -, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_span_iff_of_valuationSubring_pair
      A L (↥K) j htj hFD hsep ϖ hϖ W₀ W₁ h1 h2 h3 h5
  have hstab := @SSCrossRingK11.smul_eq_of_mem_minimalPrimes_of_comap_eq A L _ _ _ K _ j _ ϖ G _instG _instAct hsmcL act
    hcoe W₀ W₁ hi jp hfix (fun e he₁ he₂ =>
    ModularCurve.XOneP.comap_eq_of_map_j_eq_of_map_jp_eq_valuationSubring_pair_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj jp hjp W₀ W₁ h1 h2 h3 h4 h5 e he₁ he₂)

  haveI := SSCrossRingK11.hasGoingDown_floor A L K K₂ hle j j₂ hjj₂ htj hFD ιF hιF hιFinj

  obtain ⟨𝔭, h𝔭, 𝔭', h𝔭', hne, h𝔭y, h𝔭'y⟩ := htwo
  haveI : 𝔭.IsPrime := h𝔭.1.1
  haveI : 𝔭'.IsPrime := h𝔭'.1.1
  have h𝔭A : 𝔭 ∈ (Ideal.span {algebraMap ↥(chartAlgFin A (↥K₂) j₂) Afin (algebraMap A _ ϖ)}).minimalPrimes := by
    rwa [← IsScalarTower.algebraMap_apply]
  have h𝔭'A : 𝔭' ∈ (Ideal.span {algebraMap ↥(chartAlgFin A (↥K₂) j₂) Afin (algebraMap A _ ϖ)}).minimalPrimes := by
    rwa [← IsScalarTower.algebraMap_apply]
  have hq := SSCrossRingK11.under_mem_minimalPrimes_of_mem_minimalPrimes (algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ) 𝔭 h𝔭A
  have hq' := SSCrossRingK11.under_mem_minimalPrimes_of_mem_minimalPrimes (algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ) 𝔭' h𝔭'A
  have hqne : 𝔭.under ↥(chartAlgFin A (↥K₂) j₂) ≠ 𝔭'.under ↥(chartAlgFin A (↥K₂) j₂) := by
    intro heq
    obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq ↥(chartAlgFin A (↥K₂) j₂) Afin G 𝔭 𝔭' heq
    exact hne (by rw [hg, hstab 𝔭 h𝔭 g])
  have hyϖ₂ : algebraMap A ↥(chartAlgFin A (↥K₂) j₂) ϖ ∈ y.under ↥(chartAlgFin A (↥K₂) j₂) := by
    change algebraMap ↥(chartAlgFin A (↥K₂) j₂) Afin (algebraMap A _ ϖ) ∈ y
    rw [← IsScalarTower.algebraMap_apply]; exact hyϖ
  haveI hy₂ : (y.under ↥(chartAlgFin A (↥K₂) j₂)).IsPrime := Ideal.IsPrime.under _ y
  have hφ₂ : RingHom.ker (φ.comp ιF.toRingHom) = y.under ↥(chartAlgFin A (↥K₂) j₂) := by
    rw [← RingHom.comap_ker, hφ]; rfl
  have hbottom := ModularCurve.XZeroP.map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_gamma0_mul
    p M hM hpM L ζ hζ K₂ hK₂ A hAp hζA j₂ hj₂ ϖ hϖ (y.under ↥(chartAlgFin A (↥K₂) j₂)) hyϖ₂
    ⟨_, hq, _, hq', hqne, Ideal.comap_mono h𝔭y, Ideal.comap_mono h𝔭'y⟩ Ω (φ.comp ιF.toRingHom) hφ₂
  rw [RingHom.comp_apply] at hbottom
  have hιFj' : ιF.toRingHom (jChartFin A (↥K₂) j₂) = jChartFin A (↥K) j := hιFj
  rwa [hιFj'] at hbottom

end S_ModularCurve_XOneP_map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_map_jChartFin_mem_ssJSet_of_exists_two_minimalPrimes_span_le_chartAlgFin_x1_mul (solution)
