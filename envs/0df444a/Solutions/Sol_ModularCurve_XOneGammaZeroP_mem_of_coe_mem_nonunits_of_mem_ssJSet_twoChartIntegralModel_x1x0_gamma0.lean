-- Prove2me | solution 1 for ModularCurve.XOneGammaZeroP.mem_of_coe_mem_nonunits_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/2795f164-0e98-5ca7-b139-e6a0579e9742

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Theorems.Thm_ModularCurve_XOneP_le_of_mem_minimalPrimes_span_of_mem_ssJSet_chartAlgFin_x1_mul
import Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_pair_x1_mul
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_mem_minimalPrimes_span_iff_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_stalk_iso_localization_chartAlgFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneGammaZeroP_mem_of_coe_mem_nonunits_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "instance" "ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg"
p2m_attr_erase "simp" "WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one"
p2m_attr_erase "simp" "ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun"
p2m_attr_erase "simp" "KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single"
p2m_attr_erase "simp" "ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply"
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_baseChangeRingHom ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.cuspCount_one WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

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

end SSCrossRingK11

namespace SSOnSheetK11

theorem germ_toBase_mem_maximalIdeal_iff
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (y : ↥(XFin R F j)) (r : R) :
    (((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.germ ⊤ ((ιFin R F j).base y) trivial).hom
        (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))
      ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)) ↔
    algebraMap R ↥(chartAlgFin R F j) r ∈ y.asIdeal := by
  obtain ⟨e, he, -⟩ := exists_stalk_iso_localization_chartAlgFin R F j y ⟨y, trivial, rfl⟩
  let E := e.commRingCatIsoToRingEquiv
  have hE : ∀ x, E x = e.hom.hom x := fun _ => rfl
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff E, hE, he,
    IsScalarTower.algebraMap_apply R ↥(chartAlgFin R F j) (Localization.AtPrime y.asIdeal),
    ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime y.asIdeal) y.asIdeal _

end SSOnSheetK11

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K₁ : IntermediateField L (LaurentSeries L))
    (hK₁ : K₁ = ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M p))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K₁] [IsScalarTower A L ↥K₁]
    (j : ↥K₁) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K₁)
    (hW₀ : ∀ f : ↥K₁, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.stalk z)
    (hϖz : ϖz = (((AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.germ ⊤ z trivial).hom (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₁) j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ))))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K₁) j).presheaf.stalk z))
    (y : ↥(XFin A (↥K₁) j)) (hy : (ιFin A (↥K₁) j).base y = z)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K₁) j) →+* Ω),
      RingHom.ker φ = y.asIdeal → φ (jChartFin A (↥K₁) j) ∈ ModularCurve.ssJSet p Ω)

    (𝔶 : Ideal ↥(chartAlgFin A (↥K₁) j)) (h𝔶 : 𝔶 = y.asIdeal) :
    ∀ s : ↥(chartAlgFin A (↥K₁) j), (s : ↥K₁) ∈ W₀.nonunits → s ∈ 𝔶 := by
  classical
  intro s hs
  subst h𝔶
  subst hy

  have hyϖ : algebraMap A ↥(chartAlgFin A ↥K₁ j) ϖ ∈ y.asIdeal :=
    (SSOnSheetK11.germ_toBase_mem_maximalIdeal_iff A ↥K₁ j y ϖ).mp (hϖz ▸ hz)

  let K : IntermediateField L (LaurentSeries L) := ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))
  have hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)) := rfl
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hΓ : CongruenceSubgroup.Gamma1 (M * p) ≤ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 p := by
    refine le_inf (ModularCurve.Gamma1_le_of_dvd (dvd_mul_right M p)) ?_
    intro g hg
    rw [CongruenceSubgroup.Gamma1_mem] at hg
    rw [CongruenceSubgroup.Gamma0_mem]
    have h10 := hg.2.2
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h10 ⊢
    exact (dvd_trans ⟨(M : ℤ), by push_cast; ring⟩ h10 : (p : ℤ) ∣ _)
  have hle : K₁ ≤ K := by
    rw [hK₁]
    exact IntermediateField.adjoin.mono L _ _ (Set.image_mono (ModularCurve.qExpFunctionFieldC_mono ℚ hΓ))
  letI algAK : Algebra A ↥K := ((algebraMap L ↥K).comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L ↥K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let jK : ↥K := ⟨(j : LaurentSeries L), hle j.2⟩
  have hjK : ((jK : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq := hj
  have hjjK : (IntermediateField.inclusion hle j : ↥K) = jK := rfl
  haveI : Fact (jK ≠ 0) := ⟨fun h0 => (Fact.out : j ≠ 0) (Subtype.ext (by
    have := congrArg Subtype.val h0
    exact this))⟩
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (M * p) := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  haveI hFDK := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CongruenceSubgroup.Gamma1 (M * p)) hT L K hK jK hjK
  have htjK : Transcendental A jK := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A jK hjK
  have hsepK : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({jK} : Set ↥K)) ↥K := Algebra.IsSeparable.of_integral _ _

  obtain ⟨ιF, hιF, hιFinj⟩ := SSCrossRingK11.exists_algHom_chartAlgFin A (↥K₁) (↥K)
    ((IntermediateField.inclusion hle).restrictScalars A) j jK hjjK
  letI algι : Algebra ↥(chartAlgFin A (↥K₁) j) ↥(chartAlgFin A (↥K) jK) := ιF.toRingHom.toAlgebra
  haveI : IsScalarTower A ↥(chartAlgFin A (↥K₁) j) ↥(chartAlgFin A (↥K) jK) :=
    IsScalarTower.of_algebraMap_eq (fun a => (ιF.commutes a).symm)
  haveI : Module.Finite ↥(chartAlgFin A (↥K₁) j) ↥(chartAlgFin A (↥K) jK) :=
    SSCrossRingK11.finite_chartAlgFin_of_floor A L K K₁ hle jK j hjjK htjK hFDK hιF
  haveI : Algebra.IsIntegral ↥(chartAlgFin A (↥K₁) j) ↥(chartAlgFin A (↥K) jK) := inferInstance
  have hkerι : (⊥ : Ideal ↥(chartAlgFin A (↥K) jK)).comap (algebraMap ↥(chartAlgFin A (↥K₁) j) ↥(chartAlgFin A (↥K) jK)) ≤ y.asIdeal := by
    rw [← RingHom.ker_eq_comap_bot]
    have hk : RingHom.ker (algebraMap ↥(chartAlgFin A (↥K₁) j) ↥(chartAlgFin A (↥K) jK)) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot (algebraMap ↥(chartAlgFin A (↥K₁) j) ↥(chartAlgFin A (↥K) jK))).mp hιFinj
    rw [hk]
    exact bot_le
  obtain ⟨𝔶', -, h𝔶'prime, hover⟩ := Ideal.exists_ideal_over_prime_of_isIntegral y.asIdeal ⊥ hkerι
  haveI := h𝔶'prime
  have hιFj : ιF (jChartFin A (↥K₁) j) = jChartFin A (↥K) jK := by
    apply Subtype.ext
    rw [hιF, coe_jChartFin, coe_jChartFin]
    rfl

  have hss' : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
      (φ : ↥(chartAlgFin A (↥K) jK) →+* Ω), RingHom.ker φ = 𝔶' → φ (jChartFin A (↥K) jK) ∈ ModularCurve.ssJSet p Ω := by
    intro Ω _ _ _ _ φ hφ
    have hker : RingHom.ker (φ.comp ιF.toRingHom) = y.asIdeal := by
      rw [← RingHom.comap_ker, hφ]
      exact hover
    have h := hss Ω (φ.comp ιF.toRingHom) hker
    rwa [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hιFj] at h
  have hyϖ' : algebraMap A ↥(chartAlgFin A (↥K) jK) ϖ ∈ 𝔶' := by
    have : algebraMap A ↥(chartAlgFin A (↥K₁) j) ϖ ∈ 𝔶'.comap (algebraMap _ ↥(chartAlgFin A (↥K) jK)) := by
      rw [hover]; exact hyϖ
    rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply] at this
    exact this

  have hring := ModularCurve.XOneP.le_of_mem_minimalPrimes_span_of_mem_ssJSet_chartAlgFin_x1_mul
    p M hM hpM L ζ hζ K hK A hAp hζA jK hjK ϖ hϖ 𝔶' hyϖ' hss'
  obtain ⟨w⟩ := ModularCurve.nonempty_integralWeightOneForm (IsLocalRing.ResidueField A) M (by omega)
  obtain ⟨V₀, V₁, h1, h2, h3, h4, h5, -⟩ :=
    ModularCurve.XOneP.exists_valuationSubring_pair_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA jK hjK w
  obtain ⟨-, hii, -, -⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.mem_minimalPrimes_span_iff_of_valuationSubring_pair
      A L (↥K) jK htjK hFDK hsepK ϖ hϖ V₀ V₁ h1 h2 h3 h5
  obtain ⟨𝔓₀, h𝔓₀min, h𝔓₀mem⟩ := hii 0
  have hle𝔶 : 𝔓₀ ≤ 𝔶' := hring 𝔓₀ h𝔓₀min

  have hcomap : V₀.comap (IntermediateField.inclusion hle).toRingHom = W₀ := by
    ext f
    rw [ValuationSubring.mem_comap, hW₀, h4]
    rfl
  have hsV : ((ιF s : ↥(chartAlgFin A (↥K) jK)) : ↥K) ∈ V₀.nonunits := by
    rw [hιF]
    change (IntermediateField.inclusion hle).toRingHom (s : ↥K₁) ∈ V₀.nonunits
    rw [SSCrossRingK11.map_mem_nonunits_iff, hcomap]
    exact hs
  have hs𝔓₀ : ιF s ∈ 𝔓₀ := by
    rw [h𝔓₀mem]
    simpa using hsV
  have hs𝔶' : ιF s ∈ 𝔶' := hle𝔶 hs𝔓₀
  have : s ∈ 𝔶'.comap (algebraMap _ ↥(chartAlgFin A (↥K) jK)) := hs𝔶'
  rwa [hover] at this

end S_ModularCurve_XOneGammaZeroP_mem_of_coe_mem_nonunits_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0
end P2MW
export P2MW.S_ModularCurve_XOneGammaZeroP_mem_of_coe_mem_nonunits_of_mem_ssJSet_twoChartIntegralModel_x1x0_gamma0 (solution)
