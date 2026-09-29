-- Prove2me | solution 1 for ModularCurve.XOneP.mem_range_inter_range_of_iotaFin_eq_of_map_jChartFin_mem_ssJSet_specialFibre_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/47119a8e-f0e3-5c38-bf54-828b1cf9c308

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_XOneP_not_subsingleton_minimalPrimes_span_germ_of_mem_ssJSet_twoChartIntegralModel_x1_mul
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_isOpenImmersion_spec_tensor_chartAlgFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_mem_range_inter_range_of_iotaFin_eq_of_map_jChartFin_mem_ssJSet_specialFibre_twoChartModel_x1_mul
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "instance" "ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V"
p2m_attr_erase "simp" "TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP"
p2m_attr_erase "simp" "ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk"
p2m_attr_erase "simp" "ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_baseChangeRingHom ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.cuspCount_one WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"

set_option autoImplicit false

namespace R1LCfc7491e9

open scoped TensorProduct

open PrimeSpectrum in
theorem mem_inter_of_two_minimalPrimes {T : Type*} [CommRing T]
    (U₁ U₂ : Set (PrimeSpectrum T)) (hU₁ : IsClosed U₁) (hU₂ : IsClosed U₂)
    (hI₁ : IsPreirreducible U₁) (hI₂ : IsPreirreducible U₂)
    (hcov : ∀ z, z ∈ U₁ ∨ z ∈ U₂)
    (𝔓 : PrimeSpectrum T) (𝔔₁ 𝔔₂ : Ideal T)
    (h₁ : 𝔔₁ ∈ minimalPrimes T) (h₂ : 𝔔₂ ∈ minimalPrimes T) (hne : 𝔔₁ ≠ 𝔔₂)
    (hle₁ : 𝔔₁ ≤ 𝔓.asIdeal) (hle₂ : 𝔔₂ ≤ 𝔓.asIdeal) : 𝔓 ∈ U₁ ∩ U₂ := by
  haveI hp₁ : 𝔔₁.IsPrime := h₁.1.1
  haveI hp₂ : 𝔔₂.IsPrime := h₂.1.1
  have hV₁ : zeroLocus (𝔔₁ : Set T) ∈ irreducibleComponents (PrimeSpectrum T) := by
    rw [zeroLocus_ideal_mem_irreducibleComponents, hp₁.radical]; exact h₁
  have hV₂ : zeroLocus (𝔔₂ : Set T) ∈ irreducibleComponents (PrimeSpectrum T) := by
    rw [zeroLocus_ideal_mem_irreducibleComponents, hp₂.radical]; exact h₂
  have hPV₁ : 𝔓 ∈ zeroLocus (𝔔₁ : Set T) := hle₁
  have hPV₂ : 𝔓 ∈ zeroLocus (𝔔₂ : Set T) := hle₂
  have hVne : zeroLocus (𝔔₁ : Set T) ≠ zeroLocus (𝔔₂ : Set T) := by
    intro h
    have h21 : 𝔔₁ ≤ 𝔔₂ := by
      have : (⟨𝔔₂, hp₂⟩ : PrimeSpectrum T) ∈ zeroLocus (𝔔₁ : Set T) := by
        rw [h]; exact le_refl 𝔔₂
      exact this
    have h12 : 𝔔₂ ≤ 𝔔₁ := by
      have : (⟨𝔔₁, hp₁⟩ : PrimeSpectrum T) ∈ zeroLocus (𝔔₂ : Set T) := by
        rw [← h]; exact le_refl 𝔔₁
      exact this
    exact hne (le_antisymm h21 h12)
  have huniv : ∀ V : Set (PrimeSpectrum T), V ⊆ U₁ ∪ U₂ := fun V z _ => hcov z
  have key : ∀ V ∈ irreducibleComponents (PrimeSpectrum T), V = U₁ ∨ V = U₂ := by
    intro V hV
    have hirr : IsIrreducible V := hV.1
    rcases (isPreirreducible_iff_isClosed_union_isClosed.mp hirr.2) U₁ U₂ hU₁ hU₂ (huniv V) with h | h
    · exact Or.inl (le_antisymm h (hV.2 ⟨hirr.1.mono h, hI₁⟩ h))
    · exact Or.inr (le_antisymm h (hV.2 ⟨hirr.1.mono h, hI₂⟩ h))
  rcases key _ hV₁ with e₁ | e₁ <;> rcases key _ hV₂ with e₂ | e₂
  · exact absurd (e₁.trans e₂.symm) hVne
  · exact ⟨e₁ ▸ hPV₁, e₂ ▸ hPV₂⟩
  · exact ⟨e₂ ▸ hPV₂, e₁ ▸ hPV₁⟩
  · exact absurd (e₁.trans e₂.symm) hVne

theorem exists_pair_minimalPrimes_of_isLocalization_atPrime {B S : Type*} [CommRing B] [CommRing S]
    [Algebra B S] (y : Ideal B) [y.IsPrime] [IsLocalization.AtPrime S y] (b : B)
    (h : ¬ ((Ideal.span {algebraMap B S b}).minimalPrimes).Subsingleton) :
    ∃ p₁ p₂ : Ideal B, p₁ ≠ p₂ ∧ p₁ ∈ (Ideal.span {b}).minimalPrimes ∧ p₂ ∈ (Ideal.span {b}).minimalPrimes ∧
      p₁ ≤ y ∧ p₂ ≤ y := by
  have one : ∀ Q ∈ (Ideal.span {algebraMap B S b}).minimalPrimes,
      Q.under B ∈ (Ideal.span {b}).minimalPrimes ∧ Q.under B ≤ y := by
    intro Q hQ
    haveI hQp : Q.IsPrime := hQ.1.1
    have hbQ : algebraMap B S b ∈ Q := hQ.1.2 (Ideal.subset_span rfl)
    obtain ⟨hprime, hdisj⟩ := (IsLocalization.isPrime_iff_isPrime_disjoint y.primeCompl S Q).mp hQp
    have hle : Q.under B ≤ y := by
      intro x hx
      by_contra hxy
      exact Set.disjoint_left.mp hdisj (show x ∈ (y.primeCompl : Set B) from hxy) hx
    refine ⟨⟨⟨hprime, ?_⟩, ?_⟩, hle⟩
    · rw [Ideal.span_singleton_le_iff_mem]; exact hbQ
    · rintro q ⟨hq, hbq⟩ hqle
      haveI := hq
      have hqy : q ≤ y := hqle.trans hle
      have hdq : Disjoint (y.primeCompl : Set B) (q : Set B) :=
        Set.disjoint_left.mpr fun x hx hxq => hx (hqy hxq)
      have hQ' : (q.map (algebraMap B S)).IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint y.primeCompl S q hq hdq
      have hle' : q.map (algebraMap B S) ≤ Q := by
        rw [← IsLocalization.map_under y.primeCompl S Q]
        exact Ideal.map_mono hqle
      have hb' : Ideal.span {algebraMap B S b} ≤ q.map (algebraMap B S) := by
        rw [Ideal.span_singleton_le_iff_mem]
        exact Ideal.mem_map_of_mem _ (hbq (Ideal.subset_span rfl))
      have hQle : Q ≤ q.map (algebraMap B S) := hQ.2 ⟨hQ', hb'⟩ hle'
      calc Q.under B ≤ (q.map (algebraMap B S)).under B := Ideal.comap_mono hQle
        _ = q := IsLocalization.under_map_of_isPrime_disjoint y.primeCompl S hq hdq
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := Set.not_subsingleton_iff.mp h
  refine ⟨Q₁.under B, Q₂.under B, ?_, (one Q₁ hQ₁).1, (one Q₂ hQ₂).1, (one Q₁ hQ₁).2, (one Q₂ hQ₂).2⟩
  intro heq
  apply hne
  rw [← IsLocalization.map_under y.primeCompl S Q₁, ← IsLocalization.map_under y.primeCompl S Q₂]
  exact congrArg _ heq

theorem exists_prime_le_comap_eq_tensor
    {A B k : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] [Field k] [Algebra A k]
    (hk : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A k a = 0)
    (𝔭 y : Ideal B) [𝔭.IsPrime] [y.IsPrime]
    (hJ𝔭 : (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ 𝔭) (h𝔭y : 𝔭 ≤ y)
    (𝔓 : Ideal (B ⊗[A] k)) [𝔓.IsPrime]
    (h𝔓 : 𝔓.comap (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := k)) = y) :
    ∃ 𝔔 : Ideal (B ⊗[A] k), 𝔔 ≤ 𝔓 ∧ 𝔔.IsPrime ∧
      𝔔.comap (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := k)) = 𝔭 := by
  classical
  set m : Ideal A := IsLocalRing.maximalIdeal A with hm
  haveI hmmax : m.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  set J : Ideal B := m.map (algebraMap A B) with hJdef
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  letI algFk : Algebra (A ⧸ m) k := (Ideal.Quotient.lift m (algebraMap A k) hk).toAlgebra
  haveI : IsScalarTower A (A ⧸ m) k :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      rw [RingHom.algebraMap_toAlgebra, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.lift_mk])
  haveI : TensorProduct.CompatibleSMul A (A ⧸ m) (B ⧸ J) k := ⟨fun f x n => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
    rw [← Ideal.Quotient.algebraMap_eq, algebraMap_smul, algebraMap_smul, TensorProduct.smul_tmul]⟩

  let e₁ : (B ⧸ J) ⊗[A ⧸ m] k ≃ₐ[B ⧸ J] (B ⧸ J) ⊗[A] k :=
    Algebra.TensorProduct.equivOfCompatibleSMul A (A ⧸ m) (B ⧸ J) (B ⧸ J) k
  have he₁ : ∀ (b : B ⧸ J) (c : k), e₁ (b ⊗ₜ c) = b ⊗ₜ c := fun b c => rfl
  haveI : Module.Flat (B ⧸ J) ((B ⧸ J) ⊗[A ⧸ m] k) := inferInstance
  haveI : Module.Flat (B ⧸ J) ((B ⧸ J) ⊗[A] k) := Module.Flat.of_linearEquiv e₁.symm.toLinearEquiv
  haveI : Algebra.HasGoingDown (B ⧸ J) ((B ⧸ J) ⊗[A] k) := inferInstance

  have hJker : ∀ b ∈ J, (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := k)) b = 0 := by
    intro b hb
    have hle : J ≤ RingHom.ker (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := k)).toRingHom := by
      rw [hJdef, Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes,
        Algebra.TensorProduct.algebraMap_apply', hk a ha, TensorProduct.tmul_zero]
    exact hle hb
  let ψ : (B ⧸ J) →ₐ[A] B ⊗[A] k := Ideal.Quotient.liftₐ J (Algebra.TensorProduct.includeLeft) hJker
  have hψ : ∀ b : B, ψ (Ideal.Quotient.mk J b) = b ⊗ₜ 1 := fun b => rfl
  let fwd : B ⊗[A] k →ₐ[A] (B ⧸ J) ⊗[A] k :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ A J) (AlgHom.id A k)
  let bwd : (B ⧸ J) ⊗[A] k →ₐ[A] B ⊗[A] k :=
    Algebra.TensorProduct.lift ψ Algebra.TensorProduct.includeRight (fun _ _ => Commute.all _ _)
  have hbwd : ∀ (b : B) (c : k), bwd (Ideal.Quotient.mk J b ⊗ₜ c) = b ⊗ₜ c := by
    intro b c
    simp only [bwd, Algebra.TensorProduct.lift_tmul, hψ, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have hfwd : ∀ (b : B) (c : k), fwd (b ⊗ₜ c) = Ideal.Quotient.mk J b ⊗ₜ c := by
    intro b c
    simp only [fwd, Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply]
  have h₁ : bwd.comp fwd = AlgHom.id A _ := by
    apply Algebra.TensorProduct.ext'
    intro b c
    simp only [AlgHom.comp_apply, hfwd, hbwd, AlgHom.id_apply]
  have h₂ : fwd.comp bwd = AlgHom.id A _ := by
    apply Algebra.TensorProduct.ext'
    intro b c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    simp only [AlgHom.comp_apply, hbwd, hfwd, AlgHom.id_apply]
  let e₂ : (B ⧸ J) ⊗[A] k ≃ₐ[A] B ⊗[A] k := AlgEquiv.ofAlgHom bwd fwd h₁ h₂
  have he₂ : ∀ (b : B) (c : k), e₂ (Ideal.Quotient.mk J b ⊗ₜ c) = b ⊗ₜ c := hbwd

  let e : (B ⧸ J) ⊗[A ⧸ m] k ≃+* B ⊗[A] k := e₁.toRingEquiv.trans e₂.toRingEquiv
  set iL := Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := k) with hiL
  have hcomp : (e.toRingHom.comp (algebraMap (B ⧸ J) ((B ⧸ J) ⊗[A ⧸ m] k))).comp (Ideal.Quotient.mk J) = iL := by
    ext b
    simp only [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e, RingEquiv.trans_apply,
      AlgEquiv.coe_ringEquiv, he₁, he₂, hiL,
      Algebra.TensorProduct.includeLeftRingHom_apply]

  have hJy : J ≤ y := hJ𝔭.trans h𝔭y
  have hkerJ : RingHom.ker (Ideal.Quotient.mk J) = J := Ideal.mk_ker
  haveI hp : (𝔭.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [hkerJ]; exact hJ𝔭)
  haveI hq : (y.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [hkerJ]; exact hJy)
  have hpq : 𝔭.map (Ideal.Quotient.mk J) ≤ y.map (Ideal.Quotient.mk J) := Ideal.map_mono h𝔭y
  have hcm : ∀ I : Ideal B, J ≤ I → (I.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) = I := by
    intro I hI
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, hkerJ]
    exact sup_eq_left.mpr hI

  set Q : Ideal ((B ⧸ J) ⊗[A ⧸ m] k) := 𝔓.comap e.toRingHom with hQ
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  haveI : Q.LiesOver (y.map (Ideal.Quotient.mk J)) := by
    refine ⟨?_⟩
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    rw [hcm y hJy, Ideal.under_def, hQ, Ideal.comap_comap, Ideal.comap_comap, ← RingHom.comp_assoc, hcomp, h𝔓]
  obtain ⟨P, hPQ, hP, hPo⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le Q (p := 𝔭.map (Ideal.Quotient.mk J)) (q := y.map (Ideal.Quotient.mk J)) hpq
  refine ⟨P.comap e.symm.toRingHom, ?_, Ideal.comap_isPrime _ _, ?_⟩
  · intro x hx
    rw [Ideal.mem_comap] at hx
    have := hPQ hx
    rw [hQ, Ideal.mem_comap] at this
    simpa using this
  · have hsymm : e.symm.toRingHom.comp iL =
        (algebraMap (B ⧸ J) ((B ⧸ J) ⊗[A ⧸ m] k)).comp (Ideal.Quotient.mk J) := by
      rw [← hcomp]
      ext b
      simp
    rw [Ideal.comap_comap, hsymm, ← Ideal.comap_comap, ← Ideal.under_def, ← hPo.over, hcm 𝔭 hJ𝔭]

section Stalk

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

universe u

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

theorem stalk_ιFin_package (ϖ : R) (y : ↥(XFin R F j))
    (ϖz : (TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y))
    (hϖz : ϖz = ((TwoChartIntegralModel R F j).presheaf.germ ⊤ ((ιFin R F j).base y) trivial).hom
      (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))) :
    (algebraMap R ↥(chartAlgFin R F j) ϖ ∈ y.asIdeal →
      ϖz ∈ IsLocalRing.maximalIdeal ((TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y))) ∧
    (¬ ((Ideal.span {ϖz} : Ideal ((TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y))).minimalPrimes).Subsingleton →
      ∃ p₁ p₂ : Ideal ↥(chartAlgFin R F j), p₁ ≠ p₂ ∧
        p₁ ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes ∧
        p₂ ∈ (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).minimalPrimes ∧
        p₁ ≤ y.asIdeal ∧ p₂ ≤ y.asIdeal) := by

  set st := (ιFin R F j).stalkMap y with hst
  haveI : IsIso st := by rw [hst]; infer_instance

  let φ : ↥(chartAlgFin R F j) →+* ↑((TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)) :=
    (inv st).hom.comp (StructureSheaf.toStalk (↥(chartAlgFin R F j)) y).hom
  letI : Algebra ↥(chartAlgFin R F j) ↑((TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)) :=
    φ.toAlgebra
  let e : ↑((structurePresheafInCommRingCat ↥(chartAlgFin R F j)).stalk y) ≃ₐ[↥(chartAlgFin R F j)]
      ↑((TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)) :=
    { (asIso st).symm.commRingCatIsoToRingEquiv with
      commutes' := fun b => rfl }
  haveI hloc : IsLocalization.AtPrime ((TwoChartIntegralModel R F j).presheaf.stalk ((ιFin R F j).base y)) y.asIdeal :=
    IsLocalization.isLocalization_of_algEquiv y.asIdeal.primeCompl e

  have hel : st.hom (((TwoChartIntegralModel R F j).presheaf.germ ⊤ ((ιFin R F j).base y) trivial).hom
      (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))) =
      (StructureSheaf.toStalk (↥(chartAlgFin R F j)) y).hom (algebraMap R _ ϖ) := by
    rw [hst, Scheme.Hom.germ_stalkMap_apply]
    have h1 : ((ιFin R F j).app ⊤).hom (((toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)) =
        ((ιFin R F j ≫ toBase R F j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ) := rfl
    rw [h1, ιFin_toBase]
    have h2 := congrArg (fun h => h.hom ϖ)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R ↥(chartAlgFin R F j))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    rw [← h2]
    rfl
  have hφ : algebraMap ↥(chartAlgFin R F j) _ (algebraMap R ↥(chartAlgFin R F j) ϖ) = ϖz := by
    rw [hϖz]
    change (inv st).hom ((StructureSheaf.toStalk (↥(chartAlgFin R F j)) y).hom (algebraMap R _ ϖ)) = _
    rw [← hel, ← CommRingCat.comp_apply, IsIso.hom_inv_id, CommRingCat.id_apply]
  refine ⟨fun hy => ?_, fun h => ?_⟩
  · rw [← hφ]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ y.asIdeal _).mpr hy
  · rw [← hφ] at h
    exact exists_pair_minimalPrimes_of_isLocalization_atPrime y.asIdeal _ h

end Stalk

theorem eq_maximalIdeal_of_natCast_mem {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (p : ℕ) (hp0 : (p : A) ≠ 0) (𝔫 : Ideal A) [𝔫.IsPrime] (h : (p : A) ∈ 𝔫) :
    𝔫 = IsLocalRing.maximalIdeal A := by
  have hne : 𝔫 ≠ ⊥ := fun h0 => hp0 (by rw [h0] at h; exact (Ideal.mem_bot).mp h)
  exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hne)

section Main

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem mem_range_inter_range_generic
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (toBase A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (toBase A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (toBase A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (x : ↥(pullback (toBase A (↥K) j) (specMap A k)))
    (y : ↥(XFin A (↥K) j))
    (hy : (ιFin A (↥K) j).base y = (pullback.fst (toBase A (↥K) j) (specMap A k)).base x)
    (hyp : (p : ↥(chartAlgFin A (↥K) j)) ∈ y.asIdeal)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ : ↥(chartAlgFin A (↥K) j) →+* Ω),
        RingHom.ker φ = y.asIdeal → φ (jChartFin A (↥K) j) ∈ ModularCurve.ssJSet p Ω) :
    x ∈ Set.range i₁.1.base ∩ Set.range i₂.1.base := by
  classical
  have hp0 : (p : A) ≠ 0 := by
    intro h
    have h' : algebraMap A L (p : A) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h'
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h'

  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖirr

  have hyϖ : algebraMap A ↥(chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal := by
    have h𝔫 : y.asIdeal.comap (algebraMap A ↥(chartAlgFin A (↥K) j)) = IsLocalRing.maximalIdeal A := by
      refine eq_maximalIdeal_of_natCast_mem p hp0 _ ?_
      rw [Ideal.mem_comap, map_natCast]
      exact hyp
    have : ϖ ∈ y.asIdeal.comap (algebraMap A ↥(chartAlgFin A (↥K) j)) := by
      rw [h𝔫, hϖ]; exact Ideal.mem_span_singleton_self ϖ
    exact this

  have hk : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A k a = 0 := by
    have hker : RingHom.ker (algebraMap A k) = IsLocalRing.maximalIdeal A := by
      haveI : (RingHom.ker (algebraMap A k)).IsPrime := RingHom.ker_isPrime _
      refine eq_maximalIdeal_of_natCast_mem p hp0 _ ?_
      rw [RingHom.mem_ker, map_natCast]
      exact CharP.cast_eq_zero k p
    intro a ha
    rw [← RingHom.mem_ker, hker]
    exact ha

  set z : ↥(TwoChartIntegralModel A (↥K) j) := (ιFin A (↥K) j).base y with hzdef
  set ϖz : ↑((TwoChartIntegralModel A (↥K) j).presheaf.stalk z) :=
    ((TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((toBase A (↥K) j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)) with hϖz
  obtain ⟨hzmax, hpair⟩ := stalk_ιFin_package A (↥K) j ϖ y ϖz hϖz
  have hz : ϖz ∈ IsLocalRing.maximalIdeal ((TwoChartIntegralModel A (↥K) j).presheaf.stalk z) := hzmax hyϖ
  have h2br : ¬ ((Ideal.span {ϖz} : Ideal ((TwoChartIntegralModel A (↥K) j).presheaf.stalk z)).minimalPrimes).Subsingleton :=
    ModularCurve.XOneP.not_subsingleton_minimalPrimes_span_germ_of_mem_ssJSet_twoChartIntegralModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj ϖ hϖ z ϖz hϖz hz y hzdef.symm hss
  obtain ⟨𝔭₁, 𝔭₂, h𝔭ne, h𝔭₁, h𝔭₂, h𝔭₁y, h𝔭₂y⟩ := hpair h2br
  have hmapm : (IsLocalRing.maximalIdeal A).map (algebraMap A ↥(chartAlgFin A (↥K) j)) =
      Ideal.span {algebraMap A ↥(chartAlgFin A (↥K) j) ϖ} := by
    rw [hϖ, Ideal.map_span, Set.image_singleton]

  obtain ⟨g, hgimm, hg₁, hg₂, hgr⟩ := exists_isOpenImmersion_spec_tensor_chartAlgFin A (↥K) j k
  have hxr : x ∈ Set.range g.base := by
    rw [hgr]
    exact ⟨y, trivial, hy⟩
  obtain ⟨𝔓, h𝔓x⟩ := hxr
  set iL := Algebra.TensorProduct.includeLeftRingHom (R := A) (A := ↥(chartAlgFin A (↥K) j)) (B := k) with hiL
  have h𝔓y : 𝔓.asIdeal.comap iL = y.asIdeal := by
    have h := congrArg (fun h => h.base 𝔓) hg₁
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [h𝔓x] at h
    have h' : (ιFin A (↥K) j).base ((Spec.map (CommRingCat.ofHom iL)).base 𝔓) = (ιFin A (↥K) j).base y := by
      rw [← h]; exact hy.symm
    have hinj := (ιFin A (↥K) j).isOpenEmbedding.injective h'
    exact congrArg PrimeSpectrum.asIdeal hinj

  have lift : ∀ 𝔭 : Ideal ↥(chartAlgFin A (↥K) j),
      𝔭 ∈ (Ideal.span {algebraMap A ↥(chartAlgFin A (↥K) j) ϖ}).minimalPrimes → 𝔭 ≤ y.asIdeal →
      ∃ 𝔔 : Ideal (↥(chartAlgFin A (↥K) j) ⊗[A] k),
        𝔔 ∈ minimalPrimes (↥(chartAlgFin A (↥K) j) ⊗[A] k) ∧ 𝔔 ≤ 𝔓.asIdeal ∧ 𝔔.comap iL = 𝔭 := by
    intro 𝔭 h𝔭 h𝔭y
    haveI : 𝔭.IsPrime := h𝔭.1.1
    obtain ⟨𝔔', h𝔔'𝔓, h𝔔'p, h𝔔'c⟩ :=
      exists_prime_le_comap_eq_tensor hk 𝔭 y.asIdeal (hmapm ▸ h𝔭.1.2) h𝔭y 𝔓.asIdeal h𝔓y
    haveI := h𝔔'p
    obtain ⟨𝔔, h𝔔min, h𝔔le⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (↥(chartAlgFin A (↥K) j) ⊗[A] k))) (J := 𝔔') bot_le
    haveI : 𝔔.IsPrime := h𝔔min.1.1
    refine ⟨𝔔, h𝔔min, h𝔔le.trans h𝔔'𝔓, le_antisymm ?_ ?_⟩
    · calc 𝔔.comap iL ≤ 𝔔'.comap iL := Ideal.comap_mono h𝔔le
        _ = 𝔭 := h𝔔'c
    · refine h𝔭.2 ⟨Ideal.comap_isPrime iL 𝔔, ?_⟩ ((Ideal.comap_mono h𝔔le).trans h𝔔'c.le)
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, hiL, Algebra.TensorProduct.includeLeftRingHom_apply,
        ← Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply',
        hk ϖ (hϖ ▸ Ideal.mem_span_singleton_self ϖ), TensorProduct.tmul_zero]
      exact zero_mem _
  obtain ⟨𝔔₁, h𝔔₁min, h𝔔₁le, h𝔔₁c⟩ := lift 𝔭₁ h𝔭₁ h𝔭₁y
  obtain ⟨𝔔₂, h𝔔₂min, h𝔔₂le, h𝔔₂c⟩ := lift 𝔭₂ h𝔭₂ h𝔭₂y
  have h𝔔ne : 𝔔₁ ≠ 𝔔₂ := fun h => h𝔭ne (by rw [← h𝔔₁c, ← h𝔔₂c, h])

  haveI : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI : Nonempty ↥(Spec (CommRingCat.of k)) := inferInstanceAs (Nonempty (PrimeSpectrum k))
  haveI : IrreducibleSpace ↥C₁ := GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := c₁)
  haveI : IrreducibleSpace ↥C₂ := GeometricallyIrreducible.irreducibleSpace_of_subsingleton (f := c₂)
  have hirr₁ : IsIrreducible (Set.range i₁.1.base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ i₁.1.base.hom.continuous.continuousOn
  have hirr₂ : IsIrreducible (Set.range i₂.1.base) := by
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ i₂.1.base.hom.continuous.continuousOn
  have hmem := mem_inter_of_two_minimalPrimes
    (g.base ⁻¹' Set.range i₁.1.base) (g.base ⁻¹' Set.range i₂.1.base)
    (i₁.1.isClosedEmbedding.isClosed_range.preimage g.base.hom.continuous)
    (i₂.1.isClosedEmbedding.isClosed_range.preimage g.base.hom.continuous)
    (hirr₁.2.preimage g.isOpenEmbedding) (hirr₂.2.preimage g.isOpenEmbedding)
    (fun w => hcover (g.base w)) 𝔓 𝔔₁ 𝔔₂ h𝔔₁min h𝔔₂min h𝔔ne h𝔔₁le h𝔔₂le
  rw [← h𝔓x]
  exact hmem

end Main

end R1LCfc7491e9

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

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

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (x : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)))
    (y : ↥(ModularCurve.TwoChart.XFin A (↥K) j))
    (hy : (ModularCurve.TwoChart.ιFin A (↥K) j).base y = (pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base x)
    (hyp : (p : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) ∈ y.asIdeal)
    (hss : ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
        (φ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* Ω),
        RingHom.ker φ = y.asIdeal → φ (ModularCurve.TwoChart.jChartFin A (↥K) j) ∈ ModularCurve.ssJSet p Ω) :
    x ∈ Set.range i₁.1.base ∩ Set.range i₂.1.base :=
  @R1LCfc7491e9.mem_range_inter_range_generic p _ M _ hM hpM L _ _ _ ζ hζ K hK A _ _ _ _ _ hAp hζA _ _ j hj _
    k _ _ _ _ C₁ C₂ c₁ c₂ _ _ _ _ _ _ i₁ i₂ ‹IsClosedImmersion i₁.1› ‹IsClosedImmersion i₂.1›
    hcover x y hy hyp hss

end S_ModularCurve_XOneP_mem_range_inter_range_of_iotaFin_eq_of_map_jChartFin_mem_ssJSet_specialFibre_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_mem_range_inter_range_of_iotaFin_eq_of_map_jChartFin_mem_ssJSet_specialFibre_twoChartModel_x1_mul (solution)
