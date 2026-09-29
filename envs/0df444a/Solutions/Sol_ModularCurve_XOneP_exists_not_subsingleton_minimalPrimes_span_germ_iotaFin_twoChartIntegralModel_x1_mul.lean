-- Prove2me | solution 1 for ModularCurve.XOneP.exists_not_subsingleton_minimalPrimes_span_germ_iotaFin_twoChartIntegralModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c5139aab-86cc-5e37-b47e-294f71022d66

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_XOneP_not_subsingleton_minimalPrimes_span_germ_of_mem_ssJSet_twoChartIntegralModel_x1_mul
import Theorems.Thm_ModularCurve_ssJSet_nonempty
import Theorems.Thm_ModularCurve_mem_ssJSet_map_of_isAlgClosed
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
import Theorems.Thm_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_not_subsingleton_minimalPrimes_span_germ_iotaFin_twoChartIntegralModel_x1_mul
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure"
p2m_attr_erase "instance" "instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10"
p2m_attr_erase "simp" "CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk"
p2m_attr_erase "simp" "ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_baseChangeRingHom ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.cuspCount_one WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
p2m_open_scoped "TensorProduct Polynomial AlgebraicGeometry.Polynomial"

namespace CrossExists

theorem germ_mem_maximalIdeal_iff_of_chart
    {A S : Type} [CommRing A] [CommRing S] [Algebra A S] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of A)) (ι : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A S))) (q : ↥(Spec (CommRingCat.of S))) (a : A) :
    (X.presheaf.germ ⊤ (ι.base q) trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk (ι.base q)) ↔
      algebraMap A S a ∈ q.asIdeal := by

  have key : (ι.stalkMap q).hom ((X.presheaf.germ ⊤ (ι.base q) trivial).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
      ((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (algebraMap A S a)) := by
    erw [Scheme.Hom.germ_stalkMap_apply ι ⊤ q trivial]
    congr 1
    show ((f.appTop ≫ ι.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = _
    rw [← Scheme.Hom.comp_appTop, hι]
    show ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap A S))).appTop).hom a = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff (ι.stalkMap q).hom, key,
    ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]

  letI : Algebra S ((Spec (CommRingCat.of S)).presheaf.stalk q) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := S) q
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of S)).presheaf.stalk q) q.asIdeal :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk S q
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff ((Spec (CommRingCat.of S)).presheaf.stalk q) q.asIdeal (algebraMap A S a)

theorem forall_mem_ssJSet_of_exists
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (s : S) (y : Ideal S) [y.IsPrime]
    (Ω₀ : Type) [Field Ω₀] [CharP Ω₀ p] [IsAlgClosed Ω₀] [DecidableEq Ω₀] [Algebra (ZMod p) Ω₀] [Algebra.IsAlgebraic (ZMod p) Ω₀]
    (φ₀ : S →+* Ω₀) (hker₀ : RingHom.ker φ₀ = y) (hss₀ : φ₀ s ∈ ModularCurve.ssJSet p Ω₀) :
    ∀ (Ω : Type) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω] (φ : S →+* Ω),
      RingHom.ker φ = y → φ s ∈ ModularCurve.ssJSet p Ω := by
  intro Ω _ _ _ _ φ hker

  let ι₀ : S ⧸ y →+* Ω₀ := Ideal.Quotient.lift y φ₀ (fun a ha => by rwa [← RingHom.mem_ker, hker₀])
  let ι : S ⧸ y →+* Ω := Ideal.Quotient.lift y φ (fun a ha => by rwa [← RingHom.mem_ker, hker])
  have hι₀ : Function.Injective ι₀ := by
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_quotient_lift, hker₀, Ideal.map_quotient_self]
  have hι : Function.Injective ι := by
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_quotient_lift, hker, Ideal.map_quotient_self]
  haveI : IsDomain (S ⧸ y) := Ideal.Quotient.isDomain y
  letI : Algebra (S ⧸ y) Ω₀ := ι₀.toAlgebra
  letI : Algebra (S ⧸ y) Ω := ι.toAlgebra
  haveI : Module.IsTorsionFree (S ⧸ y) Ω₀ := Module.isTorsionFree_iff_algebraMap_injective.mpr hι₀
  haveI : Module.IsTorsionFree (S ⧸ y) Ω := Module.isTorsionFree_iff_algebraMap_injective.mpr hι

  haveI : CharP (S ⧸ y) p := ι₀.charP hι₀ p
  letI : Algebra (ZMod p) (S ⧸ y) := ZMod.algebra _ p
  haveI : IsScalarTower (ZMod p) (S ⧸ y) Ω₀ :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic (S ⧸ y) Ω₀ :=
    Algebra.IsAlgebraic.extendScalars (R := ZMod p) (S := S ⧸ y) (A := Ω₀) (algebraMap (ZMod p) (S ⧸ y)).injective
  let θ : Ω₀ →ₐ[S ⧸ y] Ω := IsAlgClosed.lift
  have hfac : φ s = θ (φ₀ s) := by
    have h0 : φ₀ s = algebraMap (S ⧸ y) Ω₀ (Ideal.Quotient.mk y s) := rfl
    have h1 : φ s = algebraMap (S ⧸ y) Ω (Ideal.Quotient.mk y s) := rfl
    rw [h0, h1, AlgHom.commutes]
  rw [hfac]
  exact ModularCurve.mem_ssJSet_map_of_isAlgClosed θ.toRingHom _ hss₀

end CrossExists

open CrossExists in
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
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    ∃ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j),
      ¬ ((Ideal.span {(((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y) trivial).hom
          (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))} :
        Ideal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk
          ((AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y))).minimalPrimes).Subsingleton := by
  classical

  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) (Fact.out : p.Prime).ne_zero⟩
  have htj := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj

  let Ω₀ := AlgebraicClosure (ZMod p)
  obtain ⟨j₀, hj₀⟩ := ModularCurve.ssJSet_nonempty (q := p) (k := Ω₀)

  haveI : CharP (IsLocalRing.ResidueField A) p := IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal A p hAp
  haveI : Finite (IsLocalRing.ResidueField A) := by
    have hsurj := IsCyclotomicExtension.Rat.surjective_algebraMap_int_residueField_of_isDiscreteValuationRing p L A hAp
    refine Finite.of_surjective (ZMod.castHom (dvd_refl p) (IsLocalRing.ResidueField A)) fun x => ?_
    obtain ⟨n, rfl⟩ := hsurj x
    exact ⟨(n : ZMod p), by simp⟩
  letI : Algebra (ZMod p) (IsLocalRing.ResidueField A) := ZMod.algebra _ p
  haveI : Module.Finite (ZMod p) (IsLocalRing.ResidueField A) := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField A) := Algebra.IsAlgebraic.of_finite _ _
  let e : IsLocalRing.ResidueField A →ₐ[ZMod p] Ω₀ := IsAlgClosed.lift

  let ψ : Polynomial A →+* Ω₀ := Polynomial.eval₂RingHom (e.toRingHom.comp (IsLocalRing.residue A)) j₀
  let φ : Polynomial A →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin A (↥K) j).toRingHom
  have hφX : φ Polynomial.X = AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j :=
    AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X A (↥K) j

  have hφint : φ.IsIntegral := by
    let ψA : Polynomial A →ₐ[A] ↥(Algebra.adjoin A ({(j : ↥K)} : Set ↥K)) :=
      (Polynomial.aeval (j : ↥K)).codRestrict (Algebra.adjoin A ({(j : ↥K)} : Set ↥K))
        (fun P => by rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨P, rfl⟩)
    have hψA : Function.Surjective ψA := by
      rintro ⟨y, hy⟩
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
      obtain ⟨P, rfl⟩ := hy
      exact ⟨P, Subtype.ext rfl⟩
    let incl : ↥(Algebra.adjoin A ({(j : ↥K)} : Set ↥K)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) :=
      (Subalgebra.inclusion (AlgebraicCurve.TwoChartIntegralModel.adjoin_le_chartAlg A (↥K) {(j : ↥K)})).toRingHom
    have hincl : incl.IsIntegral := by
      intro x
      obtain ⟨P, hPm, hP⟩ := (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff A (↥K)).mp x.2
      refine ⟨P, hPm, ?_⟩
      apply Subtype.ext
      have h1 := Polynomial.hom_eval₂ P incl ((AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j).val.toRingHom) x
      have h2 : ((AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j).val.toRingHom).comp incl =
          algebraMap ↥(Algebra.adjoin A ({(j : ↥K)} : Set ↥K)) ↥K := rfl
      rw [h2] at h1
      exact h1.trans hP
    have hcomp : φ = incl.comp ψA.toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        apply Subtype.ext
        simp [φ, ψA, incl, AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin]
      · apply Subtype.ext
        simp [φ, ψA, incl, AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin]
    rw [hcomp]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ hψA) hincl
  letI algφ : Algebra (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := φ.toAlgebra
  haveI : Algebra.IsIntegral (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) := ⟨fun x => hφint x⟩

  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  have hφinj : Function.Injective φ := by
    intro P Q hPQ
    apply (transcendental_iff_injective.mp htj)
    apply_fun (fun b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) => (b : ↥K)) at hPQ
    have hval : ∀ R : Polynomial A, ((φ R : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) : ↥K) = Polynomial.aeval (j : ↥K) R := by
      intro R
      show ((AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j).val
        ((AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin A (↥K) j) R)) = _
      rw [AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin, ← Polynomial.aeval_algHom_apply]
      rfl
    rw [hval, hval] at hPQ
    exact hPQ
  obtain ⟨y, -, hy, hyc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker ψ) (⊥ : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j))
    (by
      rw [← RingHom.ker_eq_comap_bot, show algebraMap (Polynomial A) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) = φ from rfl,
        (RingHom.injective_iff_ker_eq_bot φ).mp hφinj]
      exact bot_le)
  haveI := hy
  have hyc' : y.comap φ = RingHom.ker ψ := hyc

  haveI : (y.comap φ).IsPrime := Ideal.comap_isPrime φ y
  haveI : IsDomain (Polynomial A ⧸ y.comap φ) := Ideal.Quotient.isDomain _
  haveI : IsDomain (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y) := Ideal.Quotient.isDomain _
  let ψbar : (Polynomial A ⧸ y.comap φ) →+* Ω₀ :=
    Ideal.Quotient.lift (y.comap φ) ψ (fun a ha => by rwa [hyc', RingHom.mem_ker] at ha)
  have hψbar : Function.Injective ψbar := by
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_quotient_lift, ← hyc', Ideal.map_quotient_self]
  let qmap : (Polynomial A ⧸ y.comap φ) →+* (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y) := Ideal.quotientMap y φ le_rfl
  have hqmap : Function.Injective qmap := Ideal.quotientMap_injective
  letI algq : Algebra (Polynomial A ⧸ y.comap φ) (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y) := qmap.toAlgebra
  letI algψ : Algebra (Polynomial A ⧸ y.comap φ) Ω₀ := ψbar.toAlgebra
  haveI : Module.IsTorsionFree (Polynomial A ⧸ y.comap φ) (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hqmap
  haveI : Module.IsTorsionFree (Polynomial A ⧸ y.comap φ) Ω₀ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hψbar
  haveI : Algebra.IsIntegral (Polynomial A ⧸ y.comap φ) (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y) := ⟨fun x => (hφint.quotient (I := y)) x⟩
  let φbar : (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y) →ₐ[Polynomial A ⧸ y.comap φ] Ω₀ := IsAlgClosed.lift
  let φ₀ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω₀ := φbar.toRingHom.comp (Ideal.Quotient.mk y)

  have hkerbar : RingHom.ker φbar.toRingHom = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := Polynomial A ⧸ y.comap φ)
    rw [RingHom.comap_ker, show φbar.toRingHom.comp (algebraMap (Polynomial A ⧸ y.comap φ) (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y)) = ψbar from ?_]
    · exact (RingHom.injective_iff_ker_eq_bot _).mp hψbar
    · exact RingHom.ext fun d => φbar.commutes d
  have hker₀ : RingHom.ker φ₀ = y := by
    rw [← RingHom.comap_ker, hkerbar, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

  have hφ₀j : φ₀ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) = j₀ := by
    rw [← hφX]
    show φbar (Ideal.Quotient.mk y (φ Polynomial.X)) = j₀
    have h1 : Ideal.Quotient.mk y (φ Polynomial.X) =
        algebraMap (Polynomial A ⧸ y.comap φ) (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y) (Ideal.Quotient.mk (y.comap φ) Polynomial.X) :=
      (Ideal.quotientMap_mk (I := y) (f := φ) (H := le_rfl)).symm
    rw [h1, AlgHom.commutes]
    show ψbar (Ideal.Quotient.mk (y.comap φ) Polynomial.X) = j₀
    simp [ψbar, ψ]

  have hϖy : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ y := by
    have h1 : φ (Polynomial.C ϖ) = algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ := by
      simp [φ, AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin]
    rw [← h1, ← Ideal.mem_comap, hyc', RingHom.mem_ker]
    have h2 : IsLocalRing.residue A ϖ = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, hϖ]; exact Ideal.mem_span_singleton_self ϖ
    simp [ψ, h2]

  let y' : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j) := ⟨y, hy⟩
  have hz := (germ_mem_maximalIdeal_iff_of_chart (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j)
    (AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase A (↥K) j) y' ϖ).mpr hϖy
  have token := forall_mem_ssJSet_of_exists p (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) y Ω₀ φ₀ hker₀
    (hφ₀j ▸ hj₀)
  exact ⟨y', ModularCurve.XOneP.not_subsingleton_minimalPrimes_span_germ_of_mem_ssJSet_twoChartIntegralModel_x1_mul
    p M hM hpM L ζ hζ K hK A hAp hζA j hj ϖ hϖ _ _ rfl hz y' rfl token⟩

end S_ModularCurve_XOneP_exists_not_subsingleton_minimalPrimes_span_germ_iotaFin_twoChartIntegralModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_not_subsingleton_minimalPrimes_span_germ_iotaFin_twoChartIntegralModel_x1_mul (solution)
