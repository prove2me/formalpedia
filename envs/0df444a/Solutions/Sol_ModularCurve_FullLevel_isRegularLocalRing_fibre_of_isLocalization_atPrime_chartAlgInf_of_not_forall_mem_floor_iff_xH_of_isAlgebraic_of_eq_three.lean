-- Prove2me | solution 1 for ModularCurve.FullLevel.isRegularLocalRing_fibre_of_isLocalization_atPrime_chartAlgInf_of_not_forall_mem_floor_iff_xH_of_isAlgebraic_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/b2c27644-af1f-5932-b7da-4077a3c0a267

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_forall_height_one_isUnramifiedAt_chartAlgInf_xH_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three
import Theorems.Thm_IsRegularLocalRing_of_isRegularLocalRing_quotient_span_singleton_of_mem_nonZeroDivisors
import Theorems.Thm_ModularCurve_FullLevel_smoothOfRelativeDimension_one_toBase_twoChartIntegralModel_laurentBaseChange_gamma0_of_not_dvd
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_gamma0_le_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_coeffEmb_jq_mem_laurentBaseChange_x1FunctionField
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq

import Theorems.Thm_ModularCurve_isMaximal_of_jInvChartInf_mem_of_forall_mem_nonunits_gauss_chartAlgInf

import Theorems.Thm_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_isLocalization_atPrime_chartAlgInf_of_not_forall_mem_floor_iff_xH_of_isAlgebraic_of_eq_three
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso"
p2m_attr_erase "instance" "ModularCurve.DRModelPackage.e₀_iso ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.jqNModC_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul"
p2m_attr_erase "simp" "KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.cuspCount_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply AlgebraicCurve.Pic.baseChange_mk"
p2m_attr_erase "simp" "AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty ModularCurve.coe_jqNGen"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace CuspRegReduce

universe u

theorem exists_ringEquiv_stalk_apply_germ_eq
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (ι : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R S))) (ϖ : R) (q : ↥(Spec (CommRingCat.of S))) :
    ∃ e : X.presheaf.stalk (ι.base q) ≃+* Localization.AtPrime q.asIdeal,
      e ((X.presheaf.germ ⊤ (ι.base q) trivial).hom
        (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))) =
      algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S ϖ) := by
  classical
  let e₁ := (asIso (ι.stalkMap q)).commRingCatIsoToRingEquiv
  let e₂ := (Spec.stalkIso (CommRingCat.of S) q).commRingCatIsoToRingEquiv
  refine ⟨e₁.trans e₂, ?_⟩
  have key₁ : (ι.stalkMap q).hom ((X.presheaf.germ ⊤ (ι.base q) trivial).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))) =
      ((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (algebraMap R S ϖ)) := by
    erw [Scheme.Hom.germ_stalkMap_apply ι ⊤ q trivial]
    congr 1
    show ((f.appTop ≫ ι.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)) = _
    rw [← Scheme.Hom.comp_appTop, hι]
    show ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap R S))).appTop).hom ϖ = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have key₂ : (Spec.stalkIso (CommRingCat.of S) q).hom.hom (((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (algebraMap R S ϖ))) =
      algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S ϖ) := by
    have h0 : CommRingCat.ofHom (algebraMap S (Localization.AtPrime q.asIdeal)) ≫ (Spec.stalkIso (CommRingCat.of S) q).inv =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ (Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial :=
      Spec.algebraMap_stalkIso_inv q
    have h := congrArg (fun φ : CommRingCat.of S ⟶ (Spec (CommRingCat.of S)).presheaf.stalk q =>
      (CommRingCat.Hom.hom φ) (algebraMap R S ϖ)) h0
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    rw [← h, ← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  show e₂ (e₁ _) = _
  show (Spec.stalkIso (CommRingCat.of S) q).hom.hom ((ι.stalkMap q).hom _) = _
  rw [key₁, key₂]

end CuspRegReduce

namespace CROAux

open AlgebraicCurve.TwoChartIntegralModel

scoped instance gammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex := by
  refine @Subgroup.finiteIndex_of_le _ _ (CongruenceSubgroup.Gamma1 M) _ inferInstance ?_
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have h0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma1_in_Gamma0 M hA
  refine ⟨h0, ?_⟩
  have h1 := ((CongruenceSubgroup.Gamma1_mem M A).mp hA).2.1
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h1
  rw [this]; exact H.one_mem

section Incl

variable (L : Type) [Field L] (A : Type) [CommRing A] [Algebra A L]
  (K K₀ : IntermediateField L (LaurentSeries L)) (hle₀ : K₀ ≤ K)
  [Algebra A ↥K] [IsScalarTower A L ↥K] [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]

noncomputable def inclA : ↥K₀ →ₐ[A] ↥K where
  toRingHom := (IntermediateField.inclusion hle₀).toRingHom
  commutes' a := by
    apply Subtype.ext
    change ((algebraMap A ↥K₀ a : ↥K₀) : LaurentSeries L) = ((algebraMap A ↥K a : ↥K) : LaurentSeries L)
    rw [IsScalarTower.algebraMap_apply A L ↥K₀, IsScalarTower.algebraMap_apply A L ↥K]
    rfl

variable (j : ↥K) (j₀ : ↥K₀) (hjj : (j₀ : LaurentSeries L) = (j : LaurentSeries L))

include hjj in
theorem inclA_j₀ : inclA L A K K₀ hle₀ j₀ = j := Subtype.ext hjj

include hjj in

theorem inclA_mem_chartAlgInf (b : ↥(chartAlgInf A ↥K₀ j₀)) : inclA L A K K₀ hle₀ (b : ↥K₀) ∈ chartAlgInf A ↥K j := by
  have hb : IsIntegral ↥(Algebra.adjoin A ({j₀⁻¹} : Set ↥K₀)) (b : ↥K₀) := b.2
  have hle : Algebra.adjoin A ({j₀⁻¹} : Set ↥K₀) ≤ (Algebra.adjoin A ({j⁻¹} : Set ↥K)).comap (inclA L A K K₀ hle₀) := by
    refine Algebra.adjoin_le ?_
    intro t ht
    rw [Set.mem_singleton_iff.mp ht]
    change j₀⁻¹ ∈ (Algebra.adjoin A ({j⁻¹} : Set ↥K)).comap (inclA L A K K₀ hle₀)
    rw [Subalgebra.mem_comap, map_inv₀, inclA_j₀ L A K K₀ hle₀ j j₀ hjj]
    exact Algebra.self_mem_adjoin_singleton A j⁻¹
  have hmap : ∀ x : ↥(Algebra.adjoin A ({j₀⁻¹} : Set ↥K₀)), inclA L A K K₀ hle₀ (x : ↥K₀) ∈ Algebra.adjoin A ({j⁻¹} : Set ↥K) :=
    fun x => (Subalgebra.mem_comap ..).1 (hle x.2)
  let ψ : ↥(Algebra.adjoin A ({j₀⁻¹} : Set ↥K₀)) →+* ↥(Algebra.adjoin A ({j⁻¹} : Set ↥K)) :=
    ((inclA L A K K₀ hle₀).toRingHom.comp (Algebra.adjoin A ({j₀⁻¹} : Set ↥K₀)).val.toRingHom).codRestrict
      (Algebra.adjoin A ({j⁻¹} : Set ↥K)) (fun x => hmap x)
  exact hb.map_of_comp_eq ψ (inclA L A K K₀ hle₀).toRingHom (by ext x; rfl)

noncomputable def iotaInf : ↥(chartAlgInf A ↥K₀ j₀) →+* ↥(chartAlgInf A ↥K j) :=
  ((inclA L A K K₀ hle₀).toRingHom.comp (chartAlgInf A ↥K₀ j₀).val.toRingHom).codRestrict (chartAlgInf A ↥K j)
    (fun b => inclA_mem_chartAlgInf L A K K₀ hle₀ j j₀ hjj b)

theorem coe_iotaInf_apply (b : ↥(chartAlgInf A ↥K₀ j₀)) :
    ((iotaInf L A K K₀ hle₀ j j₀ hjj b : ↥(chartAlgInf A ↥K j)) : ↥K) = IntermediateField.inclusion hle₀ (b : ↥K₀) := rfl

end Incl

theorem coeffEmb_jq_mem_gamma0 (L : Type) [Field L] [CharZero L] (M' : ℕ) :
    ModularCurve.coeffEmb L ModularCurve.jq ∈
      ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) := by
  have h1 := ModularCurve.coeffEmb_jq_mem_laurentBaseChange_x1FunctionField L 1
  have hΓ : CongruenceSubgroup.Gamma0 M' ≤ CongruenceSubgroup.Gamma1 1 := by
    intro γ _
    rw [CongruenceSubgroup.Gamma1_mem]
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hle : ModularCurve.x1FunctionField 1 ≤ ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M') :=
    ModularCurve.qExpFunctionFieldC_mono ℚ hΓ
  have hsub : (⇑(ModularCurve.coeffEmb L) '' (ModularCurve.x1FunctionField 1 : Set (LaurentSeries ℚ))) ⊆
      (⇑(ModularCurve.coeffEmb L) '' (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M') : Set (LaurentSeries ℚ))) :=
    Set.image_mono (fun x hx => hle hx)
  exact IntermediateField.adjoin.mono L _ _ hsub h1

end CROAux
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_isLocalization_atPrime_chartAlgInf_of_not_forall_mem_floor_iff_xH_of_isAlgebraic_of_eq_three.CROAux"

set_option maxHeartbeats 0 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))

    [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L))) :

    ∀ (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [y.IsPrime],
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ ∈ y →
      AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K) j ∈ y →
      (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y) →
      ¬ (∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), ((b : ↥K) : LaurentSeries L) ∈ ModularCurve.laurentBaseChange L (ModularCurve.modularFunctionFieldFull (q ^ 2 * M')) →
          (b ∈ y ↔ ∃ c ∈ IsLocalRing.maximalIdeal A, ((b : ↥K) : LaurentSeries L).coeff 0 = algebraMap A L c)) →
      ∀ (Bm : Type) [CommRing Bm] [Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm] [IsLocalization.AtPrime Bm y],
        IsRegularLocalRing Bm ∧
        IsRegularLocalRing (Bm ⧸ Ideal.span {algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ)}) := by
  classical
  intro y hyP hϖy hjy hWy hother Bm _ _ _

  have hmax : y.IsMaximal := by
    have hK' : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) := by
      rw [hK]; rfl
    exact ModularCurve.isMaximal_of_jInvChartInf_mem_of_forall_mem_nonunits_gauss_chartAlgInf
      (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) L K hK' A j hj ϖ hϖ W₀ hW₀ y hϖy hjy hWy

  let yP : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf A (↥K) j) := ⟨y, hyP⟩
  obtain ⟨e, he⟩ := CuspRegReduce.exists_ringEquiv_stalk_apply_germ_eq
    (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.ιInf A (↥K) j)
    (AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase A (↥K) j) ϖ yP
  set ϖz := ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ ((AlgebraicCurve.TwoChartIntegralModel.ιInf A (↥K) j).base yP) trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)) with hϖz
  have hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.ιInf A (↥K) j).base yP)) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' := hu.map e
    rw [he] at hu'
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime yP.asIdeal) yP.asIdeal
      (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ)).mp hu' hϖy

  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : IntermediateField L (LaurentSeries L),
      K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) := ⟨_, rfl⟩
  have hle₀ : K₀ ≤ K := by
    rw [hK, hK₀]
    exact ModularCurve.laurentBaseChange_qExpFunctionFieldC_gamma0_le_laurentBaseChange_xHFunctionField L M' (q ^ 2 * M')
      (dvd_mul_left M' (q ^ 2)) (ModularCurve.FullLevel.levelH q M')
  letI algAK₀ : Algebra A ↥K₀ := ((algebraMap L ↥K₀).comp (algebraMap A L)).toAlgebra
  haveI istAK₀ : IsScalarTower A L ↥K₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨j₀, hj₀⟩ : ∃ j₀ : ↥K₀, ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq :=
    ⟨⟨ModularCurve.coeffEmb L ModularCurve.jq, by rw [hK₀]; exact CROAux.coeffEmb_jq_mem_gamma0 L M'⟩, rfl⟩
  have hjj : (j₀ : LaurentSeries L) = (j : LaurentSeries L) := hj₀.trans hj.symm
  haveI hj₀0 : Fact (j₀ ≠ 0) := ⟨fun h => (Fact.out : j ≠ 0) (by
    apply Subtype.ext
    change (j : LaurentSeries L) = ((0 : ↥K) : LaurentSeries L)
    rw [← hjj, h]
    rfl)⟩
  obtain ⟨ι, hιb⟩ : ∃ ι : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j),
      ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀), ((ι b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) : ↥K) = IntermediateField.inclusion hle₀ (b : ↥K₀) :=
    ⟨CROAux.iotaInf L A K K₀ hle₀ j j₀ hjj, fun b => rfl⟩

  have hfloor : Smooth (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₀) j₀) := by
    haveI := ModularCurve.FullLevel.smoothOfRelativeDimension_one_toBase_twoChartIntegralModel_laurentBaseChange_gamma0_of_not_dvd
      q M' hqM' L K₀ hK₀ A hAq j₀ hj₀
    exact SmoothOfRelativeDimension.smooth (n := 1) (f := AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K₀) j₀)

  have hV := ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three
    q hq3 M' hqM' L ζ hζ hι K hK A hAq hζA j hj ϖ hϖ W₀ hW₀ _ ϖz hϖz hz yP rfl hmax hjy hWy K₀ hK₀ hle₀ j₀ hj₀ ι hιb

  letI algι : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) := ι.toAlgebra
  have hH := ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three
    q hq3 M' hqM' L ζ hζ hι K hK A hAq hζA j hj ϖ hϖ W₀ hW₀ _ ϖz hϖz hz yP rfl hmax hjy hWy K₀ hK₀ hle₀ j₀ hj₀ ι hιb

  have hreg := ModularCurve.FullLevel.isRegularLocalRing_fibre_of_forall_height_one_isUnramifiedAt_chartAlgInf_xH_of_eq_three
    q hq3 M' hqM' L ζ hζ hι K hK A hAq hζA j hj ϖ hϖ W₀ hW₀ _ ϖz hϖz hz yP rfl hmax hWy K₀ hK₀ hle₀ j₀ hj₀ ι hιb hfloor
    (fun 𝔔 _ h𝔔y h1 => by
      by_cases hϖ𝔔 : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ ∈ 𝔔
      · exact hV 𝔔 h𝔔y h1 hϖ𝔔
      · exact hH 𝔔 h𝔔y h1 hϖ𝔔)

  haveI := hreg
  let eB : Localization.AtPrime yP.asIdeal ≃ₐ[↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)] Bm := IsLocalization.algEquiv yP.asIdeal.primeCompl _ _
  let eT := e.trans eB.toRingEquiv
  have heT : eT ϖz = algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ) := by
    show eB (e ϖz) = _
    rw [he]
    exact eB.commutes _
  have hfib : IsRegularLocalRing (Bm ⧸ Ideal.span {algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ)}) := by
    let eq := Ideal.quotientEquiv (Ideal.span {ϖz}) (Ideal.span {algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ)}) eT
      (by rw [Ideal.map_span, Set.image_singleton]; congr 1; rw [← heT]; rfl)
    exact @IsRegularLocalRing.of_ringEquiv _ _ hreg _ _ eq

  haveI hloc : IsLocalRing Bm := IsLocalization.AtPrime.isLocalRing Bm y
  haveI hnoethB : IsNoetherianRing ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) := by
    have hT : ModularGroup.T ∈ CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :=
      ModularCurve.translation_mem_GammaH _ _
    haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
      ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
        (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) hT L K hK j hj
    haveI hAlg : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsAlgebraic.of_finite _ _
    haveI hsepK : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
    haveI hFT : Algebra.FiniteType A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) :=
      (AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsepK).2
    exact Algebra.FiniteType.isNoetherianRing A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)
  haveI hnoeth : IsNoetherianRing Bm := IsLocalization.isNoetherianRing y.primeCompl Bm hnoethB
  have hϖm : algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ) ∈ IsLocalRing.maximalIdeal Bm := by
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Bm y _).mpr hϖy
  have hnzd : algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm (algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ) ∈ nonZeroDivisors Bm := by
    have hq0 : (q : A) ≠ 0 := by
      intro h
      have : (q : L) = 0 := by rw [← map_natCast (algebraMap A L), h, map_zero]
      exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this
    have hϖ0 : ϖ ≠ 0 := by
      intro h
      have hq' : (q : A) ∈ Ideal.span {ϖ} := hϖ ▸ hAq
      rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at hq'
      exact hq0 ((Submodule.mem_bot A).mp hq')
    have hne : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ ≠ 0 := by
      intro h0
      have h1 : ((algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) : ↥K) = algebraMap A ↥K ϖ := rfl
      rw [h0] at h1
      have h2 : algebraMap A ↥K ϖ = 0 := h1.symm
      rw [IsScalarTower.algebraMap_apply A L ↥K, map_eq_zero] at h2
      exact hϖ0 (IsFractionRing.injective A L (h2.trans (map_zero _).symm))
    have hle : y.primeCompl ≤ nonZeroDivisors ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) := Ideal.primeCompl_le_nonZeroDivisors y
    have hinj : Function.Injective (algebraMap ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) Bm) := IsLocalization.injective Bm hle
    haveI : IsDomain Bm := IsLocalization.isDomain_of_le_nonZeroDivisors (S := Bm) hle
    exact mem_nonZeroDivisors_of_ne_zero (fun h0 => hne (hinj (h0.trans (map_zero _).symm)))
  exact ⟨(IsRegularLocalRing.of_isRegularLocalRing_quotient_span_singleton_of_mem_nonZeroDivisors _ hϖm hnzd hfib).1, hfib⟩

end S_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_isLocalization_atPrime_chartAlgInf_of_not_forall_mem_floor_iff_xH_of_isAlgebraic_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_isLocalization_atPrime_chartAlgInf_of_not_forall_mem_floor_iff_xH_of_isAlgebraic_of_eq_three (solution)
