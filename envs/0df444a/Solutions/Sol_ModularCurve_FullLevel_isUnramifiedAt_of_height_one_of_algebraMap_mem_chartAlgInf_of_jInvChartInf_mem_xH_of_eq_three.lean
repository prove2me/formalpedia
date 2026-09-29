-- Prove2me | solution 1 for ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/df3e0167-3ddf-50aa-acad-d90cda9b6b87

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_Algebra_isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one
import Theorems.Thm_IsIntegrallyClosed_exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one
import Theorems.Thm_IsIntegrallyClosed_exists_valuationSubring_mem_iff_of_height_eq_one
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_exists_eq_mul_of_mem_nonunits_of_forall_mem_iff_gaussPresentation
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_gamma0_le_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_valuationSubring_unique_laurentBaseChange_gamma0_of_not_dvd
import Theorems.Thm_ModularCurve_FullLevel_forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_jInvChartInf_mem_xH_of_isAlgebraic_of_eq_three
import Theorems.Thm_ModularCurve_FullLevel_exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH_of_eq_three
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso"
p2m_attr_erase "instance" "ModularCurve.DRModelPackage.e₀_iso ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun"
p2m_attr_erase "simp" "KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.cuspCount_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

open AlgebraicCurve.TwoChartIntegralModel

theorem E149V.mem_nonunits_comap_iff {F F' : Type*} [Field F] [Field F'] (O : ValuationSubring F)
    (τ : F' →+* F) (x : F') : x ∈ (O.comap τ).nonunits ↔ τ x ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero]

theorem E149V.mem_valuationSubring_iff_of_under
    {O C : Type*} [CommRing O] [CommRing C] [Algebra O C]
    {K₂ K₁ : Type*} [Field K₂] [Field K₁] [Algebra O K₂] [Algebra C K₁]
    (ι₂ : K₂ →+* K₁) (hι₂ : ∀ o : O, ι₂ (algebraMap O K₂ o) = algebraMap C K₁ (algebraMap O C o))
    (Q : Ideal C) [Q.IsPrime]
    (V : ValuationSubring K₁)
    (hCV : ∀ c : C, algebraMap C K₁ c ∈ V)
    (hcen : ∀ c : C, algebraMap C K₁ c ∈ V.nonunits ↔ c ∈ Q)
    (V₂ : ValuationSubring K₂) (hPIR : IsPrincipalIdealRing ↥V₂)
    (hV₂mem : ∀ x : K₂, x ∈ V₂ ↔ ∃ c s : O, s ∉ Q.under O ∧ x * algebraMap O K₂ s = algebraMap O K₂ c)
    (t : O) (ht : t ∈ Q.under O) (ht0 : algebraMap O K₂ t ≠ 0) :
    ∀ y : K₂, y ∈ V₂ ↔ ι₂ y ∈ V := by
  classical

  have hunit : ∀ s : O, s ∉ Q.under O → algebraMap C K₁ (algebraMap O C s) ∉ V.nonunits :=
    fun s hs h => hs (Ideal.mem_comap.mpr ((hcen _).mp h))
  have hne : ∀ s : O, s ∉ Q.under O → algebraMap O K₂ s ≠ 0 := fun s hs h0 =>
    hunit s hs (by rw [← hι₂, h0, map_zero]; exact V.nonunits.zero_mem)
  have hfwd : ∀ y : K₂, y ∈ V₂ → ι₂ y ∈ V := by
    intro y hy
    obtain ⟨c, s, hs, hcs⟩ := (hV₂mem y).mp hy
    have hs0 : ι₂ (algebraMap O K₂ s) ≠ 0 := (map_ne_zero ι₂).mpr (hne s hs)
    have hinv : (ι₂ (algebraMap O K₂ s))⁻¹ ∈ V := by
      have h := hunit s hs
      rw [← hι₂, ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at h
      exact h.2
    have : ι₂ y = ι₂ (algebraMap O K₂ c) * (ι₂ (algebraMap O K₂ s))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hs0, ← map_mul, hcs]
    rw [this]
    exact V.mul_mem _ _ (by rw [hι₂]; exact hCV _) hinv
  intro y
  refine ⟨hfwd y, fun hy => ?_⟩

  haveI : IsPrincipalIdealRing ↥V₂ := hPIR
  have hle : V₂ ≤ V.comap ι₂ := fun x hx => ValuationSubring.mem_comap.mpr (hfwd x hx)
  have hnt : V.comap ι₂ ≠ ⊤ := by
    intro htop
    have hmem : (algebraMap O K₂ t)⁻¹ ∈ V.comap ι₂ := htop ▸ ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap, map_inv₀, hι₂] at hmem
    have hnu : algebraMap C K₁ (algebraMap O C t) ∈ V.nonunits := (hcen _).mpr (Ideal.mem_comap.mp ht)
    rw [ValuationSubring.mem_nonunits_iff_or] at hnu
    rcases hnu with h0 | hni
    · apply ht0
      rw [← hι₂] at h0
      exact (map_eq_zero ι₂).mp h0
    · exact hni hmem
  have heq : V₂ = V.comap ι₂ := V₂.eq_of_le_of_ne_top hle hnt
  rw [heq, ValuationSubring.mem_comap]
  exact hy

theorem E149V.isSeparable_residueField_of_under
    {O C : Type*} [CommRing O] [CommRing C] [Algebra O C]
    {K₂ K₁ : Type*} [Field K₂] [Field K₁] [Algebra O K₂] [Algebra C K₁]
    (ι₂ : K₂ →+* K₁) (hι₂ : ∀ o : O, ι₂ (algebraMap O K₂ o) = algebraMap C K₁ (algebraMap O C o))
    (Q : Ideal C) [Q.IsPrime]
    [Algebra (Localization.AtPrime (Q.under O)) (Localization.AtPrime Q)]
    [Localization.AtPrime.IsLiesOverAlgebra (Q.under O) Q]
    (V : ValuationSubring K₁)
    (hCV : ∀ c : C, algebraMap C K₁ c ∈ V)
    (ιV : IsLocalRing.ResidueField ↥V ≃+* Q.ResidueField)
    (hιV : ∀ (c : C) (hc : algebraMap C K₁ c ∈ V),
      ιV (IsLocalRing.residue ↥V ⟨algebraMap C K₁ c, hc⟩) = algebraMap C Q.ResidueField c)
    (V₂ : ValuationSubring K₂)
    (hV₂mem : ∀ x : K₂, x ∈ V₂ ↔ ∃ c s : O, s ∉ Q.under O ∧ x * algebraMap O K₂ s = algebraMap O K₂ c)
    (ιV₂ : IsLocalRing.ResidueField ↥V₂ ≃+* (Q.under O).ResidueField)
    (hιV₂ : ∀ (c : O) (hc : algebraMap O K₂ c ∈ V₂),
      ιV₂ (IsLocalRing.residue ↥V₂ ⟨algebraMap O K₂ c, hc⟩) = algebraMap O (Q.under O).ResidueField c)
    [Algebra ↥V₂ ↥V] (halg : ∀ y : ↥V₂, ((algebraMap ↥V₂ ↥V y : ↥V) : K₁) = ι₂ (y : K₂))
    [IsLocalHom (algebraMap ↥V₂ ↥V)]
    [Algebra.IsSeparable (IsLocalRing.ResidueField ↥V₂) (IsLocalRing.ResidueField ↥V)] :
    Algebra.IsSeparable (Q.under O).ResidueField Q.ResidueField := by
  classical
  refine Algebra.IsSeparable.of_equiv_equiv ιV₂ ιV ?_

  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun y => ?_
  obtain ⟨c, s, hs, hcs⟩ := (hV₂mem y).mp y.2
  have h1 : (1 : O) ∉ Q.under O := fun h => (inferInstance : (Q.under O).IsPrime).ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hcV₂ : algebraMap O K₂ c ∈ V₂ := (hV₂mem _).mpr ⟨c, 1, h1, by simp⟩
  have hsV₂ : algebraMap O K₂ s ∈ V₂ := (hV₂mem _).mpr ⟨s, 1, h1, by simp⟩

  set F : IsLocalRing.ResidueField ↥V₂ →+* Q.ResidueField :=
    (algebraMap (Q.under O).ResidueField Q.ResidueField).comp (ιV₂ : IsLocalRing.ResidueField ↥V₂ →+* (Q.under O).ResidueField) with hF
  set G : IsLocalRing.ResidueField ↥V₂ →+* Q.ResidueField :=
    (ιV : IsLocalRing.ResidueField ↥V →+* Q.ResidueField).comp (algebraMap (IsLocalRing.ResidueField ↥V₂) (IsLocalRing.ResidueField ↥V)) with hG

  have hFO : ∀ (o : O) (ho : algebraMap O K₂ o ∈ V₂), F (IsLocalRing.residue ↥V₂ ⟨_, ho⟩) = algebraMap C Q.ResidueField (algebraMap O C o) := by
    intro o ho
    rw [hF, RingHom.comp_apply, RingHom.coe_coe, hιV₂ o ho, ← IsScalarTower.algebraMap_apply O (Q.under O).ResidueField Q.ResidueField,
      IsScalarTower.algebraMap_apply O C Q.ResidueField]
  have hGO : ∀ (o : O) (ho : algebraMap O K₂ o ∈ V₂), G (IsLocalRing.residue ↥V₂ ⟨_, ho⟩) = algebraMap C Q.ResidueField (algebraMap O C o) := by
    intro o ho
    rw [hG, RingHom.comp_apply, IsLocalRing.ResidueField.algebraMap_residue, RingHom.coe_coe]
    have h2 : (algebraMap ↥V₂ ↥V ⟨algebraMap O K₂ o, ho⟩ : ↥V) = ⟨algebraMap C K₁ (algebraMap O C o), hCV _⟩ :=
      Subtype.ext (by rw [halg]; exact hι₂ o)
    rw [h2, hιV]

  have hys : (y * ⟨algebraMap O K₂ s, hsV₂⟩ : ↥V₂) = ⟨algebraMap O K₂ c, hcV₂⟩ := Subtype.ext hcs
  have hs0 : algebraMap C Q.ResidueField (algebraMap O C s) ≠ 0 := fun h0 =>
    hs (Ideal.mem_comap.mpr (Ideal.algebraMap_residueField_eq_zero.mp h0))
  show F (Ideal.Quotient.mk _ y) = G (Ideal.Quotient.mk _ y)
  have key : F (IsLocalRing.residue ↥V₂ y) * algebraMap C Q.ResidueField (algebraMap O C s) =
      G (IsLocalRing.residue ↥V₂ y) * algebraMap C Q.ResidueField (algebraMap O C s) := by
    conv_lhs => rw [← hFO s hsV₂, ← map_mul, ← map_mul, hys, hFO c hcV₂]
    conv_rhs => rw [← hGO s hsV₂, ← map_mul, ← map_mul, hys, hGO c hcV₂]
  exact mul_right_cancel₀ hs0 key

theorem E149V.gauss_of_gauss_inv {A K : Type*} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]
    (V : ValuationSubring K) (x : K) (hx : x ≠ 0)
    (h : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval x⁻¹ P ∈ V ∧ (Polynomial.aeval x⁻¹ P)⁻¹ ∈ V) :
    ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval x P ∈ V ∧ (Polynomial.aeval x P)⁻¹ ∈ V := by
  classical
  have hX : (Polynomial.X : Polynomial A).map (IsLocalRing.residue A) ≠ 0 := by
    rw [Polynomial.map_X]; exact Polynomial.X_ne_zero
  obtain ⟨hxinv, hxV⟩ := h Polynomial.X hX
  rw [Polynomial.aeval_X] at hxinv hxV
  rw [inv_inv] at hxV
  intro P hP
  have hrev : P.reverse.map (IsLocalRing.residue A) ≠ 0 := by
    intro h0
    apply hP
    ext i
    have := congrArg (fun Q => Polynomial.coeff Q (Polynomial.revAt P.natDegree i)) h0
    simp only [Polynomial.coeff_map, Polynomial.coeff_reverse, Polynomial.revAt_invol, Polynomial.coeff_zero] at this
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact this
  obtain ⟨h1, h2⟩ := h P.reverse hrev
  letI : Invertible x := invertibleOfNonzero hx
  have key : Polynomial.aeval x P = Polynomial.aeval x⁻¹ P.reverse * x ^ P.natDegree := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, ← invOf_eq_inv x, Polynomial.eval₂_reverse_mul_pow]
  refine ⟨?_, ?_⟩
  · rw [key]; exact V.mul_mem _ _ h1 (pow_mem hxV _)
  · rw [key, mul_inv, ← inv_pow]; exact V.mul_mem _ _ h2 (pow_mem hxinv _)

namespace E149Aux

open scoped MatrixGroups

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

end E149Aux
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three.E149Aux"

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in

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
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιInf A (↥K) j).base y = z)
    (hmax : y.asIdeal.IsMaximal)

    (hcusp : AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K) j ∈ y.asIdeal)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal)

    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle₀ : K₀ ≤ K)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ι : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j))
    (hι : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀), ((ι b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) : ↥K) = IntermediateField.inclusion hle₀ (b : ↥K₀)) :
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) := ι.toAlgebra
    ∀ (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [𝔔.IsPrime], 𝔔 ≤ y.asIdeal → 𝔔.height = 1 →
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ ∈ 𝔔 → Algebra.IsUnramifiedAt ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀) 𝔔 := by
  intro Q _inst hQy hQ1 hϖQ
  classical
  have hιC : ∃ ι' : L →+* ℂ, ι' ζ = Complex.exp (2 * Real.pi * Complex.I / q) := by assumption
  letI algBB : Algebra ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) := ι.toAlgebra
  set φK : ↥K₀ →ₐ[L] ↥K := IntermediateField.inclusion hle₀ with hφKdef

  haveI : IsIntegrallyClosed ↥(chartAlgInf A (↥K) j) := isIntegrallyClosed_chartAlg A (↥K) _
  haveI : IsIntegrallyClosed ↥(chartAlgInf A (↥K₀) j₀) := isIntegrallyClosed_chartAlg A (↥K₀) _

  have hT : ModularGroup.T ∈ CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :=
    ModularCurve.translation_mem_GammaH _ _
  have hT₀ : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M' := by
    rw [← CohCarrier.GammaH_top]; exact ModularCurve.translation_mem_GammaH _ _
  haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) hT L K hK j hj
  haveI hFD₀ : FiniteDimensional ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma0 M') hT₀ L K₀ hK₀ j₀ hj₀
  haveI hAlg : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsAlgebraic.of_finite _ _
  haveI hAlg₀ : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ := Algebra.IsAlgebraic.of_finite _ _
  haveI hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hsep₀ : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have htj₀ : Transcendental A j₀ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₀ A j₀ hj₀

  have hadj : IntermediateField.adjoin L ({j⁻¹} : Set ↥K) = IntermediateField.adjoin L ({j} : Set ↥K) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self L j)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h := IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self L (j⁻¹ : ↥K))
      rwa [inv_inv] at h
  have hadj₀ : IntermediateField.adjoin L ({j₀⁻¹} : Set ↥K₀) = IntermediateField.adjoin L ({j₀} : Set ↥K₀) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self L j₀)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have h := IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self L (j₀⁻¹ : ↥K₀))
      rwa [inv_inv] at h
  haveI hAlginv : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j⁻¹} : Set ↥K)) ↥K := by rw [hadj]; exact hAlg
  haveI hAlg₀inv : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j₀⁻¹} : Set ↥K₀)) ↥K₀ := by rw [hadj₀]; exact hAlg₀
  have hFDinv : FiniteDimensional ↥(IntermediateField.adjoin L ({j⁻¹} : Set ↥K)) ↥K := by rw [hadj]; exact hFD
  have hsepinv : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j⁻¹} : Set ↥K)) ↥K := by rw [hadj]; exact hsep
  have htjinv : Transcendental A j⁻¹ := fun h => htj (IsAlgebraic.inv_iff.mp h)
  haveI : Fact (j⁻¹ ≠ 0) := ⟨inv_ne_zero (Fact.out : j ≠ 0)⟩
  haveI : IsFractionRing ↥(chartAlgInf A (↥K) j) ↥K := isFractionRing_chartAlg A L (↥K) _
  haveI : IsFractionRing ↥(chartAlgInf A (↥K₀) j₀) ↥K₀ := isFractionRing_chartAlg A L (↥K₀) _
  haveI : IsNoetherianRing ↥(chartAlgInf A (↥K₀) j₀) := by
    haveI := (finiteType_chartAlgFin_and_chartAlgInf A L (↥K₀) j₀ htj₀ hFD₀ hsep₀).2
    exact Algebra.FiniteType.isNoetherianRing A _

  have hιj : ι (jInvChartInf A (↥K₀) j₀) = jInvChartInf A (↥K) j := by
    apply Subtype.ext
    rw [hι]
    apply Subtype.ext
    show ((jInvChartInf A (↥K₀) j₀ : ↥K₀) : LaurentSeries L) = ((jInvChartInf A (↥K) j : ↥K) : LaurentSeries L)
    rw [coe_jInvChartInf, coe_jInvChartInf, IntermediateField.coe_inv, IntermediateField.coe_inv, hj₀, hj]
  haveI : IsScalarTower A ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    symm
    apply Subtype.ext
    show ((ι (algebraMap A ↥(chartAlgInf A (↥K₀) j₀) a) : ↥(chartAlgInf A (↥K) j)) : ↥K) = (algebraMap A ↥(chartAlgInf A (↥K) j) a : ↥K)
    rw [hι]
    apply Subtype.ext
    show ((algebraMap A ↥K₀ a : ↥K₀) : LaurentSeries L) = ((algebraMap A ↥K a : ↥K) : LaurentSeries L)
    rw [IsScalarTower.algebraMap_apply A L ↥K₀, IsScalarTower.algebraMap_apply A L ↥K]
    rfl
  haveI : Module.Finite ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) := by
    letI algP : Algebra (Polynomial A) ↥(chartAlgInf A (↥K) j) := (polynomialToChartInf A (↥K) j).toRingHom.toAlgebra
    letI algP₀ : Algebra (Polynomial A) ↥(chartAlgInf A (↥K₀) j₀) := (polynomialToChartInf A (↥K₀) j₀).toRingHom.toAlgebra
    haveI hfinP : Module.Finite (Polynomial A) ↥(chartAlgInf A (↥K) j) :=
      (finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep).2
    have hcomp : ι.comp (polynomialToChartInf A (↥K₀) j₀).toRingHom = (polynomialToChartInf A (↥K) j).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        show ι (polynomialToChartInf A (↥K₀) j₀ (Polynomial.C a)) = polynomialToChartInf A (↥K) j (Polynomial.C a)
        rw [Polynomial.C_eq_algebraMap, AlgHom.commutes, AlgHom.commutes]
        exact (IsScalarTower.algebraMap_apply A ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) a).symm
      · show ι (polynomialToChartInf A (↥K₀) j₀ Polynomial.X) = polynomialToChartInf A (↥K) j Polynomial.X
        rw [polynomialToChartInf_X, polynomialToChartInf_X, hιj]
    haveI : IsScalarTower (Polynomial A) ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) := by
      apply IsScalarTower.of_algebraMap_eq
      intro p
      show polynomialToChartInf A (↥K) j p = ι (polynomialToChartInf A (↥K₀) j₀ p)
      exact (congrArg (fun g : Polynomial A →+* ↥(chartAlgInf A (↥K) j) => g p) hcomp).symm
    exact Module.Finite.of_restrictScalars_finite (Polynomial A) _ _
  haveI : IsNoetherianRing ↥(chartAlgInf A (↥K) j) := by
    haveI := (finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep).2
    exact Algebra.FiniteType.isNoetherianRing A _
  have halg : ∀ x, algebraMap ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) x = ι x := fun _ => rfl
  have hinj : Function.Injective (algebraMap ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j)) := by
    intro a b h
    rw [halg, halg] at h
    have h' : IntermediateField.inclusion hle₀ (a : ↥K₀) = IntermediateField.inclusion hle₀ (b : ↥K₀) := by
      rw [← hι a, ← hι b, h]
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥K => (z : LaurentSeries L)) h'
  haveI : NoZeroSMulDivisors ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) := ⟨fun {c x} h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun hc => hinj (by rw [map_zero]; exact hc)⟩

  have hϖirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hϖprime : Prime ϖ := hϖirr.prime
  have hAB : Function.Injective (algebraMap A ↥(chartAlgInf A (↥K) j)) := by
    intro a b h
    have h' := congrArg (algebraMap ↥(chartAlgInf A (↥K) j) ↥K) h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A L ↥K, IsScalarTower.algebraMap_apply A L ↥K] at h'
    exact IsFractionRing.injective A L ((algebraMap L ↥K).injective h')
  have hϖB0 : algebraMap A ↥(chartAlgInf A (↥K) j) ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hAB]
    exact hϖprime.ne_zero
  have htϖ : algebraMap ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) (algebraMap A ↥(chartAlgInf A (↥K₀) j₀) ϖ) = algebraMap A ↥(chartAlgInf A (↥K) j) ϖ :=
    (IsScalarTower.algebraMap_apply A ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) ϖ).symm
  have hϖ₂ : algebraMap A ↥(chartAlgInf A (↥K₀) j₀) ϖ ∈ Q.under ↥(chartAlgInf A (↥K₀) j₀) := by
    rw [Ideal.under_def, Ideal.mem_comap, htϖ]
    exact hϖQ
  have hϖK₀ : algebraMap ↥(chartAlgInf A (↥K₀) j₀) ↥K₀ (algebraMap A ↥(chartAlgInf A (↥K₀) j₀) ϖ) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective ↥(chartAlgInf A (↥K₀) j₀) ↥K₀)]
    intro h
    apply hϖB0
    rw [← htϖ, h, map_zero]
  have hι₂O : ∀ o : ↥(chartAlgInf A (↥K₀) j₀), (IntermediateField.inclusion hle₀).toRingHom (algebraMap ↥(chartAlgInf A (↥K₀) j₀) ↥K₀ o) =
      algebraMap ↥(chartAlgInf A (↥K) j) ↥K (algebraMap ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) o) := by
    intro o
    rw [halg]
    exact (hι o).symm

  have hQmin : Q ∈ (Ideal.span {algebraMap A ↥(chartAlgInf A (↥K) j) ϖ}).minimalPrimes := by
    refine ⟨⟨‹Q.IsPrime›, (Ideal.span_singleton_le_iff_mem _).mpr hϖQ⟩, ?_⟩
    rintro P ⟨hP, hϖP⟩ hPQ
    by_contra hne
    have hlt : P < Q := lt_of_le_of_ne hPQ (fun h => hne (h ▸ le_rfl))
    haveI := hP
    have hP0 : P ≠ ⊥ := fun h => hϖB0 (by
      have := (Ideal.span_singleton_le_iff_mem _).mp hϖP
      simpa [h] using this)
    have hPne : P.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff]
      exact hP0
    have h1 : Q.height ≤ ((1 : ℕ) : ℕ∞) := by rw [hQ1]; exact_mod_cast le_rfl
    have hlt' := (Ideal.height_le_iff.mp h1) P hP hlt
    exact hPne (ENat.lt_one_iff_eq_zero.mp (by exact_mod_cast hlt'))

  obtain ⟨V', -, -, hcen', -, hVj'⟩ :=
    AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin A L ↥K j⁻¹ htjinv hFDinv hsepinv
      ϖ hϖprime Q hQmin
  have hcoe : ∀ P : Polynomial A, ((Polynomial.aeval (jInvChartInf A (↥K) j) P : ↥(chartAlgInf A (↥K) j)) : ↥K) = Polynomial.aeval j⁻¹ P := by
    intro P
    exact (Polynomial.aeval_algHom_apply (chartAlgInf A (↥K) j).val (jInvChartInf A (↥K) j) P).symm
  have hgauss : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      ∃ b : ↥(chartAlgInf A (↥K) j), algebraMap ↥(chartAlgInf A (↥K) j) ↥K b = Polynomial.aeval j⁻¹ P ∧ b ∉ Q := by
    intro P hP
    have hndvd : ¬ (Polynomial.C ϖ ∣ P) := by
      intro hdvd
      apply hP
      obtain ⟨R, rfl⟩ := hdvd
      rw [Polynomial.map_mul, Polynomial.map_C]
      have : IsLocalRing.residue A ϖ = 0 := (IsLocalRing.residue_eq_zero_iff ϖ).mpr (by
        rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ)
      rw [this, Polynomial.C_0, zero_mul]
    refine ⟨Polynomial.aeval (jInvChartInf A (↥K) j) P, hcoe P, fun hmem => ?_⟩
    obtain ⟨-, hinv⟩ := hVj' P hndvd
    have hnu : ((Polynomial.aeval (jInvChartInf A (↥K) j) P : ↥(chartAlgInf A (↥K) j)) : ↥K) ∈ V'.nonunits := (hcen' _).mp hmem
    rw [hcoe] at hnu
    have hP0 : P ≠ 0 := fun h => hndvd (h ▸ dvd_zero _)
    have hx0 : Polynomial.aeval j⁻¹ P ≠ 0 := fun h => hP0 ((transcendental_iff_injective.mp htjinv) (by rw [h, map_zero]))
    have hlt := (ValuationSubring.mem_nonunits_iff _).mp hnu
    have hle' := (V'.valuation_le_one_iff _).mpr hinv
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0))] at hle'
    exact absurd hlt (not_lt.mpr hle')

  letI locAlg : Algebra (Localization.AtPrime (Q.under ↥(chartAlgInf A (↥K₀) j₀))) (Localization.AtPrime Q) :=
    (Localization.localRingHom (Q.under ↥(chartAlgInf A (↥K₀) j₀)) Q (algebraMap ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j)) Ideal.LiesOver.over).toAlgebra
  haveI : Localization.AtPrime.IsLiesOverAlgebra (Q.under ↥(chartAlgInf A (↥K₀) j₀)) Q := ⟨rfl⟩
  obtain ⟨hQ₂1, -, -, hiff⟩ :=
    Algebra.isUnramifiedAt_iff_map_maximalIdeal_eq_and_isSeparable_of_height_eq_one (O := ↥(chartAlgInf A (↥K₀) j₀)) (C := ↥(chartAlgInf A (↥K) j)) Q hQ1

  obtain ⟨V, -, hCV, hcen, hramiff, ιV, hιV⟩ :=
    IsIntegrallyClosed.exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one (K := ↥K) Q hQ1

  have hVA : ∀ a : A, algebraMap A ↥K a ∈ V := fun a => by
    rw [IsScalarTower.algebraMap_apply A ↥(chartAlgInf A (↥K) j) ↥K]
    exact hCV _
  have hϖV : algebraMap A ↥K ϖ ∈ V.nonunits := by
    rw [IsScalarTower.algebraMap_apply A ↥(chartAlgInf A (↥K) j) ↥K]
    exact (hcen _).mpr hϖQ
  have hVm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits := by
    intro a ha
    rw [hϖ, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [map_mul, ValuationSubring.mem_nonunits_iff, Valuation.map_mul]
    have h1 : V.valuation (algebraMap A ↥K ϖ) < 1 := (ValuationSubring.mem_nonunits_iff _).mp hϖV
    have h2 : V.valuation (algebraMap A ↥K c) ≤ 1 := V.valuation_le_one ⟨_, hVA c⟩
    calc V.valuation (algebraMap A ↥K ϖ) * V.valuation (algebraMap A ↥K c)
        ≤ V.valuation (algebraMap A ↥K ϖ) * 1 := mul_le_mul_right h2 _
      _ < 1 := by rwa [mul_one]
  have hVjinv : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j⁻¹ P ∈ V ∧ (Polynomial.aeval j⁻¹ P)⁻¹ ∈ V := by
    intro P hP
    obtain ⟨b, hb, hbQ⟩ := hgauss P hP
    have hmemV : Polynomial.aeval j⁻¹ P ∈ V := by rw [← hb]; exact hCV _
    have hnn : Polynomial.aeval j⁻¹ P ∉ V.nonunits := fun h => hbQ ((hcen _).mp (by rw [hb]; exact h))
    refine ⟨hmemV, ?_⟩
    rw [ValuationSubring.mem_nonunits_iff, not_lt] at hnn
    have heq : V.valuation (Polynomial.aeval j⁻¹ P) = 1 := le_antisymm (V.valuation_le_one ⟨_, hmemV⟩) hnn
    exact (V.valuation_le_one_iff _).mp (by rw [map_inv₀, heq, inv_one])
  have hVj : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V :=
    E149V.gauss_of_gauss_inv V j (Fact.out : j ≠ 0) hVjinv

  haveI : NeZero (q * M') := ⟨mul_ne_zero (Fact.out : q.Prime).ne_zero (NeZero.ne M')⟩
  set K₀' : IntermediateField L (LaurentSeries L) :=
    ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M'))) with hK₀'def
  have hle' : K₀' ≤ K := by
    rw [hK₀'def, hK]
    exact ModularCurve.laurentBaseChange_qExpFunctionFieldC_gamma0_le_laurentBaseChange_xHFunctionField L (q * M') (q ^ 2 * M')
      ⟨q, by ring⟩ _
  have hle₀' : K₀ ≤ K₀' := by
    rw [hK₀, hK₀'def]
    have h : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) ≤
        ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionFieldC ℚ (q * M') ⊤) :=
      ModularCurve.laurentBaseChange_qExpFunctionFieldC_gamma0_le_laurentBaseChange_xHFunctionField L M' (q * M') ⟨q, by ring⟩ ⊤
    rwa [ModularCurve.xHFunctionFieldC_top] at h
  letI algK₀K : Algebra ↥K₀ ↥K := (IntermediateField.inclusion hle₀).toRingHom.toAlgebra
  letI algK₀'K : Algebra ↥K₀' ↥K := (IntermediateField.inclusion hle').toRingHom.toAlgebra

  obtain ⟨O₀, hO₀, hO₀A, hO₀m, hO₀j, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC (CongruenceSubgroup.Gamma0 M') L K₀ hK₀ A j₀ hj₀

  letI algAK₀' : Algebra A ↥K₀' := ((algebraMap L ↥K₀').comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower A L ↥K₀' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let j₀' : ↥K₀' := ⟨(j₀ : LaurentSeries L), hle₀' j₀.2⟩
  have hj₀' : ((j₀' : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq := hj₀
  haveI : Fact (j₀' ≠ 0) := ⟨fun h => (Fact.out : j₀ ≠ 0) (Subtype.ext (by
    have h' := congrArg Subtype.val h
    exact h'))⟩
  obtain ⟨O₀', hO₀', -, -, -, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC (CongruenceSubgroup.Gamma0 (q * M')) L K₀' hK₀'def A j₀' hj₀'

  have hinclL : ∀ x : L, IntermediateField.inclusion hle₀ (algebraMap L ↥K₀ x) = algebraMap L ↥K x := fun _ => rfl
  have hinclj : IntermediateField.inclusion hle₀ j₀ = j := by
    apply Subtype.ext
    show ((j₀ : ↥K₀) : LaurentSeries L) = ((j : ↥K) : LaurentSeries L)
    rw [hj₀, hj]
  have hV₀ : V.comap (IntermediateField.inclusion hle₀).toRingHom = O₀ := by
    apply ModularCurve.valuationSubring_unique_laurentBaseChange_gamma0_of_not_dvd q M' hqM' L K₀ hK₀ A hAq j₀ hj₀
    · refine ⟨fun a => ?_, fun a ha => ?_, fun P hP => ?_⟩
      · rw [ValuationSubring.mem_comap]
        show IntermediateField.inclusion hle₀ (algebraMap L ↥K₀ (algebraMap A L a)) ∈ V
        rw [hinclL, ← IsScalarTower.algebraMap_apply A L ↥K]
        exact hVA a
      · rw [E149V.mem_nonunits_comap_iff]
        show IntermediateField.inclusion hle₀ (algebraMap L ↥K₀ (algebraMap A L a)) ∈ V.nonunits
        rw [hinclL, ← IsScalarTower.algebraMap_apply A L ↥K]
        exact hVm a ha
      · have hP' := hVj P hP
        have heq : IntermediateField.inclusion hle₀ (Polynomial.aeval j₀ (P.map (algebraMap A L))) = Polynomial.aeval j P := by
          rw [← Polynomial.aeval_map_algebraMap L j P, ← hinclj]
          exact (Polynomial.aeval_algHom_apply (IntermediateField.inclusion hle₀) j₀ _).symm
        constructor
        · rw [ValuationSubring.mem_comap]
          show IntermediateField.inclusion hle₀ (Polynomial.aeval j₀ (P.map (algebraMap A L))) ∈ V
          rw [heq]; exact hP'.1
        · rw [ValuationSubring.mem_comap]
          show IntermediateField.inclusion hle₀ (Polynomial.aeval j₀ (P.map (algebraMap A L)))⁻¹ ∈ V
          rw [map_inv₀, heq]; exact hP'.2
    · refine ⟨fun a => ?_, fun a ha => ?_, fun P hP => ?_⟩
      · rw [← IsScalarTower.algebraMap_apply A L ↥K₀]; exact hO₀A a
      · rw [← IsScalarTower.algebraMap_apply A L ↥K₀]; exact hO₀m a ha
      · rw [Polynomial.aeval_map_algebraMap]; exact hO₀j P hP
  have hVK₀ : ∀ x : ↥K₀, algebraMap ↥K₀ ↥K x ∈ V ↔ x ∈ O₀ := by
    intro x
    rw [← hV₀, ValuationSubring.mem_comap]
    rfl

  have hcenV : ∀ b : ↥(chartAlgInf A (↥K) j), (b : ↥K) ∈ V.nonunits → b ∈ y.asIdeal :=
    fun b hb => hQy ((hcen b).mp hb)
  have hVK₀' : ∀ x : ↥K₀', algebraMap ↥K₀' ↥K x ∈ V ↔ x ∈ O₀' :=
    ModularCurve.FullLevel.forall_mem_iff_mem_gauss_gamma0_mul_of_forall_mem_nonunits_of_jInvChartInf_mem_xH_of_isAlgebraic_of_eq_three
      q hq3 M' hqM' L ζ hζ hιC K hK A hAq hζA j hj ϖ hϖ W₀ hW₀ z ϖz hϖz hz y hy hmax hcusp hz₀
      K₀ hK₀ K₀' hK₀'def hle₀' hle' O₀ hO₀ O₀' hO₀' V hVK₀ hcenV

  obtain ⟨⟨τ, -, hVτ⟩, ⟨hB, -, hloc, hsepV⟩⟩ :=
    ModularCurve.FullLevel.exists_comap_eq_and_ramificationIdx_eq_one_and_isSeparable_of_over_gauss_gamma0_mul_xH_of_eq_three
      q hq3 M' hqM' L ζ hζ hιC K hK K₀ hK₀ hle₀ A hAq hζA W₀ hW₀ O₀ hO₀ K₀' hK₀'def hle₀' hle' O₀' hO₀' V hVK₀'
  refine hiff.mpr ⟨?_, ?_⟩
  ·
    have key : ∀ f : ↥K, f ∈ V.nonunits → ∃ g : ↥K, g ∈ V ∧
        f = algebraMap ↥(chartAlgInf A (↥K) j) ↥K (algebraMap A ↥(chartAlgInf A (↥K) j) ϖ) * g := by
      intro f hf
      have hfτ : τ f ∈ W₀.nonunits := by
        rw [hVτ] at hf
        exact (E149V.mem_nonunits_comap_iff W₀ τ.toAlgHom.toRingHom f).mp hf
      obtain ⟨g, hg, hfg⟩ :=
        ModularCurve.exists_eq_mul_of_mem_nonunits_of_forall_mem_iff_gaussPresentation L K A ϖ hϖ W₀ hW₀ (τ f) hfτ
      refine ⟨τ.symm g, ?_, ?_⟩
      · rw [hVτ, ValuationSubring.mem_comap]
        show τ (τ.symm g) ∈ W₀
        rw [AlgEquiv.apply_symm_apply]
        exact hg
      · have hϖA : algebraMap ↥(chartAlgInf A (↥K) j) ↥K (algebraMap A ↥(chartAlgInf A (↥K) j) ϖ) =
            algebraMap L ↥K (algebraMap A L ϖ) := by
          rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A L ↥K]
        rw [hϖA]
        apply τ.injective
        rw [map_mul, AlgEquiv.commutes, AlgEquiv.apply_symm_apply, ← IsScalarTower.algebraMap_apply A L ↥K]
        exact hfg
    have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime Q) =
        Ideal.span {algebraMap ↥(chartAlgInf A (↥K) j) (Localization.AtPrime Q) (algebraMap A ↥(chartAlgInf A (↥K) j) ϖ)} :=
      (hramiff _ hϖQ).mp key
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hx' : algebraMap ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) x ∈ Q := by
        rw [Ideal.under_def, Ideal.mem_comap] at hx
        exact hx
      rw [Ideal.mem_comap]
      show algebraMap ↥(chartAlgInf A (↥K) j) (Localization.AtPrime Q) (algebraMap ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) x) ∈ _
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).mpr hx'
    · rw [hmax, Ideal.span_singleton_le_iff_mem, ← htϖ]
      exact Ideal.mem_map_of_mem _ hϖ₂
  ·
    obtain ⟨V₂, hV₂mem, -, -, -, ιV₂, hιV₂⟩ :=
      IsIntegrallyClosed.exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one (K := ↥K₀)
        (Q.under ↥(chartAlgInf A (↥K₀) j₀)) hQ₂1
    obtain ⟨V₂', hPIR', -, hV₂'mem⟩ :=
      IsIntegrallyClosed.exists_valuationSubring_mem_iff_of_height_eq_one ↥K₀ (Q.under ↥(chartAlgInf A (↥K₀) j₀)) hQ₂1
    have hVV : V₂' = V₂ := by
      ext x
      rw [hV₂'mem, hV₂mem]
    subst hVV
    have hV₂ : ∀ y : ↥K₀, y ∈ V₂' ↔ (IntermediateField.inclusion hle₀).toRingHom y ∈ V :=
      E149V.mem_valuationSubring_iff_of_under (IntermediateField.inclusion hle₀).toRingHom hι₂O Q V hCV hcen V₂' hPIR' hV₂mem
        (algebraMap A ↥(chartAlgInf A (↥K₀) j₀) ϖ) hϖ₂ hϖK₀
    have hVO : O₀ = V₂' := by
      ext x
      rw [hV₂]
      exact (hVK₀ x).symm
    subst hVO
    letI algOV : Algebra ↥O₀ ↥V :=
      (((algebraMap ↥K₀ ↥K).comp O₀.subtype).codRestrict V.toSubring fun a => (hB a).mpr a.2).toAlgebra
    haveI := hloc
    haveI := hsepV
    exact E149V.isSeparable_residueField_of_under (O := ↥(chartAlgInf A (↥K₀) j₀)) (C := ↥(chartAlgInf A (↥K) j))
      (IntermediateField.inclusion hle₀).toRingHom hι₂O Q V hCV ιV hιV O₀ hV₂mem ιV₂ hιV₂ (fun y => rfl)

end S_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three
end P2MW
export P2MW.S_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_three (solution)
