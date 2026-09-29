-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_forall_mem_nonunits_gauss_of_forall_not_mem_ssJSet_twoChartIntegralModel_xH_of_isAlgebraic_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/e7d1965c-0801-5082-b95f-259587a7d517

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_mem_smoothLocus_of_isRegularLocalRing_stalk_of_ringKrullDim_le_one_of_perfectField
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_flat_toBase
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_locallyOfFinitePresentation_toBase
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicGeometry_ker_fiberIota_stalkMap_eq_maximalIdeal_map
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_ringKrullDim_stalk_le
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Theorems.Thm_AlgebraicGeometry_IsOpenImmersion_ringKrullDim_stalk_eq
import Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
import Theorems.Thm_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_not_isMaximal_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_isMaximal_of_not_mem_ssJSet_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH_of_perfectField_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_isRegularLocalRing_fibre_of_not_mem_range_iotaFin_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH_of_embedding_of_isAlgebraic_of_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_forall_mem_nonunits_gauss_of_forall_not_mem_ssJSet_twoChartIntegralModel_xH_of_isAlgebraic_of_eq_two
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth"
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "instance" "ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.jqNModC_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants"
p2m_attr_erase "simp" "AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.frickeH1L_apply"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.cuspCount_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_baseChangeRingHom ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.GluedPic0.toPic0Pair_mk"
p2m_attr_erase "simp" "AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_nodeEquivOfPlaces_apply ModularCurve.widthOfPlaces_mk ModularCurve.smulNodePairEmb_apply ModularCurve.card_nodePairsOfPlaces ModularCurve.smulNodePair_snd ModularCurve.smulNodePair_fst ModularCurve.coe_nodeEquivOfPlaces_symm_apply ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe"
p2m_attr_erase "simp" "ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty ModularCurve.coe_jqNGen"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

namespace IgX

theorem levelData
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) :
    Transcendental A j ∧ FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := by
  refine ⟨ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj, ?_⟩
  haveI : NeZero (q ^ 2 * M') := ⟨Nat.mul_ne_zero (pow_ne_zero 2 (Fact.out : q.Prime).ne_zero) (NeZero.ne M')⟩
  haveI : (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
  exact ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))
    (ModularCurve.translation_mem_GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) L K hK j hj

theorem stalkMap_algebraMap_eq_germ
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (x : ↥X) (r : R) :
    letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) :=
      AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := R) (f.base x)
    (f.stalkMap x).hom (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) r) =
      (X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := R) (f.base x)
  show (f.stalkMap x).hom (AlgebraicGeometry.StructureSheaf.toStalk R (f.base x) r) = _
  simp only [AlgebraicGeometry.StructureSheaf.toStalk, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  erw [Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial]
  rfl

theorem asIdeal_base_eq_maximalIdeal
    {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (x : ↥X) (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (hx : (X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ)) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    (f.base x).asIdeal = IsLocalRing.maximalIdeal R := by
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := R) (f.base x)
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) (f.base x).asIdeal :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk R (f.base x)
  rw [← stalkMap_algebraMap_eq_germ f x ϖ] at hx
  have h1 : algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) ϖ ∈
      IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal] at hx ⊢
    exact fun hu => hx (hu.map _)
  have h2 : ϖ ∈ (f.base x).asIdeal :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) (f.base x).asIdeal ϖ).mp h1
  refine ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le (f.base x).isPrime.ne_top ?_).symm
  rw [hϖ, Ideal.span_le, Set.singleton_subset_iff]
  exact h2

theorem map_maximalIdeal_stalkMap_eq_span
    {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (x : ↥X) (ϖ : R)
    (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (hfx : (f.base x).asIdeal = IsLocalRing.maximalIdeal R) :
    (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x))).map (f.stalkMap x).hom =
      Ideal.span {(X.presheaf.germ ⊤ x trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ))} := by
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := R) (f.base x)
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)) (f.base x).asIdeal :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk R (f.base x)
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (f.base x).asIdeal ((Spec (CommRingCat.of R)).presheaf.stalk (f.base x)),
    hfx, hϖ, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, stalkMap_algebraMap_eq_germ]

theorem ringKrullDim_le_of_isIntegral_ringHom
    {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  letI : Algebra R S := φ.toAlgebra
  refine Order.krullDim_le_of_strictMono (fun P : PrimeSpectrum S => PrimeSpectrum.comap φ P) ?_
  intro P Q hPQ
  have hle : P.asIdeal ≤ Q.asIdeal := le_of_lt hPQ
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => ne_of_lt hPQ (PrimeSpectrum.ext h)
  obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal := by
    by_contra h
    exact hne (le_antisymm hle fun y hy => by_contra fun hy' => h ⟨y, hy, hy'⟩)
  change P.asIdeal.comap φ < Q.asIdeal.comap φ
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxQ, hxP⟩ (hφ x)

theorem ringKrullDim_chartAlg_singleton_le
    (R : Type) [CommRing R] (F : Type) [Field F] [Algebra R F] (s : F) :
    ringKrullDim ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}) ≤ ringKrullDim (Polynomial R) := by

  let ψ : Polynomial R →ₐ[R] ↥(Algebra.adjoin R ({s} : Set F)) :=
    (Polynomial.aeval s).codRestrict (Algebra.adjoin R ({s} : Set F))
      (fun P => by
        rw [Algebra.adjoin_singleton_eq_range_aeval]
        exact ⟨P, rfl⟩)
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨P, rfl⟩ := hy
    exact ⟨P, Subtype.ext rfl⟩

  let ι : ↥(Algebra.adjoin R ({s} : Set F)) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}) :=
    (Subalgebra.inclusion (AlgebraicCurve.TwoChartIntegralModel.adjoin_le_chartAlg R F {s})).toRingHom
  have hι : ι.IsIntegral := by
    intro x
    obtain ⟨P, hPm, hP⟩ := (AlgebraicCurve.TwoChartIntegralModel.mem_chartAlg_iff R F).mp x.2
    refine ⟨P, hPm, ?_⟩
    apply Subtype.ext
    have h1 := Polynomial.hom_eval₂ P ι ((AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}).val.toRingHom) x
    have h2 : ((AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}).val.toRingHom).comp ι =
        algebraMap ↥(Algebra.adjoin R ({s} : Set F)) F := rfl
    rw [h2] at h1
    exact h1.trans hP
  calc ringKrullDim ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s})
      ≤ ringKrullDim ↥(Algebra.adjoin R ({s} : Set F)) := ringKrullDim_le_of_isIntegral_ringHom ι hι
    _ ≤ ringKrullDim (Polynomial R) :=
        ringKrullDim_le_of_isIntegral_ringHom ψ.toRingHom (RingHom.isIntegral_of_surjective _ hψ)

theorem ringKrullDim_stalk_le_two
    (R : Type) [CommRing R] [IsNoetherianRing R] (hR : ringKrullDim R ≤ 1)
    (F : Type) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel R F j)) :
    ringKrullDim ((AlgebraicCurve.TwoChartIntegralModel R F j).presheaf.stalk z) ≤ 2 := by
  have hpoly : ringKrullDim (Polynomial R) ≤ 2 := by
    rw [Polynomial.ringKrullDim_of_isNoetherianRing]
    calc ringKrullDim R + 1 ≤ 1 + 1 := add_le_add hR le_rfl
      _ = 2 := by norm_num
  have key : ∀ (s : F) (y : ↥(Spec (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s})))),
      ringKrullDim ((Spec (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}))).presheaf.stalk y) ≤ 2 := by
    intro s y
    calc ringKrullDim ((Spec (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}))).presheaf.stalk y)
        ≤ ringKrullDim Γ(Spec (CommRingCat.of ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s})), ⊤) :=
          AlgebraicGeometry.IsAffineOpen.ringKrullDim_stalk_le (isAffineOpen_top _) y trivial
      _ = ringKrullDim ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlg R F {s}) :=
          ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of _)).commRingCatIsoToRingEquiv
      _ ≤ ringKrullDim (Polynomial R) := ringKrullDim_chartAlg_singleton_le R F s
      _ ≤ 2 := hpoly
  rcases AlgebraicCurve.TwoChartIntegralModel.mem_range_ιFin_or_mem_range_ιInf R F j z with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · rw [← AlgebraicGeometry.IsOpenImmersion.ringKrullDim_stalk_eq (AlgebraicCurve.TwoChartIntegralModel.ιFin R F j) y]
    exact key j y
  · rw [← AlgebraicGeometry.IsOpenImmersion.ringKrullDim_stalk_eq (AlgebraicCurve.TwoChartIntegralModel.ιInf R F j) y]
    exact key j⁻¹ y

theorem fibre_stalk_regular_and_dim
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (s : ↥(Spec (CommRingCat.of R))) (q : ↥(f.fiber s))
    (t : X.presheaf.stalk ((f.fiberι s).base q))
    (ht : (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk (f.base ((f.fiberι s).base q)))).map
        (f.stalkMap ((f.fiberι s).base q)).hom = Ideal.span {t})
    (hreg : IsRegularLocalRing ((X.presheaf.stalk ((f.fiberι s).base q)) ⧸ Ideal.span {t}))
    (hdim : ringKrullDim ((X.presheaf.stalk ((f.fiberι s).base q)) ⧸ Ideal.span {t}) ≤ 1) :
    IsRegularLocalRing ((f.fiber s).presheaf.stalk q) ∧ ringKrullDim ((f.fiber s).presheaf.stalk q) ≤ 1 := by
  have hsurj : Function.Surjective ((f.fiberι s).stalkMap q).hom := (f.fiberι s).stalkMap_surjective q
  have hker : RingHom.ker ((f.fiberι s).stalkMap q).hom = Ideal.span {t} := by
    rw [AlgebraicGeometry.ker_fiberIota_stalkMap_eq_maximalIdeal_map f s q, ht]
  let e : ((X.presheaf.stalk ((f.fiberι s).base q)) ⧸ Ideal.span {t}) ≃+* (f.fiber s).presheaf.stalk q :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  haveI := hreg
  exact ⟨IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e) ▸ hdim⟩

end IgX

namespace IgX

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

end IgX

open IgX in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))

    [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [PerfectField (IsLocalRing.ResidueField A)]
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

    (hzFin : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j),
      (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal)
    (hzInf : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf A (↥K) j),
      (AlgebraicCurve.TwoChartIntegralModel.ιInf A (↥K) j).base y = z →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal)

    (hord : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A (↥K) j),
      (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base y = z →
        ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
          (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω),
          RingHom.ker φ = y.asIdeal →
            φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A (↥K) j) ∉ ModularCurve.ssJSet q Ω) :
    ∃ U : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).Opens,
      z ∈ U ∧ Smooth (U.ι ≫ AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) := by
  classical
  obtain ⟨htj, hFD⟩ := IgX.levelData q M' L K hK A j hj

  have hreg : IsRegularLocalRing (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ⧸ Ideal.span {ϖz}) := by
    by_cases hzF : z ∈ Set.range (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j).base
    · obtain ⟨y, hy⟩ := hzF
      have hϖy : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ϖ ∈ y.asIdeal := by
        subst hy; subst hϖz
        exact (IgX.germ_mem_maximalIdeal_iff_of_chart (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (AlgebraicCurve.TwoChartIntegralModel.ιFin A (↥K) j)
          (AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase A (↥K) j) y ϖ).mp hz
      by_cases hmax : y.asIdeal.IsMaximal
      ·
        letI : Field (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y.asIdeal) := Ideal.Quotient.field y.asIdeal
        let Ω : Type := AlgebraicClosure (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y.asIdeal)
        let φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) →+* Ω := (algebraMap (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y.asIdeal) Ω).comp (Ideal.Quotient.mk y.asIdeal)
        have hφ : RingHom.ker φ = y.asIdeal := by
          ext b
          simp only [φ, RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, map_eq_zero_iff _ (algebraMap (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y.asIdeal) Ω).injective,
            Ideal.Quotient.eq_zero_iff_mem]
        haveI : CharP (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y.asIdeal) q := by
          have hq0 : ((q : ℕ) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y.asIdeal) = 0 := by
            have hqϖ : (q : A) ∈ Ideal.span {ϖ} := hϖ ▸ hAq
            obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hqϖ
            have hmem : ((q : ℕ) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) ∈ y.asIdeal := by
              have : ((q : ℕ) : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j)) = algebraMap A _ (q : A) := by simp
              rw [this, ← hc, map_mul]
              exact Ideal.mul_mem_left _ _ hϖy
            rw [← map_natCast (Ideal.Quotient.mk y.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
            exact hmem
          exact (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr hq0
        haveI : CharP Ω q := charP_of_injective_algebraMap (algebraMap (↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K) j) ⧸ y.asIdeal) Ω).injective q
        exact ModularCurve.FullLevel.isRegularLocalRing_fibre_of_isMaximal_of_not_mem_ssJSet_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH_of_perfectField_of_eq_two q hq2 M' hqM' L ζ hζ hι K hK A hAq hζA j hj ϖ hϖ W₀ hW₀ z ϖz hϖz hz y hy hmax Ω φ hφ (hord y hy Ω φ hφ) (hzFin y hy)
      · exact ModularCurve.FullLevel.isRegularLocalRing_fibre_of_not_isMaximal_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH_of_eq_two q hq2 M' hqM' L ζ hζ K hK A hAq hζA j hj ϖ hϖ W₀ hW₀ z ϖz hϖz hz y hy hmax (hzFin y hy)
    ·
      exact ModularCurve.FullLevel.isRegularLocalRing_fibre_of_not_mem_range_iotaFin_of_forall_mem_nonunits_gauss_twoChartIntegralModel_xH_of_embedding_of_isAlgebraic_of_eq_two q hq2 M' hqM' L ζ hζ hι K hK A hAq hζA j hj ϖ hϖ W₀ hW₀ z ϖz hϖz hz hzF hzInf

  haveI := hFD
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsSeparable.of_integral _ _
  obtain ⟨hftF, hftI⟩ := AlgebraicCurve.TwoChartIntegralModel.finiteType_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD inferInstance
  haveI := hftF; haveI := hftI
  haveI : Flat (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) := AlgebraicCurve.TwoChartIntegralModel.flat_toBase A (↥K) j
    (by
      rw [IsScalarTower.algebraMap_eq A L ↥K]
      exact (algebraMap L ↥K).injective.comp (IsFractionRing.injective A L))
  haveI : LocallyOfFinitePresentation (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) := AlgebraicCurve.TwoChartIntegralModel.locallyOfFinitePresentation_toBase A (↥K) j

  haveI : IsIntegral (AlgebraicCurve.TwoChartIntegralModel A (↥K) j) := AlgebraicCurve.TwoChartIntegralModel.isIntegral A (↥K) j
  have hϖ0 : ϖ ≠ 0 := fun h => IsDiscreteValuationRing.not_a_field A (by rw [hϖ, h, Ideal.span_singleton_eq_bot])
  have hϖz0 : ϖz ≠ 0 := by
    letI : Algebra A ((Spec (CommRingCat.of A)).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).base z)) := AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := A) ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).base z)
    haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of A)).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).base z)) ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).base z).asIdeal :=
      AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk A ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).base z)
    have h1 : ϖz = ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).stalkMap z).hom (algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).base z)) ϖ) := by
      rw [stalkMap_algebraMap_eq_germ]; exact hϖz
    have hinjA : Function.Injective (algebraMap A ((Spec (CommRingCat.of A)).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).base z))) :=
      IsLocalization.injective ((Spec (CommRingCat.of A)).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).base z)) ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).base z).asIdeal.primeCompl_le_nonZeroDivisors
    have hinj : Function.Injective ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).stalkMap z).hom := by
      algebraize [((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).stalkMap z).hom]
      have : Module.FaithfullyFlat ((Spec (CommRingCat.of A)).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).base z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) :=
        @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
          (AlgebraicGeometry.Flat.stalkMap (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) z) ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).toLRSHom.prop z)
      exact FaithfulSMul.algebraMap_injective ((Spec (CommRingCat.of A)).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).base z)) ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    rw [h1]
    exact fun h => hϖ0 (hinjA (hinj (by rw [h, map_zero, map_zero])))
  have hdim : ringKrullDim (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ⧸ Ideal.span {ϖz}) ≤ 1 := by
    have h2 : ringKrullDim ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ≤ 2 :=
      ringKrullDim_stalk_le_two A (IsDiscreteValuationRing.ringKrullDim_eq_one A).le (↥K) j z
    have h1 : ringKrullDim (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ⧸ Ideal.span {ϖz}) + 1 ≤ ringKrullDim ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) :=
      ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hϖz0)
    have h12 := h1.trans h2
    generalize hd : ringKrullDim (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z) ⧸ Ideal.span {ϖz}) = d at h12
    induction d using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        exfalso
        have h'' := h12
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add] at h''
        simp at h''
        first
          | exact Option.noConfusion h''
          | exact (WithBot.natCast_ne_top 2) h''
          | exact (WithBot.ofNat_ne_top 2) h''
          | cases h''
      | coe n =>
        have hn : n + 1 ≤ 2 := by
          have : (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
            simpa using h12
          exact_mod_cast this
        have hn1 : n ≤ 1 := by omega
        have : (((n : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hn1
        simpa using this

  have hfz : ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).base z).asIdeal = IsLocalRing.maximalIdeal A :=
    asIdeal_base_eq_maximalIdeal (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) z ϖ hϖ (hϖz ▸ hz)
  have hmax : (IsLocalRing.maximalIdeal ((Spec (CommRingCat.of A)).presheaf.stalk ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).base z))).map ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).stalkMap z).hom =
      Ideal.span {ϖz} := by
    rw [hϖz]
    exact map_maximalIdeal_stalkMap_eq_span (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) z ϖ hϖ hfz
  have hs₀ : (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).base z = IsLocalRing.closedPoint A := PrimeSpectrum.ext hfz
  obtain ⟨w, hw⟩ : ∃ w : ↥((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).fiber (IsLocalRing.closedPoint A)), ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).fiberι (IsLocalRing.closedPoint A)).base w = z := by
    have : z ∈ Set.range ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).fiberι (IsLocalRing.closedPoint A)).base := by
      rw [Scheme.Hom.range_fiberι]
      exact hs₀
    exact this
  subst hw
  obtain ⟨hreg', hdim'⟩ := fibre_stalk_regular_and_dim (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (IsLocalRing.closedPoint A) w ϖz hmax hreg hdim

  haveI : PerfectField (IsLocalRing.ResidueField ((Spec (CommRingCat.of A)).presheaf.stalk (IsLocalRing.closedPoint A))) := by
    let e : ((Spec (CommRingCat.of A)).presheaf.stalk (IsLocalRing.closedPoint A)) ≃+* A :=
      (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
    let eκ : IsLocalRing.ResidueField ((Spec (CommRingCat.of A)).presheaf.stalk (IsLocalRing.closedPoint A)) ≃+*
        IsLocalRing.ResidueField A := IsLocalRing.ResidueField.mapEquiv e
    letI : Algebra (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField ((Spec (CommRingCat.of A)).presheaf.stalk (IsLocalRing.closedPoint A))) :=
      eκ.symm.toRingHom.toAlgebra
    haveI : Algebra.IsAlgebraic (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField ((Spec (CommRingCat.of A)).presheaf.stalk (IsLocalRing.closedPoint A))) :=
      Algebra.IsAlgebraic.of_injective (AlgEquiv.ofRingEquiv (f := eκ.symm) (fun _ => rfl)).symm.toAlgHom
        (AlgEquiv.ofRingEquiv (f := eκ.symm) (fun _ => rfl)).symm.injective
    exact Algebra.IsAlgebraic.perfectField (K := IsLocalRing.ResidueField A)

  let Kz : Type := IsLocalRing.ResidueField ((Spec (CommRingCat.of A)).presheaf.stalk (IsLocalRing.closedPoint A))
  let g' : (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).fiber (IsLocalRing.closedPoint A) ⟶ Spec (CommRingCat.of Kz) := (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).fiberToSpecResidueField (IsLocalRing.closedPoint A)
  haveI hlfp : LocallyOfFinitePresentation g' :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _ ‹_›
  haveI : PerfectField Kz := ‹_›
  haveI hlfp2 : LocallyOfFinitePresentation ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).fiberToSpecResidueField (IsLocalRing.closedPoint A)) := hlfp
  have hzs : w ∈ g'.smoothLocus :=
    AlgebraicGeometry.Scheme.Hom.mem_smoothLocus_of_isRegularLocalRing_stalk_of_ringKrullDim_le_one_of_perfectField g' w hreg' hdim'
  have hz' : ((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).fiberι (IsLocalRing.closedPoint A)).base w ∈ (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).smoothLocus :=
    AlgebraicGeometry.Scheme.Hom.fiberInclusion_mem_smoothLocus_of_mem_smoothLocus_fiberToSpecResidueField
      (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) (IsLocalRing.closedPoint A) w hzs

  refine ⟨(AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).smoothLocus, hz', ?_⟩
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
  ext x
  simp

end S_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_forall_mem_nonunits_gauss_of_forall_not_mem_ssJSet_twoChartIntegralModel_xH_of_isAlgebraic_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_forall_mem_nonunits_gauss_of_forall_not_mem_ssJSet_twoChartIntegralModel_xH_of_isAlgebraic_of_eq_two (solution)
