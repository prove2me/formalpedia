-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/23f80df1-5b07-52a6-b8ad-aae28aad3c1c

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_FullLevel_exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_descent_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_descent_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgFin_descent_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_mem_ssJSet_of_forall_mem_maximalIdeal_drinfeldRing_mem_chartAlgFin_descent_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_chartAlgInf_descent_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgInf_descent_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_exists_valuationSubring_localization_chartAlg_of_not_mem_descent_of_eq_two
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_ModularCurve_FullLevel_algebraMap_mem_of_le_igusaRing_descent_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_isMaximal_of_forall_mem_iff_mem_nonunits_of_lt_gaussRing_descent_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_exists_valuationSubring_localization_chartAlg_of_not_mem_descent_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_exists_jInvariant_sub_mem_maximalIdeal_drinfeldRing_descent_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_exists_forall_mem_maximalIdeal_drinfeldRing_mem_of_isMaximal_chartAlgFin_of_mem_ssJSet_descent_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_exists_primes_chartAlg_localization_eq_igusaRing_minimal_injective_descent_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss
import Theorems.Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_two
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange"
p2m_attr_erase "instance" "ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso ValuationSubring.instIsAlgClosedResidueField ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.cuspCount_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_baseChangeRingHom ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply"
p2m_attr_erase "simp" "CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty ModularCurve.coe_jqNGen ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 32000000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))

    (K₀ : Subfield (AlgebraicClosure ℚ)) [Algebra.IsAlgebraic ↥K₀ (AlgebraicClosure ℚ)] (hπK₀ : π ∈ K₀)
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι : A₀ →+* ↥A) [IsLocalHom ι] (hι : Function.Injective ι)
    (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : AlgebraicClosure ℚ)) =
      (A : Set (AlgebraicClosure ℚ)) ∩ (K₀ : Set (AlgebraicClosure ℚ)))
    (hres : Function.Surjective ((IsLocalRing.residue ↥A).comp ι))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})

    (hϖ₀π : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) = π)

    (F₀ : Subfield ↥(fieldBar q M'))
    (hF₀ : ∀ f : ↥(fieldBar q M'), f ∈ F₀ ↔ ∀ n : ℤ, ((f : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ K₀)

    (hjF₀ : (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) ∈ F₀)

    [Algebra A₀ ↥F₀]
    (hj₀ : ∀ a : A₀, ((algebraMap A₀ ↥F₀ a : ↥F₀) : ↥(fieldBar q M')) =
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ))
    (V : ValuationSubring ↥F₀)

    (hV : ∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q))
    (hVlt : ∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ∧ f ∉ V) :
    (∃ (B : Subalgebra A₀ ↥F₀) (𝔪 : Ideal ↥B) (_ : 𝔪.IsMaximal),

      B.FG ∧
      (∀ x : ↥F₀, _root_.IsIntegral ↥B x → x ∈ B) ∧
      (∀ x : ↥F₀, ∃ b c : ↥F₀, b ∈ B ∧ c ∈ B ∧ c ≠ 0 ∧ x * c = b) ∧
      (∀ 𝔮 : Ideal ↥B, 𝔮.IsPrime → Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔮 → ¬ 𝔮.IsMaximal →
        𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes) ∧
      (∀ 𝔭 : Ideal ↥B, 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀) ≤ 𝔭) →
        ∃ V₁ : ValuationSubring ↥F₀, ∀ f : ↥F₀, f ∈ V₁ ↔ ∃ b c : ↥B, c ∉ 𝔭 ∧ f * (c : ↥F₀) = (b : ↥F₀)) ∧

      (∀ ℓ' : CuspidalType.ProjLine q, (∀ b : ↥B, ((b : ↥F₀) : ↥(fieldBar q M')) ∈ OIg ℓ') → ℓ' = lineInfty q) ∧
      (∀ s : ↥W, ¬ ∀ b : ↥B, ((b : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s) ∧
      (∃ 𝔮 : Ideal ↥B, 𝔮.IsPrime ∧ ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ↔
        ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧
      (∀ 𝔮 : Ideal ↥B, 𝔮 ∈ (Ideal.map (algebraMap A₀ ↥B) (maximalIdeal A₀)).minimalPrimes →
        ∀ x : ↥F₀, (x : ↥(fieldBar q M')) ∈ OIg (lineInfty q) ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀)) ∧

      (∀ b : ↥B, (b : ↥F₀) ∈ V) ∧ (∀ b : ↥B, b ∈ 𝔪 ↔ (b : ↥F₀) ∈ V.nonunits) ∧

      ((⟨_, hjF₀⟩ : ↥F₀) ∈ B ∨ (⟨_, hjF₀⟩ : ↥F₀)⁻¹ ∈ B) ∧

      (algebraMap A₀ (Localization.AtPrime 𝔪)).FormallySmooth) ∨

    (∃ s : ↥W, (∀ g : ↥F₀, _root_.IsIntegral ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) g →
        (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) →
          g ∈ V.nonunits)) := by
  classical

  let O : ValuationSubring ↥F₀ := (OIg (lineInfty q)).comap F₀.subtype
  have memO : ∀ f : ↥F₀, f ∈ O ↔ (f : ↥(fieldBar q M')) ∈ OIg (lineInfty q) := fun _ => ValuationSubring.mem_comap
  have hVO : V ≤ O := fun f hf => (memO f).mpr (hV f hf)
  have hconst : ∀ a : A₀, algebraMap A₀ ↥F₀ a ∈ V :=
    ModularCurve.FullLevel.algebraMap_mem_of_le_igusaRing_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ (lineInfty q) V hV
  obtain ⟨γ, hγ, -, hOℓ⟩ := hIg (lineInfty q)
  have hJO : (⟨_, hjF₀⟩ : ↥F₀) ∈ O ∧ ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀) ≠ 0 := by
    obtain ⟨h, hu⟩ := ModularCurve.FullLevel.isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss q M' hqM' A hle ζ γ hγ
      (OIg (lineInfty q)) hIg_inf (0 : ↥A)
    have h' : levelAutBar q M' ζ γ (((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀) : ↥(fieldBar q M')) ∈ OIg (lineInfty q) := by simpa using h
    refine ⟨?_, ?_⟩
    · rw [memO, hOℓ]; exact h'
    · intro h0
      have hJF : (((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀) : ↥(fieldBar q M')) = 0 := by rw [h0]; rfl
      have hzero : levelAutBar q M' ζ γ (((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀) : ↥(fieldBar q M')) -
          algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((0 : ↥A) : AlgebraicClosure ℚ) = 0 := by
        rw [hJF, map_zero, ZeroMemClass.coe_zero, map_zero, sub_zero]
      apply not_isUnit_zero (M₀ := ↥(OIg (lineInfty q)))
      have hz : (⟨_, h⟩ : ↥(OIg (lineInfty q))) = 0 :=
        Subtype.ext (hzero.trans (ZeroMemClass.coe_zero (OIg (lineInfty q))).symm)
      rwa [hz] at hu
  haveI hj0 : Fact ((⟨_, hjF₀⟩ : ↥F₀) ≠ 0) := ⟨hJO.2⟩

  by_cases hjV : ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀) ∈ V
  ·
    have hCV : ∀ g : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (g : ↥F₀) ∈ V := by
      intro g
      have hg : _root_.IsIntegral ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) (g : ↥F₀) := g.2

      have hle : ∀ x : ↥F₀, x ∈ Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀) → x ∈ V := by
        intro x hx
        refine Algebra.adjoin_induction (fun y hy => ?_) (fun a => hconst a) (fun _ _ _ _ => add_mem) (fun _ _ _ _ => mul_mem) hx
        rw [Set.mem_singleton_iff.mp hy]; exact hjV
      let ρ₀ : ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) →+* ↥V :=
        ((Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)).val.toRingHom).codRestrict V (fun x => hle x x.2)
      letI : Algebra ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) ↥V := ρ₀.toAlgebra
      haveI : IsScalarTower ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) ↥V ↥F₀ :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have hgV : _root_.IsIntegral ↥V (g : ↥F₀) := hg.tower_top
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥V) (K := ↥F₀)).mp hgV
      rw [← hy]; exact y.2

    let ρ : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) →+* ↥V :=
      ((TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).val.toRingHom).codRestrict V hCV
    let 𝔫 : Ideal ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) := (maximalIdeal ↥V).comap ρ
    have h𝔫 : ∀ g, g ∈ 𝔫 ↔ (g : ↥F₀) ∈ V.nonunits := by
      intro g
      rw [Ideal.mem_comap, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
      exact ⟨fun h => ⟨hCV g, h⟩, fun ⟨_, h⟩ => h⟩
    have h𝔫max : 𝔫.IsMaximal :=
      ModularCurve.FullLevel.isMaximal_of_forall_mem_iff_mem_nonunits_of_lt_gaussRing_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀
        ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀) (Or.inl rfl) V hV hVlt hCV 𝔫 h𝔫
    have hϖ𝔫 : algebraMap A₀ ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ϖ₀ ∈ 𝔫 := by
      rw [h𝔫]
      change (algebraMap A₀ ↥F₀ ϖ₀ : ↥F₀) ∈ V.nonunits

      apply ValuationSubring.nonunits_le_nonunits.mpr hVO
      obtain ⟨R, hR⟩ := ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing_of_eq_two
        q hq2 M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr
      rw [ValuationSubring.mem_nonunits_iff_or]
      right
      rw [memO]
      intro hinv
      have hcoe : (((algebraMap A₀ ↥F₀ ϖ₀)⁻¹ : ↥F₀) : ↥(fieldBar q M')) =
          algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ))⁻¹ := by
        rw [map_inv₀, ← hj₀]; rfl
      rw [hcoe, ← hR, R.algebraMap_mem_iff] at hinv

      have hπ0 : ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) ≠ 0 := by
        rw [hϖ₀π]; intro h; rw [h, zero_pow (Nat.sub_ne_zero_of_lt (by
          have := (Fact.out : q.Prime).two_le; nlinarith))] at hπ
        exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) hπ.symm
      have hu : IsUnit (ι ϖ₀) := by
        refine ⟨⟨ι ϖ₀, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hπ0), Subtype.ext (inv_mul_cancel₀ hπ0)⟩, rfl⟩
      have : IsUnit ϖ₀ := IsLocalHom.map_nonunit ϖ₀ hu
      exact (IsLocalRing.mem_maximalIdeal _).mp (hϖ₀ ▸ Ideal.mem_span_singleton_self ϖ₀) this

    by_cases hss : ∃ (Ω : Type) (_ : Field Ω) (_ : CharP Ω q) (_ : IsAlgClosed Ω) (_ : DecidableEq Ω)
        (φ : ↥(TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) →+* Ω),
        RingHom.ker φ = 𝔫 ∧ φ (TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ∈ ModularCurve.ssJSet q Ω
    ·
      obtain ⟨Ω, _, _, _, _, φ, hφ, hφss⟩ := hss
      obtain ⟨s, hs⟩ :=
        ModularCurve.FullLevel.exists_forall_mem_maximalIdeal_drinfeldRing_mem_of_isMaximal_chartAlgFin_of_mem_ssJSet_descent_of_eq_two
          q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ 𝔫 h𝔫max hϖ𝔫 Ω φ hφ hφss
      refine Or.inr ⟨s, fun g hg hgm => ?_⟩
      have hgC : g ∈ TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) := hg
      exact (h𝔫 ⟨g, hgC⟩).mp (hs ⟨g, hgC⟩ hgm)
    ·
      left
      haveI h𝔫p : 𝔫.IsPrime := h𝔫max.isPrime

      obtain ⟨hx₀, hxcl, hxFin, hxInf⟩ :=
        ModularCurve.FullLevel.toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ V hV hVlt hCV 𝔫 h𝔫p h𝔫
      have hιinj : Function.Injective (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base :=
        (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).isOpenEmbedding.injective
      have hord : ∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
          (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base y = (AlgebraicCurve.TwoChartIntegralModel.ιFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩ →
          ∀ (Ω : Type) [Field Ω] [CharP Ω q] [IsAlgClosed Ω] [DecidableEq Ω]
            (φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) →+* Ω), RingHom.ker φ = y.asIdeal →
              φ (AlgebraicCurve.TwoChartIntegralModel.jChartFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ∉ ModularCurve.ssJSet q Ω := by
        intro y hy Ω _ _ _ _ φ hφ hmem
        apply hss
        refine ⟨Ω, inferInstance, inferInstance, inferInstance, inferInstance, φ, ?_, hmem⟩
        rw [hφ, hιinj hy]
      obtain ⟨U, hxU, hU⟩ := ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ _ hx₀ hxcl hxFin hxInf hord

      have hnotSS : ∀ s : ↥W, ∃ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
          (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) ∧ g ∉ 𝔫 := by
        intro s
        by_contra hcon
        have hs : ∀ g : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
            (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) → g ∈ 𝔫 := by
          intro g hg; by_contra hgn; exact hcon ⟨g, hg, hgn⟩

        let κ𝔫 := ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) ⧸ 𝔫
        letI : Field κ𝔫 := Ideal.Quotient.field 𝔫
        let Ω := AlgebraicClosure κ𝔫
        have hchar : CharP Ω q := by

          have hϖq : ϖ₀ ^ (q ^ 2 - 1) = (q : A₀) := by
            apply hι
            apply Subtype.ext
            simp only [map_pow, map_natCast]
            rw [show (((ι ϖ₀ : ↥A) ^ (q ^ 2 - 1) : ↥A) : AlgebraicClosure ℚ) = ((ι ϖ₀ : ↥A) : AlgebraicClosure ℚ) ^ (q ^ 2 - 1)
              from by simp, hϖ₀π, hπ]
            simp
          have hq2𝔫 : (q : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) ∈ 𝔫 := by
            rw [← map_natCast (algebraMap A₀ ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))), ← hϖq, map_pow]
            exact Ideal.pow_mem_of_mem 𝔫 hϖ𝔫 _ (Nat.sub_pos_of_lt (by have := (Fact.out : q.Prime).two_le; nlinarith))
          haveI : CharP κ𝔫 q := by
            rw [CharP.charP_iff_prime_eq_zero Fact.out]
            rw [← map_natCast (Ideal.Quotient.mk 𝔫), Ideal.Quotient.eq_zero_iff_mem]
            exact hq2𝔫
          exact charP_of_injective_algebraMap (algebraMap κ𝔫 Ω).injective q
        haveI := hchar
        let φ : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) →+* Ω := (algebraMap κ𝔫 Ω).comp (Ideal.Quotient.mk 𝔫)
        have hφ : RingHom.ker φ = 𝔫 := by
          ext g
          rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap κ𝔫 Ω).injective,
            Ideal.Quotient.eq_zero_iff_mem]
        apply hss
        exact ⟨Ω, inferInstance, hchar, inferInstance, inferInstance, φ, hφ,
          ModularCurve.FullLevel.mem_ssJSet_of_forall_mem_maximalIdeal_drinfeldRing_mem_chartAlgFin_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ 𝔫 h𝔫max hϖ𝔫 s hs Ω φ hφ⟩

      obtain ⟨𝔮, hLOC, hMIN, hINJ, hSURJ⟩ :=
        ModularCurve.FullLevel.exists_primes_chartAlg_localization_eq_igusaRing_minimal_injective_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀
          ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀) (Or.inl rfl)
      have hGENFIB := ModularCurve.FullLevel.exists_valuationSubring_localization_chartAlg_of_not_mem_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀) (Or.inl rfl)
      haveI : Smooth (U.ι ≫ AlgebraicCurve.TwoChartIntegralModel.toBase A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) := hU
      exact ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgFin_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ V hV hVlt hCV 𝔫 h𝔫max h𝔫 hnotSS 𝔮 hLOC hMIN hINJ hSURJ
        (fun 𝔭 h𝔭 h0 hϖ => hGENFIB 𝔭 h𝔭 h0 hϖ) U hxU hU
  ·
    have hjinv : ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ ∈ V := (V.mem_or_inv_mem _).resolve_left hjV
    left
    have hCV : ∀ g : ↥(TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), (g : ↥F₀) ∈ V := by
      intro g
      have hg : _root_.IsIntegral ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)⁻¹} : Set ↥F₀)) (g : ↥F₀) := g.2
      have hle : ∀ x : ↥F₀, x ∈ Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)⁻¹} : Set ↥F₀) → x ∈ V := by
        intro x hx
        refine Algebra.adjoin_induction (fun y hy => ?_) (fun a => hconst a) (fun _ _ _ _ => add_mem) (fun _ _ _ _ => mul_mem) hx
        rw [Set.mem_singleton_iff.mp hy]; exact hjinv
      let ρ₀ : ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)⁻¹} : Set ↥F₀)) →+* ↥V :=
        ((Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)⁻¹} : Set ↥F₀)).val.toRingHom).codRestrict V (fun x => hle x x.2)
      letI : Algebra ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)⁻¹} : Set ↥F₀)) ↥V := ρ₀.toAlgebra
      haveI : IsScalarTower ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)⁻¹} : Set ↥F₀)) ↥V ↥F₀ :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have hgV : _root_.IsIntegral ↥V (g : ↥F₀) := hg.tower_top
      obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥V) (K := ↥F₀)).mp hgV
      rw [← hy]; exact y.2
    obtain ⟨𝔫, h𝔫⟩ : ∃ 𝔫 : Ideal ↥(TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), ∀ g, g ∈ 𝔫 ↔ (g : ↥F₀) ∈ V.nonunits := by
      let ρ : ↥(TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)) →+* ↥V := ((TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).val.toRingHom).codRestrict V hCV
      refine ⟨(maximalIdeal ↥V).comap ρ, fun g => ?_⟩
      rw [Ideal.mem_comap, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
      exact ⟨fun h => ⟨hCV g, h⟩, fun ⟨_, h⟩ => h⟩
    have h𝔫max : 𝔫.IsMaximal :=
      ModularCurve.FullLevel.isMaximal_of_forall_mem_iff_mem_nonunits_of_lt_gaussRing_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀
        ({(⟨_, hjF₀⟩ : ↥F₀)⁻¹} : Set ↥F₀) (Or.inr rfl) V hV hVlt hCV 𝔫 h𝔫
    haveI h𝔫p : 𝔫.IsPrime := h𝔫max.isPrime

    obtain ⟨hx₀, hxcl, hxnoFin, hxInf⟩ :=
      ModularCurve.FullLevel.toBase_eq_closedPoint_and_specializes_and_mem_asIdeal_of_centre_chartAlgInf_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ V hV hVlt hjV hCV 𝔫 h𝔫p h𝔫
    obtain ⟨U, hxU, hU⟩ := ModularCurve.FullLevel.exists_opens_smooth_comp_toBase_of_goodPt_twoChartIntegralModel_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀
      ((AlgebraicCurve.TwoChartIntegralModel.ιInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)).base ⟨𝔫, h𝔫p⟩) hx₀ hxcl
      (fun y hy b hb => (hxnoFin y hy).elim) hxInf (fun y hy Ω _ _ _ _ φ hφ => (hxnoFin y hy).elim)

    have hjinv𝔫 : (⟨((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹, TwoChartIntegralModel.subset_chartAlg A₀ ↥F₀ _ rfl⟩ : ↥(TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀))) ∈ 𝔫 := by
      rw [h𝔫, ValuationSubring.mem_nonunits_iff_or]
      right; rw [inv_inv]; exact hjV
    have hnotSS : ∀ s : ↥W, (∃ g : ↥(TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)),
        (∃ h : ((g : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s, (⟨_, h⟩ : ↥(OSS s)) ∈ maximalIdeal ↥(OSS s)) ∧ g ∉ 𝔫) ∨
        (∃ g : ↥(TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀)), ((g : ↥F₀) : ↥(fieldBar q M')) ∉ OSS s) := by
      intro s
      by_cases hinvS : ((((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ : ↥F₀) : ↥(fieldBar q M')) ∈ OSS s
      · left
        obtain ⟨a, ha, hamax⟩ := ModularCurve.FullLevel.exists_jInvariant_sub_mem_maximalIdeal_drinfeldRing_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ s

        have hgmem : (1 - algebraMap A₀ ↥F₀ a * ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ : ↥F₀) ∈ TwoChartIntegralModel.chartAlgInf A₀ ↥F₀ (⟨_, hjF₀⟩ : ↥F₀) := by
          apply TwoChartIntegralModel.adjoin_le_chartAlg
          exact sub_mem (one_mem _) (mul_mem (Subalgebra.algebraMap_mem _ a) (Algebra.subset_adjoin rfl))
        have hgeq : (1 - algebraMap A₀ ↥F₀ a * ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ : ↥F₀) = ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ * ((⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥F₀ a) := by
          rw [mul_sub, inv_mul_cancel₀ hJO.2, mul_comm]
        refine ⟨⟨_, hgmem⟩, ⟨?_, ?_⟩, ?_⟩
        · change (((1 - algebraMap A₀ ↥F₀ a * ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ : ↥F₀)) : ↥(fieldBar q M')) ∈ OSS s
          rw [hgeq, MulMemClass.coe_mul]
          exact mul_mem hinvS ha
        ·
          have : (⟨(((1 - algebraMap A₀ ↥F₀ a * ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ : ↥F₀)) : ↥(fieldBar q M')), by
              rw [hgeq, MulMemClass.coe_mul]; exact mul_mem hinvS ha⟩ : ↥(OSS s)) = ⟨_, hinvS⟩ * ⟨_, ha⟩ := by
            apply Subtype.ext
            change (((1 - algebraMap A₀ ↥F₀ a * ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ : ↥F₀)) : ↥(fieldBar q M')) = _ * _
            rw [hgeq, MulMemClass.coe_mul]
          rw [this]
          exact Ideal.mul_mem_left _ _ hamax
        · rw [h𝔫]
          change (1 - algebraMap A₀ ↥F₀ a * ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ : ↥F₀) ∉ V.nonunits
          have hn : algebraMap A₀ ↥F₀ a * ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ ∈ V.nonunits := by
            have h1 : ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹ ∈ V.nonunits := (V.inv_mem_nonunits_iff).mpr (Or.inr hjV)
            rw [ValuationSubring.mem_nonunits_iff] at h1 ⊢
            rw [map_mul]
            calc V.valuation (algebraMap A₀ ↥F₀ a) * V.valuation (((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹)
                ≤ 1 * V.valuation (((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹) := by
                  gcongr; exact (V.valuation_le_one_iff _).mpr (hconst a)
              _ < 1 := by rw [one_mul]; exact h1
          intro hg
          rw [ValuationSubring.mem_nonunits_iff] at hn hg
          have : V.valuation (1 - algebraMap A₀ ↥F₀ a * ((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹) = 1 := by
            rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left]
            · exact map_one _
            · rw [Valuation.map_neg, map_one]; exact hn
          rw [this] at hg
          exact lt_irrefl _ hg
      · exact Or.inr ⟨⟨((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀)⁻¹, TwoChartIntegralModel.subset_chartAlg A₀ ↥F₀ _ rfl⟩, hinvS⟩
    obtain ⟨𝔮, hLOC, hMIN, hINJ, hSURJ⟩ :=
      ModularCurve.FullLevel.exists_primes_chartAlg_localization_eq_igusaRing_minimal_injective_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀
        ({(⟨_, hjF₀⟩ : ↥F₀)⁻¹} : Set ↥F₀) (Or.inr rfl)
    have hGENFIB := ModularCurve.FullLevel.exists_valuationSubring_localization_chartAlg_of_not_mem_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ ({(⟨_, hjF₀⟩ : ↥F₀)⁻¹} : Set ↥F₀) (Or.inr rfl)
    exact ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_of_smooth_opens_chartAlgInf_descent_of_eq_two q hq2 M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ V hV hVlt hCV 𝔫 h𝔫max h𝔫 hnotSS 𝔮 hLOC hMIN hINJ hSURJ
      (fun 𝔭 h𝔭 h0 hϖ => hGENFIB 𝔭 h𝔭 h0 hϖ) U hxU hU

end S_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_gaussRing_descent_of_eq_two (solution)
