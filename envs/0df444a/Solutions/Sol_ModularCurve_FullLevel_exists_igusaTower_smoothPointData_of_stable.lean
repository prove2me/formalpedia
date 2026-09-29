-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_igusaTower_smoothPointData_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/20291f67-9715-5b41-b15b-fa1862be3592

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Theorems.Thm_ModularCurve_FullLevel_exists_igusaBaseModel_smoothPointStalks
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_smoothPointStalks_tower_of_base
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_and_henselianLocalRing_comap_of_finiteDimensional
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_igusaTower_smoothPointData_of_stable
p2m_attr_erase "instance" "AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent"
p2m_attr_erase "instance" "CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex ValuationSubring.instIsAlgClosedResidueField GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.TwoChart.isOpenImmersion_fInf ModularCurve.TwoChart.isOpenImmersion_ιFin ModularCurve.TwoChart.isOpenImmersion_ιInf ModularCurve.TwoChart.isOpenImmersion_fFin AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.quasiCompact_gluedToBase instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso AlgebraicCurve.SemistableModel.Descent.commRing AlgebraicCurve.SemistableModel.Descent.isNoetherianRing"
p2m_attr_erase "instance" "AlgebraicCurve.SemistableModel.Descent.isProper₀ AlgebraicCurve.SemistableModel.Descent.isIntegral₀ AlgebraicCurve.SemistableModel.isProper AlgebraicCurve.SemistableModel.flat AlgebraicCurve.SemistableModel.Descent.henselianLocalRing AlgebraicCurve.SemistableModel.locallyOfFinitePresentation AlgebraicCurve.SemistableModel.Descent.isLocalHom AlgebraicCurve.SemistableModel.Descent.isAlgebraic AlgebraicCurve.SemistableModel.Descent.isAlgebraic_F₀ AlgebraicCurve.SemistableModel.Descent.locallyOfFinitePresentation₀ AlgebraicCurve.SemistableModel.isIntegral AlgebraicCurve.SemistableModel.Descent.flat₀ AlgebraicCurve.SemistableModel.isClosedImmersion_specMap_residue kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime AlgebraicCurve.GaussReduction.isLocalHom_constToGauss"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ"
p2m_attr_erase "simp" "ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ"
p2m_attr_erase "simp" "ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"
p2m_attr_erase "simp" "ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.TwoChart.coe_jChartFin ModularCurve.TwoChart.ιFin_modelTo ModularCurve.TwoChart.ιInf_modelTo ModularCurve.TwoChart.ιInf_modelTo_assoc ModularCurve.TwoChart.coe_jInvChartInf ModularCurve.TwoChart.ιFin_modelTo_assoc AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.cuspCount_one WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_baseChangeRingHom ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty ModularCurve.coe_jqNGen"
p2m_attr_erase "simp" "AlgebraicCurve.SemistableModel.mk.injEq AlgebraicCurve.SemistableModel.mk.sizeOf_spec AlgebraicCurve.SemistableModel.Descent.mk.injEq AlgebraicCurve.SemistableModel.Descent.mk.sizeOf_spec AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers"

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups
open scoped Pointwise

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
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
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (hstab : ∀ τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), (∀ x : (AlgebraicClosure ℚ), x ∈ A ↔ τ x ∈ A) →
      ∀ x : (AlgebraicClosure ℚ), x ∈ k₀ → τ x ∈ k₀)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    {ι : Type} (K : ι → IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKfin : ∀ n, FiniteDimensional ↥k₀ ↥(K n))
    (An : ∀ n, ValuationSubring ↥(K n))
    (hAn : ∀ n (x : ↥(K n)), x ∈ An n ↔ (x : AlgebraicClosure ℚ) ∈ A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∃ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M'))
      (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))))
      (Sn : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → ι → Subring ↥(fieldBar q M'))
      (φn : (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) → (n : ι) → (Polynomial ↥(An n) →+* ↥(Sn Q n)))
      (χn : (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) → (n : ι) → (↥(Sn Q n) →+* ResidueField ↥A))
      (Dn : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → ι → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),

      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) ∧
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) ∧

      NIg.card = W.card ∧

      (∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ Q.toValuationSubring) ∧

      (∀ O : ValuationSubring ↥(fieldBar q M'), (∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x ∈ O) → O ≠ ⊤ → IsPrincipalIdealRing ↥O) ∧

      (∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg →
            (∀ n : ι,

              Function.Surjective (fun a : ↥(An n) => IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : AlgebraicClosure ℚ), (hAn n a).mp a.2⟩) ∧

              (∀ a : ↥(An n), algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ) ∈ Sn Q n) ∧

              (φn Q n).FormallySmooth ∧ (φn Q n).FormallyUnramified ∧

              (∀ a : ↥(An n), ((φn Q n (Polynomial.C a) : ↥(Sn Q n)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) ∧

              (∀ a : ↥(An n), χn Q n (φn Q n (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : AlgebraicClosure ℚ), (hAn n a).mp a.2⟩) ∧

              χn Q n (φn Q n Polynomial.X) = 0 ∧

              (∀ c : ↥(An n), IsLocalRing.residue ↥A ⟨((c : ↥(K n)) : AlgebraicClosure ℚ), (hAn n c).mp c.2⟩ = 0 →
                ∃! χ : ↥(Sn Q n) →+* ↥(An n), (∀ a : ↥(An n), χ (φn Q n (Polynomial.C a)) = a) ∧
                  (∀ f : ↥(Sn Q n), IsLocalRing.residue ↥A ⟨((χ f : ↥(K n)) : AlgebraicClosure ℚ), (hAn n _).mp (χ f).2⟩ = χn Q n f) ∧
                  χ (φn Q n Polynomial.X) = c) ∧

              (∀ f : ↥(Sn Q n), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
                IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                  algebraMap (ResidueField ↥A) Q.ResidueField (χn Q n f)) ∧

              (∃ hR : ((φn Q n Polynomial.X : ↥(Sn Q n)) : ↥(fieldBar q M')) ∈ R.integers,
                Q.ord (R.residue ⟨((φn Q n Polynomial.X : ↥(Sn Q n)) : ↥(fieldBar q M')), hR⟩) = 1) ∧

              (∀ P, P ∈ Dn Q n ↔ (P.IsRational ∧
                (∀ f : ↥(Sn Q n), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
                (∀ f : ↥(Sn Q n), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χn Q n f = 0))) ∧

              (∀ c : ↥(An n), φn Q n Polynomial.X ≠ φn Q n (Polynomial.C c)) ∧

              (∃ _ : IsLocalRing ↥(Sn Q n), ∀ f : ↥(Sn Q n), f ∈ IsLocalRing.maximalIdeal ↥(Sn Q n) ↔ χn Q n f = 0) ∧

              IsNoetherianRing ↥(Sn Q n) ∧ UniqueFactorizationMonoid ↥(Sn Q n) ∧

              (∀ f : ↥(fieldBar q M'), f ∈ Sn Q n → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
              (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥(Sn Q n), (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

              (∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
                LinearIndependent ↥(K n) c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) ∧

              (∃ ϖ : ↥(An n), IsLocalRing.maximalIdeal ↥(An n) = Ideal.span {ϖ} ∧ ϖ ≠ 0 ∧
                Prime (φn Q n (Polynomial.C ϖ)) ∧
                (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀ →
                  (f ∈ R.integers ↔ ∃ g h : ↥(Sn Q n), ¬ (φn Q n (Polynomial.C ϖ) ∣ h) ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M')))) ∧
                (∀ p : ↥(Sn Q n), Prime p → ¬ Associated p (φn Q n (Polynomial.C ϖ)) →
                  ∀ x : ↥(Sn Q n), ∃ r : Polynomial ↥(An n), r.Monic ∧ p ∣ (r.map ((φn Q n).comp Polynomial.C)).eval x)) ∧

              (∀ χ : ↥(Sn Q n) →+* ↥(An n), (∀ a : ↥(An n), χ (φn Q n (Polynomial.C a)) = a) →
                (∀ f : ↥(Sn Q n), IsLocalRing.residue ↥A ⟨((χ f : ↥(K n)) : AlgebraicClosure ℚ), (hAn n _).mp (χ f).2⟩ = χn Q n f) →
                RingHom.ker χ = Ideal.span {φn Q n Polynomial.X - φn Q n (Polynomial.C (χ (φn Q n Polynomial.X)))}) ∧

              (∃ G : Finset ↥(fieldBar q M'), ↑G ⊆ (Sn Q n : Set ↥(fieldBar q M')) ∧ ∀ f ∈ Sn Q n, ∃ g h : ↥(fieldBar q M'),
                g ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ)) ∧
                h ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ)) ∧
                (∃ u : (↥(Sn Q n))ˣ, ((u : ↥(Sn Q n)) : ↥(fieldBar q M')) = h) ∧ f * h = g)) ∧

            (∃ hmono : ∀ n n', K n ≤ K n' → Sn Q n ≤ Sn Q n',
              (∀ n n', K n ≤ K n' →
                Sn Q n' ≤ Subring.closure ((Sn Q n : Set ↥(fieldBar q M')) ∪ ((fun a : ↥(An n') => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n')) : AlgebraicClosure ℚ)) '' Set.univ))) ∧
              (∀ n n', ((φn Q n Polynomial.X : ↥(Sn Q n)) : ↥(fieldBar q M')) = ((φn Q n' Polynomial.X : ↥(Sn Q n')) : ↥(fieldBar q M'))) ∧
              (∀ n n' (h : K n ≤ K n') (f : ↥(Sn Q n)), χn Q n' ⟨(f : ↥(fieldBar q M')), hmono n n' h f.2⟩ = χn Q n f))) ∧

          (∀ Q Q' : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg → Q' ∉ NIg → ∀ (n : ι) (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ Dn Q n → P ∈ Dn Q' n → Q = Q') ∧

          (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),
              (R.resAut τ hτ • Q ∈ NIg ↔ Q ∈ NIg) ∧
              (Q ∉ NIg → ∀ n : ι, AlgebraicCurve.RegularProlongation.smulDisc τ (Dn Q n) = Dn (R.resAut τ hτ • Q) n)) ∧

          (∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ n : ι, (∀ x : AlgebraicClosure ℚ, x ∈ K n → τ x ∈ K n) →
            ∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg →
              (∀ f : ↥(fieldBar q M'), f ∈ Sn Q n ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f ∈ Sn Q n) ∧
              (∀ (f : ↥(Sn Q n)) (hf : ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : ↥(fieldBar q M')) ∈ Sn Q n),
                χn Q n ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : ↥(fieldBar q M')), hf⟩ = χn Q n f)) ∧

          (∀ g ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            (OIg (lineInfty q)).comap g.toAlgHom.toRingHom ≠ OIg (lineInfty q) →
              ∀ Q Q' : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg → Q' ∉ NIg → ∀ (n : ι) (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ Dn Q n → g • P ∉ Dn Q' n) ∧

          (∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg → ∀ (n : ι), ∀ P ∈ Dn Q n, ∀ s : ↥W, ¬ (((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
              (∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField A) M') →
                ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                  (⟨_, h⟩ : A) ∈ maximalIdeal A)) ∧
            ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
              (∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jNGeomGen (ResidueField A) M') →
                ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                  (⟨_, h⟩ : A) ∈ maximalIdeal A)))) ∧

          (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'),
            (∀ s : ↥W, ¬ (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
                (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                  0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
                (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                  ∀ a : A, residue A a =
                      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                    ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                      (⟨_, h⟩ : A) ∈ maximalIdeal A)) →
            ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ ∃ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg ∧ ∀ n : ι, levelAutBar q M' ζ γ • P ∈ Dn Q n) ∧

          (∃ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P.toValuationSubring = qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M') ∧
            ∃ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg ∧ ∀ n : ι, P ∈ Dn Q n) := by
  classical
  haveI hQalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by convert AlgebraicClosure.isAlgebraic ℚ; rfl; rfl
  have hcurve : IsCurveOver (AlgebraicClosure ℚ) ↥(fieldBar q M') :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
      (AlgebraicClosure ℚ) (q ^ 2 * M') (levelH q M')).1

  obtain ⟨hdvr_b, hhens_b⟩ :=
    ValuationSubring.isDiscreteValuationRing_and_henselianLocalRing_comap_of_finiteDimensional
      (F := ℚ) (E := AlgebraicClosure ℚ) hQalg A k₀ hdvr hhens (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) inferInstance
  haveI := hdvr_b
  haveI := hhens_b

  obtain ⟨F₀, NIg, S, φ, χ, D, hK1, hF₀st, hcard, hN, hdvrF, hLD, hQ, hdisj, heqv, hγ, hH1, hH2, hδ, hcusp⟩ :=
    ModularCurve.FullLevel.exists_igusaBaseModel_smoothPointStalks q hq M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS
      hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr R hR hR₀O π hπ hπP
      k₀ π₀ hπ₀ hdvr hunif hhens hres hκ ℓ hℓ hℓ3 hℓq hℓM' ζ₀ hζ₀ ϖt hϖtA hϖt
      (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) inferInstance (A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) (fun _ => Iff.rfl)

  have hAeq : ∀ n, An n = A.comap (algebraMap ↥(K n) (AlgebraicClosure ℚ)) := fun n => by
    ext x; exact hAn n x
  have hlay := fun n =>
    ValuationSubring.isDiscreteValuationRing_and_henselianLocalRing_comap_of_finiteDimensional
      (F := ℚ) (E := AlgebraicClosure ℚ) hQalg A k₀ hdvr hhens (K n) (hKfin n)
  have hdvrn : ∀ n, IsDiscreteValuationRing ↥(An n) := fun n => by rw [hAeq]; exact (hlay n).1
  have hhensn : ∀ n, HenselianLocalRing ↥(An n) := fun n => by rw [hAeq]; exact (hlay n).2
  have hκn : ∀ n, Function.Surjective
      (fun a : ↥(An n) => IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : AlgebraicClosure ℚ), (hAn n a).mp a.2⟩) := by
    intro n y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨c, hcA, h, hm⟩ := hκ a a.2
    refine ⟨⟨⟨(c : AlgebraicClosure ℚ), (K n).algebraMap_mem c⟩, (hAn n _).mpr hcA⟩, ?_⟩
    change IsLocalRing.residue ↥A ⟨(c : AlgebraicClosure ℚ), hcA⟩ = IsLocalRing.residue ↥A a
    rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hm

  have hunifb : ∃ ϖ : ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))),
      IsLocalRing.maximalIdeal _ = Ideal.span {ϖ} ∧ ϖ ≠ 0 := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)))
    exact ⟨ϖ, hϖ.maximalIdeal_eq, hϖ.ne_zero⟩
  have halgb : ∀ x : AlgebraicClosure ℚ, IsAlgebraic ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) x := fun x =>
    ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral.tower_top (A := ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)))).isAlgebraic
  have key := fun Q (hQn : Q ∉ NIg) =>
    @AlgebraicCurve.RegularProlongation.exists_smoothPointStalks_tower_of_base
      ↥k₀ (AlgebraicClosure ℚ) ↥(fieldBar q M') _ _ _ _ _ _ _ hcurve A _ _ _ R (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) halgb
      (A.comap (algebraMap ↥(⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ))) (fun _ => Iff.rfl) (hQ Q hQn).1 (S Q) (φ Q) (χ Q)
      (hQ Q hQn).2.1 (hQ Q hQn).2.2.1 (hQ Q hQn).2.2.2.1 (hQ Q hQn).2.2.2.2.1 _ _
      hunifb.choose hunifb.choose_spec.1 hunifb.choose_spec.2 (hQ Q hQn).2.2.2.2.2.1.choose (hQ Q hQn).2.2.2.2.2.1.choose_spec
      (hQ Q hQn).2.2.2.2.2.2.1 (hQ Q hQn).2.2.2.2.2.2.2.1 (hQ Q hQn).2.2.2.2.2.2.2.2.1 (hQ Q hQn).2.2.2.2.2.2.2.2.2.2.2.1.choose ((hQ Q hQn).2.2.2.2.2.2.2.2.2.2.2.1.choose_spec hunifb.choose hunifb.choose_spec.1)
      Q inferInstance (D Q) (hQ Q hQn).2.2.2.2.2.2.2.2.2.2.2.2.2.2 (hQ Q hQn).2.2.2.2.2.2.2.2.2.2.2.2.1 (hQ Q hQn).2.2.2.2.2.2.2.2.2.2.2.2.2.1
      ι K (fun n => bot_le) hKfin An hAn hκn hdvrn hhensn F₀ hK1 (hQ Q hQn).2.2.2.2.2.2.2.2.2.1 (hQ Q hQn).2.2.2.2.2.2.2.2.2.2.1 hLD

  have tot := fun Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) =>
    if hQn : Q ∉ NIg then
      Exists.imp (fun _ => Exists.imp fun _ => Exists.imp fun _ => fun h (_ : Q ∉ NIg) => h) (key Q hQn)
    else by
      refine ⟨fun n => ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp
          ((algebraMap ↥(K n) (AlgebraicClosure ℚ)).comp (An n).subtype)).range,
        fun n => ?_, fun n => ?_, fun h => absurd h hQn⟩
      · let f : ↥(An n) →+* ↥(fieldBar q M') :=
          (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp ((algebraMap ↥(K n) (AlgebraicClosure ℚ)).comp (An n).subtype)
        exact f.rangeRestrict.comp (Polynomial.evalRingHom 0)
      · let f : ↥(An n) →+* ↥(fieldBar q M') :=
          (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp ((algebraMap ↥(K n) (AlgebraicClosure ℚ)).comp (An n).subtype)
        have hf : Function.Injective f :=
          (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).injective.comp
            ((algebraMap ↥(K n) (AlgebraicClosure ℚ)).injective.comp Subtype.val_injective)
        let e : ↥(An n) ≃+* ↥f.range :=
          RingEquiv.ofBijective f.rangeRestrict ⟨fun a b hab => hf (congrArg Subtype.val hab), f.rangeRestrict_surjective⟩
        let ιA : ↥(An n) →+* ↥A := ((algebraMap ↥(K n) (AlgebraicClosure ℚ)).comp (An n).subtype).codRestrict A.toSubring
          (fun a => (hAn n a).mp a.2)
        exact ((IsLocalRing.residue ↥A).comp ιA).comp e.symm.toRingHom
  choose Sn φn χn hT using tot
  refine ⟨F₀, NIg, Sn, φn, χn, fun Q _ => D Q, hK1, hF₀st, hcard, hN, hdvrF, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q hQn
    exact ⟨(hT Q hQn).2.1, (hT Q hQn).2.2⟩
  · intro Q Q' hQn hQn' n P
    exact hdisj Q Q' hQn hQn' P
  · intro τ hτ hτR Q
    exact ⟨(heqv τ hτ hτR Q).1, fun hQn n => (heqv τ hτ hτR Q).2 hQn⟩
  ·
    intro τ hτ n hKn Q hQn

    have hτA : ∀ x : AlgebraicClosure ℚ, x ∈ A ↔ τ x ∈ A := by
      obtain ⟨σ, -, rfl⟩ := Subgroup.mem_map.mp hτ
      have hfix : (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • A = A := MulAction.mem_stabilizer_iff.mp σ.2
      intro x
      constructor
      · intro hx
        have := ValuationSubring.smul_mem_pointwise_smul (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) x A hx
        rwa [hfix] at this
      · intro hx
        have hfix' : (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)⁻¹ • A = A := inv_smul_eq_iff.mpr hfix.symm
        have := ValuationSubring.smul_mem_pointwise_smul ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)⁻¹) _ A hx
        rw [hfix'] at this
        simpa [AlgEquiv.smul_def] using this
    have hbot : ∀ x : AlgebraicClosure ℚ, x ∈ (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) → τ x ∈ (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) := by
      intro x hx
      rw [IntermediateField.mem_bot] at hx ⊢
      obtain ⟨c, rfl⟩ := hx
      exact ⟨⟨τ (c : AlgebraicClosure ℚ), hstab τ hτA _ c.2⟩, rfl⟩
    obtain ⟨hSst, hχst⟩ := hγ τ hτ hbot Q hQn
    obtain ⟨hmono₁, hgen₁, -, hχ₁⟩ := (hT Q hQn).1
    have hblk := (hT Q hQn).2.1 n
    have hASn : ∀ a : ↥(An n), algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ) ∈ Sn Q n :=
      hblk.2.1
    have hχCn : ∀ a : ↥(An n), χn Q n (φn Q n (Polynomial.C a)) =
        IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : AlgebraicClosure ℚ), (hAn n a).mp a.2⟩ := hblk.2.2.2.2.2.1
    have hφCn : ∀ a : ↥(An n), ((φn Q n (Polynomial.C a) : ↥(Sn Q n)) : ↥(fieldBar q M')) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ) := hblk.2.2.2.2.1

    have hpin : Sn Q n = Subring.closure (((S Q) : Set ↥(fieldBar q M')) ∪
        ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ)) := by
      refine le_antisymm (hgen₁ n) (Subring.closure_le.mpr ?_)
      rintro f (hf | ⟨a, -, rfl⟩)
      · exact hmono₁ n hf
      · exact hASn a

    have hgconst : ∀ x : AlgebraicClosure ℚ,
        ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x =
          algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (τ x) := fun x => by
      rw [AlgebraicCurve.SemilinearAut.smul_algebraMap]
      rfl

    have hfwd : ∀ (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), σ' ∈ A.inertiaSubgroupIn ℚ →
        (∀ x : AlgebraicClosure ℚ, x ∈ A ↔ σ' x ∈ A) →
        (∀ x : AlgebraicClosure ℚ, x ∈ K n → σ' x ∈ K n) →
        ∀ f : ↥(fieldBar q M'), f ∈ Sn Q n →
          ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) σ' • f ∈ Sn Q n := by
      intro σ' hσ' hσ'A hσ'K f hf
      have hbot' : ∀ x : AlgebraicClosure ℚ, x ∈ (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) → σ' x ∈ (⊥ : IntermediateField ↥k₀ (AlgebraicClosure ℚ)) := by
        intro x hx
        rw [IntermediateField.mem_bot] at hx ⊢
        obtain ⟨c, rfl⟩ := hx
        exact ⟨⟨σ' (c : AlgebraicClosure ℚ), hstab σ' hσ'A _ c.2⟩, rfl⟩
      have hSst' := (hγ σ' hσ' hbot' Q hQn).1
      rw [hpin] at hf ⊢
      have hle : Subring.closure (((S Q) : Set ↥(fieldBar q M')) ∪
            ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ)) ≤
          (Subring.closure (((S Q) : Set ↥(fieldBar q M')) ∪
            ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ))).comap
            (MulSemiringAction.toRingHom _ ↥(fieldBar q M')
              (ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) σ')) := by
        refine Subring.closure_le.mpr ?_
        rintro x (hx | ⟨a, -, rfl⟩)
        · rw [SetLike.mem_coe, Subring.mem_comap, MulSemiringAction.toRingHom_apply]
          exact Subring.subset_closure (Or.inl ((hSst' x).mp hx))
        · rw [SetLike.mem_coe, Subring.mem_comap, MulSemiringAction.toRingHom_apply, AlgebraicCurve.SemilinearAut.smul_algebraMap]
          refine Subring.subset_closure (Or.inr ⟨⟨⟨σ' ((a : ↥(K n)) : AlgebraicClosure ℚ), hσ'K _ (a : ↥(K n)).2⟩,
            (hAn n _).mpr ((hσ'A _).mp ((hAn n a).mp a.2))⟩, Set.mem_univ _, ?_⟩)
          rfl
      have := hle hf
      rwa [Subring.mem_comap, MulSemiringAction.toRingHom_apply] at this

    have hKn' : ∀ x : AlgebraicClosure ℚ, x ∈ K n → τ⁻¹ x ∈ K n := by
      intro x hx
      have hint : IsIntegral ℚ x := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral
      have hfin : ((minpoly ℚ x).rootSet (AlgebraicClosure ℚ) ∩ (K n : Set (AlgebraicClosure ℚ))).Finite := (Polynomial.rootSet_finite _ _).inter_of_left _
      have hmaps : Set.MapsTo τ ((minpoly ℚ x).rootSet (AlgebraicClosure ℚ) ∩ (K n : Set (AlgebraicClosure ℚ))) ((minpoly ℚ x).rootSet (AlgebraicClosure ℚ) ∩ (K n : Set (AlgebraicClosure ℚ))) := by
        intro y hy
        refine ⟨?_, hKn _ hy.2⟩
        have hy1 := hy.1
        rw [Polynomial.mem_rootSet] at hy1 ⊢
        refine ⟨hy1.1, ?_⟩
        have h : Polynomial.aeval (τ y) (minpoly ℚ x) = τ (Polynomial.aeval y (minpoly ℚ x)) :=
          Polynomial.aeval_algHom_apply (τ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ) y (minpoly ℚ x)
        rw [h, hy1.2, map_zero]
      have hinj : Set.InjOn τ ((minpoly ℚ x).rootSet (AlgebraicClosure ℚ) ∩ (K n : Set (AlgebraicClosure ℚ))) := fun a _ b _ h => τ.injective h
      have hsurj : Set.SurjOn τ ((minpoly ℚ x).rootSet (AlgebraicClosure ℚ) ∩ (K n : Set (AlgebraicClosure ℚ))) ((minpoly ℚ x).rootSet (AlgebraicClosure ℚ) ∩ (K n : Set (AlgebraicClosure ℚ))) := ((hfin.injOn_iff_bijOn_of_mapsTo hmaps).mp hinj).surjOn
      have hxR : x ∈ ((minpoly ℚ x).rootSet (AlgebraicClosure ℚ) ∩ (K n : Set (AlgebraicClosure ℚ))) :=
        ⟨by rw [Polynomial.mem_rootSet]; exact ⟨minpoly.ne_zero hint, minpoly.aeval ℚ x⟩, hx⟩
      obtain ⟨y, hy, hyx⟩ := hsurj hxR
      have : τ⁻¹ x = y := by rw [← hyx]; exact τ.symm_apply_apply y
      rw [this]; exact hy.2
    have hτ' : τ⁻¹ ∈ A.inertiaSubgroupIn ℚ := Subgroup.inv_mem _ hτ
    have hτA' : ∀ x : AlgebraicClosure ℚ, x ∈ A ↔ τ⁻¹ x ∈ A := fun x => by
      rw [hτA (τ⁻¹ x)]; simp
    refine ⟨fun f => ⟨hfwd τ hτ hτA hKn f, fun hf => ?_⟩, fun f hf => ?_⟩
    · have := hfwd τ⁻¹ hτ' hτA' hKn' _ hf
      rw [map_inv, inv_smul_smul] at this
      exact this
    ·
      obtain ⟨σ, hσI, hστ⟩ := Subgroup.mem_map.mp hτ
      have hresτ : ∀ (x : AlgebraicClosure ℚ) (hx : x ∈ A) (hx' : τ x ∈ A),
          IsLocalRing.residue ↥A ⟨τ x, hx'⟩ = IsLocalRing.residue ↥A ⟨x, hx⟩ := by
        intro x hx hx'
        have hk : MulSemiringAction.toRingAut (↥(A.decompositionSubgroup ℚ)) (ResidueField ↥A) σ = 1 := by
          simpa [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] using hσI
        have h1 : (⟨τ x, hx'⟩ : ↥A) = σ • (⟨x, hx⟩ : ↥A) := Subtype.ext (by subst hστ; rfl)
        have h2 := RingEquiv.congr_fun hk (IsLocalRing.residue ↥A ⟨x, hx⟩)
        rw [h1, IsLocalRing.ResidueField.residue_smul]
        exact h2
      have hCle : Subring.closure (((S Q) : Set ↥(fieldBar q M')) ∪
            ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ)) ≤ Sn Q n := le_of_eq hpin.symm
      have hfwdC : ∀ x, x ∈ Subring.closure (((S Q) : Set ↥(fieldBar q M')) ∪
            ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ)) → ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • x ∈ Sn Q n := fun x h => hfwd τ hτ hτA hKn x (hCle h)
      have key2 : ∀ (x : ↥(fieldBar q M')) (h : x ∈ Subring.closure (((S Q) : Set ↥(fieldBar q M')) ∪
            ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ))),
          χn Q n ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • x, hfwdC x h⟩ = χn Q n ⟨x, hCle h⟩ := by
        intro x h
        refine Subring.closure_induction
          (p := fun x h => χn Q n ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • x, hfwdC x h⟩ = χn Q n ⟨x, hCle h⟩) ?_ ?_ ?_ ?_ ?_ ?_ h
        · rintro x (hxS | ⟨a, -, rfl⟩)
          · have e1 : χn Q n ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • x, hfwdC x (Subring.subset_closure (Or.inl hxS))⟩ =
                χ Q ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • x, (hSst x).mp hxS⟩ := hχ₁ n ⟨_, (hSst x).mp hxS⟩
            have e2 : χn Q n ⟨x, hCle (Subring.subset_closure (Or.inl hxS))⟩ = χ Q ⟨x, hxS⟩ := hχ₁ n ⟨x, hxS⟩
            rw [e1, e2]
            exact hχst ⟨x, hxS⟩ _
          · have hτaK : τ ((a : ↥(K n)) : AlgebraicClosure ℚ) ∈ K n := hKn _ (a : ↥(K n)).2
            have hτaA : τ ((a : ↥(K n)) : AlgebraicClosure ℚ) ∈ A := (hτA _).mp ((hAn n a).mp a.2)
            have e1 : (⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ),
                  hfwdC _ (Subring.subset_closure (Or.inr ⟨a, Set.mem_univ _, rfl⟩))⟩ : ↥(Sn Q n)) =
                φn Q n (Polynomial.C (⟨⟨τ ((a : ↥(K n)) : AlgebraicClosure ℚ), hτaK⟩, (hAn n _).mpr hτaA⟩ : ↥(An n))) := by
              apply Subtype.ext
              show ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ) = _
              rw [hφCn, AlgebraicCurve.SemilinearAut.smul_algebraMap]
              rfl
            have e2 : (⟨algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ),
                  hCle (Subring.subset_closure (Or.inr ⟨a, Set.mem_univ _, rfl⟩))⟩ : ↥(Sn Q n)) =
                φn Q n (Polynomial.C a) := Subtype.ext (hφCn a).symm
            rw [e1, e2, hχCn, hχCn]
            exact hresτ _ _ _
        · have e : (⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (0 : ↥(fieldBar q M')), hfwdC 0 (Subring.zero_mem _)⟩ : ↥(Sn Q n)) = 0 :=
            Subtype.ext (smul_zero _)
          rw [e, map_zero]
          exact (map_zero (χn Q n)).symm
        · have e : (⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (1 : ↥(fieldBar q M')), hfwdC 1 (Subring.one_mem _)⟩ : ↥(Sn Q n)) = 1 :=
            Subtype.ext (smul_one _)
          rw [e, map_one]
          exact (map_one (χn Q n)).symm
        · intro x y hx hy ihx ihy
          have e : (⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (x + y), hfwdC _ (Subring.add_mem _ hx hy)⟩ : ↥(Sn Q n)) =
              ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • x, hfwdC x hx⟩ + ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • y, hfwdC y hy⟩ := Subtype.ext (smul_add _ _ _)
          have e' : (⟨x + y, hCle (Subring.add_mem _ hx hy)⟩ : ↥(Sn Q n)) = ⟨x, hCle hx⟩ + ⟨y, hCle hy⟩ := rfl
          rw [e, e', map_add, map_add, ihx, ihy]
        · intro x hx ihx
          have e : (⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (-x), hfwdC _ (Subring.neg_mem _ hx)⟩ : ↥(Sn Q n)) = -⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • x, hfwdC x hx⟩ :=
            Subtype.ext (smul_neg _ _)
          have e' : (⟨-x, hCle (Subring.neg_mem _ hx)⟩ : ↥(Sn Q n)) = -⟨x, hCle hx⟩ := rfl
          rw [e, e', map_neg, map_neg, ihx]
        · intro x y hx hy ihx ihy
          have e : (⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (x * y), hfwdC _ (Subring.mul_mem _ hx hy)⟩ : ↥(Sn Q n)) =
              ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • x, hfwdC x hx⟩ * ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • y, hfwdC y hy⟩ := Subtype.ext (smul_mul' _ _ _)
          have e' : (⟨x * y, hCle (Subring.mul_mem _ hx hy)⟩ : ↥(Sn Q n)) = ⟨x, hCle hx⟩ * ⟨y, hCle hy⟩ := rfl
          rw [e, e', map_mul, map_mul, ihx, ihy]
      exact key2 (f : ↥(fieldBar q M')) (hpin ▸ f.2)
  · intro g hg hmv Q Q' hQn hQn' n P
    exact hH1 g hg hmv Q Q' hQn hQn' P
  · intro Q hQn n P hP s
    exact hH2 Q hQn P hP s
  · intro P hP
    obtain ⟨γ, hγ, Q, hQn, h⟩ := hδ P hP
    exact ⟨γ, hγ, Q, hQn, fun _ => h⟩
  · obtain ⟨P, hPq, Q, hQn, h⟩ := hcusp
    exact ⟨P, hPq, Q, hQn, fun _ => h⟩

end S_ModularCurve_FullLevel_exists_igusaTower_smoothPointData_of_stable
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_igusaTower_smoothPointData_of_stable (solution)
