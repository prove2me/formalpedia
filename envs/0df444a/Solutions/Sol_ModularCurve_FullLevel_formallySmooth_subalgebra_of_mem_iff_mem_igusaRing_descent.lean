-- Prove2me | solution 1 for ModularCurve.FullLevel.formallySmooth_subalgebra_of_mem_iff_mem_igusaRing_descent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/b8619f51-2efe-576e-aa7f-0e3f8890f334

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_ModularCurve_FullLevel_exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_igusaRing_descent_local
import Theorems.Thm_ModularCurve_FullLevel_exists_jInvariant_sub_mem_maximalIdeal_drinfeldRing_descent
import Theorems.Thm_ModularCurve_FullLevel_isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss
import Theorems.Thm_ModularCurve_FullLevel_exists_regularProlongation_integers_eq_igusaGaussRing
import Theorems.Thm_ModularCurve_FullLevel_exists_admissible_smallConstants_of_descentBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_formallySmooth_subalgebra_of_mem_iff_mem_igusaRing_descent
p2m_attr_erase "instance" "AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod"
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin ModularCurve.instTowerRatLBaseChange ModularCurve.instTowerRatF₀BaseChange"
p2m_attr_erase "instance" "ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex AdicCompletion.instIsLocalRingMaximalIdeal ModularCurve.DRModelPackage.smoothLocus_relDim ModularCurve.DRModelPackage.eη_iso ModularCurve.DRModelPackage.e₀_iso ValuationSubring.instIsAlgClosedResidueField ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap"
p2m_attr_erase "simp" "KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"
p2m_attr_erase "simp" "WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"
p2m_attr_erase "simp" "FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.cuspCount_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU"
p2m_attr_erase "simp" "ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_baseChangeRingHom ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply AdicCompletion.map_smul_of AdicCompletion.algebraMap_of"
p2m_attr_erase "simp" "AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul ModularCurve.DRModelPackage.mk.sizeOf_spec ModularCurve.DRModelPackage.mk.injEq AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty ModularCurve.coe_jqNGen ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq"

set_option autoImplicit false

p2m_open "AlgebraicCurve~TwoChartIntegralModel ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open CategoryTheory AlgebraicGeometry
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace E150G

p2m_open "Polynomial AlgebraicGeometry.Polynomial IsLocalRing"

variable {K : Type*} [Field K]

private def _root_.E150G.comp (O : ValuationSubring K) (W : ValuationSubring (ResidueField O)) : ValuationSubring K where
  carrier := {x | ∃ h : x ∈ O, residue O ⟨x, h⟩ ∈ W}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e : (⟨a * b, mul_mem ha hb⟩ : O) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [e, map_mul]; exact mul_mem ha' hb'
  one_mem' := ⟨one_mem O, by rw [show (⟨1, one_mem O⟩ : O) = 1 from rfl, map_one]; exact one_mem W⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨add_mem ha hb, ?_⟩
    have e : (⟨a + b, add_mem ha hb⟩ : O) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [e, map_add]; exact add_mem ha' hb'
  zero_mem' := ⟨zero_mem O, by rw [show (⟨0, zero_mem O⟩ : O) = 0 from rfl, map_zero]; exact zero_mem W⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨neg_mem ha, ?_⟩
    have e : (⟨-a, neg_mem ha⟩ : O) = -⟨a, ha⟩ := rfl
    rw [e, map_neg]; exact neg_mem ha'
  mem_or_inv_mem' := by
    intro x
    by_cases hx : x ∈ O
    · by_cases hx' : residue O ⟨x, hx⟩ ∈ W
      · exact Or.inl ⟨hx, hx'⟩
      · right
        have hx0 : residue O ⟨x, hx⟩ ≠ 0 := fun h => hx' (h ▸ W.zero_mem)
        have hunit : IsUnit (⟨x, hx⟩ : O) := (residue_ne_zero_iff_isUnit _).mp hx0
        obtain ⟨u, hu⟩ := hunit
        have hxK : x ≠ 0 := by
          rintro rfl; apply hx0; rw [show (⟨(0:K), hx⟩ : O) = 0 from rfl, map_zero]
        have hinvO : x⁻¹ ∈ O := by
          have : ((u⁻¹ : Oˣ) : O) * (u : O) = 1 := u.inv_mul
          have h2 : (((u⁻¹ : Oˣ) : O) : K) * x = 1 := by
            have := congrArg (fun t : O => (t : K)) this; rw [hu] at this; simpa using this
          exact (inv_eq_of_mul_eq_one_left h2) ▸ ((u⁻¹ : Oˣ) : O).2
        refine ⟨hinvO, ?_⟩
        have hprod : residue O ⟨x, hx⟩ * residue O ⟨x⁻¹, hinvO⟩ = 1 := by
          rw [← map_mul]
          have : (⟨x, hx⟩ : O) * ⟨x⁻¹, hinvO⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hxK)
          rw [this, map_one]
        rw [show residue O ⟨x⁻¹, hinvO⟩ = (residue O ⟨x, hx⟩)⁻¹ from (inv_eq_of_mul_eq_one_right hprod).symm]
        exact (W.mem_or_inv_mem _).resolve_left hx'
    · right
      have hinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hx
      refine ⟨hinv, ?_⟩
      have hnu : ¬ IsUnit (⟨x⁻¹, hinv⟩ : O) := by
        intro hu
        obtain ⟨u, hu⟩ := hu
        apply hx
        have : ((u⁻¹ : Oˣ) : O) * (u : O) = 1 := u.inv_mul
        have h2 : (((u⁻¹ : Oˣ) : O) : K) * x⁻¹ = 1 := by
          have := congrArg (fun t : O => (t : K)) this; rw [hu] at this; simpa using this
        have hx0 : x ≠ 0 := by rintro rfl; simp at h2
        have : x = (((u⁻¹ : Oˣ) : O) : K) := by
          have := congrArg (· * x) h2; simp [mul_assoc, inv_mul_cancel₀ hx0] at this; exact this.symm
        rw [this]; exact ((u⁻¹ : Oˣ) : O).2
      rw [show residue O ⟨x⁻¹, hinv⟩ = 0 from (residue_eq_zero_iff _).mpr hnu]
      exact W.zero_mem

p2m_export "E150G" "comp"
theorem comp_le (O : ValuationSubring K) (W : ValuationSubring (ResidueField O)) : comp O W ≤ O :=
  fun _ ⟨h, _⟩ => h

theorem mem_comp_iff (O : ValuationSubring K) (W : ValuationSubring (ResidueField O)) (x : K) :
    x ∈ comp O W ↔ ∃ h : x ∈ O, residue O ⟨x, h⟩ ∈ W := Iff.rfl

theorem exists_le_inv_mem_nonunits (O : ValuationSubring K) {A' : Type*} [CommRing A'] [IsLocalRing A']
    [IsAlgClosed (ResidueField A')]
    (c : A' →+* ↥O) (hc : ∀ a ∈ maximalIdeal A', c a ∈ maximalIdeal ↥O)
    (x : ↥O) (hx : ∀ a : A', IsUnit (x - c a)) :
    ∃ V : ValuationSubring K, V ≤ O ∧ (∀ a : A', ((c a : ↥O) : K) ∈ V) ∧ (x : K)⁻¹ ∈ V.nonunits ∧ (x : K) ∉ V := by
  classical
  set κ := ResidueField ↥O
  let k := ResidueField A'
  have hker : ∀ a ∈ maximalIdeal A', ((residue ↥O).comp c) a = 0 := fun a ha => by
    rw [RingHom.comp_apply, residue_eq_zero_iff]; exact hc a ha
  let ψ : k →+* κ := Ideal.Quotient.lift (maximalIdeal A') ((residue ↥O).comp c) hker
  have hψ : ∀ a : A', ψ (residue A' a) = residue ↥O (c a) := fun a => rfl
  letI : Algebra k κ := ψ.toAlgebra
  set r : κ := residue ↥O x with hr

  have hr_notmem : ∀ a : k, r ≠ ψ a := by
    intro a h
    obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h' : r = residue ↥O (c a₀) := h
    have : residue ↥O (x - c a₀) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr h'
    exact (residue_eq_zero_iff _ |>.mp this) (hx a₀)

  have hr_tr : Transcendental k r := by
    intro halg
    have hint : IsIntegral k r := halg.isIntegral
    have h1 : (minpoly k r).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    have hq : (minpoly k r).leadingCoeff = 1 := (minpoly.monic hint).leadingCoeff
    have h0 : aeval r (minpoly k r) = 0 := minpoly.aeval k r
    rw [eq_X_add_C_of_degree_eq_one h1, hq, C_1, one_mul, aeval_add, aeval_X, aeval_C,
      add_eq_zero_iff_eq_neg] at h0
    apply hr_notmem (-(minpoly k r).coeff 0)
    rw [map_neg]; exact h0
  have hr0 : r ≠ 0 := fun h => hr_notmem 0 (by rw [h, map_zero])
  have hri_tr : Transcendental k r⁻¹ := fun h => hr_tr (by have := h.inv; rwa [inv_inv] at this)
  have hinj : Function.Injective (aeval (R := k) r⁻¹) := transcendental_iff_injective.mp hri_tr

  let R : Subring κ := (aeval (R := k) r⁻¹).toRingHom.range
  have hrR : r⁻¹ ∈ R := ⟨X, by simp⟩
  let I : Ideal ↥R := Ideal.span {⟨r⁻¹, hrR⟩}
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : ↥R) ∈ I := htop ▸ Submodule.mem_top
    rw [Ideal.mem_span_singleton] at h1
    obtain ⟨y, hy⟩ := h1
    obtain ⟨p, hp⟩ := y.2
    have hval : r⁻¹ * aeval r⁻¹ p = 1 := by
      have := congrArg Subtype.val hy
      simp only [Subring.coe_mul, OneMemClass.coe_one] at this
      have hp' : (y : κ) = aeval r⁻¹ p := by rw [← hp]; rfl
      rw [← hp']; exact this.symm
    have : aeval (R := k) r⁻¹ (X * p - 1) = 0 := by
      rw [map_sub, map_mul, aeval_X, map_one, hval, sub_self]
    have hzero : (X * p - 1 : k[X]) = 0 := hinj (by rw [this, map_zero])
    have := congrArg (Polynomial.eval 0) hzero
    simp at this
  obtain ⟨W, hRW, hIW⟩ := Ideal.image_subset_nonunits_valuationSubring I hI
  have hrW : r⁻¹ ∈ W.nonunits := hIW ⟨⟨r⁻¹, hrR⟩, Ideal.subset_span rfl, rfl⟩
  have hrW' : r ∉ W := by
    have := (W.inv_mem_nonunits_iff).mp hrW
    exact this.elim (fun h => (hr0 h).elim) id

  refine ⟨comp O W, comp_le O W, ?_, ?_, ?_⟩
  · intro a
    refine ⟨(c a).2, ?_⟩
    have : residue ↥O ⟨((c a : ↥O) : K), (c a).2⟩ = ψ (residue A' a) := by
      rw [hψ]
    rw [this]
    exact hRW ⟨C (residue A' a), by simp [RingHom.algebraMap_toAlgebra]⟩
  ·
    have hxu : IsUnit x := by
      have := hx 0; rwa [map_zero, sub_zero] at this
    obtain ⟨u, hu⟩ := hxu
    have hxinvO : (x : K)⁻¹ ∈ O := by
      have h2 : (((u⁻¹ : (↥O)ˣ) : ↥O) : K) * (x : K) = 1 := by
        have := congrArg (fun t : ↥O => (t : K)) u.inv_mul; rw [hu] at this; simpa using this
      exact (inv_eq_of_mul_eq_one_left h2) ▸ ((u⁻¹ : (↥O)ˣ) : ↥O).2
    rw [ValuationSubring.mem_nonunits_iff_or]
    right
    rw [inv_inv]
    intro hxV
    obtain ⟨_, hres⟩ := (mem_comp_iff O W _).mp hxV
    apply hrW'
    convert hres using 2
  · intro hxV
    obtain ⟨_, hres⟩ := (mem_comp_iff O W _).mp hxV
    apply hrW'
    convert hres using 2

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem formallySmooth_of_le_of_localization {A₀ F : Type*} [CommRing A₀] [Field F] [Algebra A₀ F]
    (B : Subalgebra A₀ F) (𝔪 𝔮 : Ideal ↥B) [𝔪.IsPrime] [𝔮.IsPrime] (hqm : 𝔮 ≤ 𝔪)
    (hsm : (algebraMap A₀ (Localization.AtPrime 𝔪)).FormallySmooth)
    (S : Subalgebra A₀ F) (hS : ∀ x : F, x ∈ S ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : F) = (b : F)) :
    Algebra.FormallySmooth A₀ ↥S := by
  classical
  have hBinj : ∀ b : ↥B, (b : F) = 0 → b = 0 := fun b hb => Subtype.ext hb

  have hunits : ∀ y : 𝔪.primeCompl, IsUnit (algebraMap ↥B (Localization.AtPrime 𝔮) y) := fun y =>
    IsLocalization.map_units (M := 𝔮.primeCompl) (Localization.AtPrime 𝔮) ⟨y.1, fun hy => y.2 (hqm hy)⟩
  let g : Localization.AtPrime 𝔪 →+* Localization.AtPrime 𝔮 := IsLocalization.lift (M := 𝔪.primeCompl) hunits
  letI : Algebra (Localization.AtPrime 𝔪) (Localization.AtPrime 𝔮) := g.toAlgebra
  haveI : IsScalarTower ↥B (Localization.AtPrime 𝔪) (Localization.AtPrime 𝔮) :=
    IsScalarTower.of_algebraMap_eq (R := ↥B) (S := Localization.AtPrime 𝔪) (A := Localization.AtPrime 𝔮)
      (fun b => (IsLocalization.lift_eq hunits b).symm)
  haveI : IsScalarTower A₀ (Localization.AtPrime 𝔪) (Localization.AtPrime 𝔮) :=
    IsScalarTower.of_algebraMap_eq (R := A₀) (S := Localization.AtPrime 𝔪) (A := Localization.AtPrime 𝔮) (fun a => by
      rw [IsScalarTower.algebraMap_apply A₀ ↥B (Localization.AtPrime 𝔮),
        IsScalarTower.algebraMap_apply A₀ ↥B (Localization.AtPrime 𝔪), RingHom.algebraMap_toAlgebra]
      exact (IsLocalization.lift_eq hunits _).symm)
  haveI : IsLocalization (𝔮.primeCompl.map (algebraMap ↥B (Localization.AtPrime 𝔪))) (Localization.AtPrime 𝔮) :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.AtPrime 𝔪) (Localization.AtPrime 𝔮)
      𝔪.primeCompl 𝔮.primeCompl (fun x hx hq => hx (hqm hq))
  haveI : Algebra.FormallySmooth (Localization.AtPrime 𝔪) (Localization.AtPrime 𝔮) :=
    Algebra.FormallySmooth.of_isLocalization (𝔮.primeCompl.map (algebraMap ↥B (Localization.AtPrime 𝔪)))
  haveI : Algebra.FormallySmooth A₀ (Localization.AtPrime 𝔪) := RingHom.formallySmooth_algebraMap.mp hsm
  haveI : Algebra.FormallySmooth A₀ (Localization.AtPrime 𝔮) :=
    Algebra.FormallySmooth.comp A₀ (Localization.AtPrime 𝔪) (Localization.AtPrime 𝔮)

  have hunitsF : ∀ y : 𝔮.primeCompl, IsUnit (algebraMap ↥B F y) := fun y => by
    rw [isUnit_iff_ne_zero]
    intro h0
    exact y.2 (by rw [hBinj _ h0]; exact 𝔮.zero_mem)
  let φ : Localization.AtPrime 𝔮 →+* F := IsLocalization.lift (M := 𝔮.primeCompl) hunitsF
  have hφ : ∀ b : ↥B, φ (algebraMap ↥B (Localization.AtPrime 𝔮) b) = (b : F) :=
    fun b => IsLocalization.lift_eq hunitsF b
  have hφmk : ∀ (b : ↥B) (c : 𝔮.primeCompl),
      φ (IsLocalization.mk' (Localization.AtPrime 𝔮) b c) * ((c : ↥B) : F) = (b : F) := by
    intro b c
    rw [← hφ (c : ↥B), ← map_mul, IsLocalization.mk'_spec, hφ]
  have hφA : ∀ a : A₀, φ (algebraMap A₀ (Localization.AtPrime 𝔮) a) = algebraMap A₀ F a := fun a => by
    rw [IsScalarTower.algebraMap_apply A₀ ↥B (Localization.AtPrime 𝔮), hφ]; rfl
  let φₐ : Localization.AtPrime 𝔮 →ₐ[A₀] F := { toRingHom := φ, commutes' := hφA }
  have hφₐ : ∀ z, φₐ z = φ z := fun _ => rfl
  have hc0 : ∀ c : 𝔮.primeCompl, ((c : ↥B) : F) ≠ 0 := fun c h0 => c.2 (by rw [hBinj _ h0]; exact 𝔮.zero_mem)
  have hrange : ∀ z, φₐ z ∈ S := by
    intro z
    obtain ⟨⟨b, c⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl z
    rw [hS]
    exact ⟨b, c, c.2, hφmk b c⟩
  have hinj : Function.Injective φₐ := by
    intro z₁ z₂ h
    obtain ⟨⟨b₁, c₁⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl z₁
    obtain ⟨⟨b₂, c₂⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl z₂
    rw [hφₐ, hφₐ] at h
    rw [IsLocalization.mk'_eq_iff_eq]
    have e₁ := hφmk b₁ c₁
    have e₂ := hφmk b₂ c₂
    congr 1
    apply Subtype.ext
    simp only [Subalgebra.coe_mul]

    calc ((c₂ : ↥B) : F) * (b₁ : F) = ((c₂ : ↥B) : F) * (φ (IsLocalization.mk' _ b₁ c₁) * ((c₁ : ↥B) : F)) := by rw [e₁]
      _ = ((c₁ : ↥B) : F) * (φ (IsLocalization.mk' _ b₂ c₂) * ((c₂ : ↥B) : F)) := by rw [h]; ring
      _ = ((c₁ : ↥B) : F) * (b₂ : F) := by rw [e₂]
  have hsurj : Function.Surjective (φₐ.codRestrict S hrange) := by
    intro f
    obtain ⟨b, c, hc, hfc⟩ := (hS f).mp f.2
    have hcm : c ∈ 𝔮.primeCompl := hc
    refine ⟨IsLocalization.mk' (Localization.AtPrime 𝔮) b ⟨c, hcm⟩, Subtype.ext ?_⟩
    change φ _ = (f : F)
    have := hφmk b ⟨c, hcm⟩
    have hc' : ((c : ↥B) : F) ≠ 0 := hc0 ⟨c, hcm⟩
    calc φ (IsLocalization.mk' (Localization.AtPrime 𝔮) b ⟨c, hcm⟩)
        = (b : F) * ((c : ↥B) : F)⁻¹ := by rw [← this, mul_assoc, mul_inv_cancel₀ hc', mul_one]
      _ = (f : F) := by rw [← hfc, mul_assoc, mul_inv_cancel₀ hc', mul_one]
  let e : Localization.AtPrime 𝔮 ≃ₐ[A₀] ↥S :=
    AlgEquiv.ofBijective (φₐ.codRestrict S hrange) ⟨fun z₁ z₂ h => hinj (congrArg Subtype.val h), hsurj⟩
  exact Algebra.FormallySmooth.of_equiv e

theorem isUnit_of_inv_mem' {S : Type*} [SetLike S K] [SubringClass S K] (s : S) {x : K} (hx : x ∈ s)
    (hx' : x⁻¹ ∈ s) (hx0 : x ≠ 0) : IsUnit (⟨x, hx⟩ : s) :=
  ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hx'⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

theorem inv_mem_of_isUnit' {S : Type*} [SetLike S K] [SubringClass S K] (s : S) {x : K} (hx : x ∈ s)
    (h : IsUnit (⟨x, hx⟩ : s)) : x⁻¹ ∈ s := by
  obtain ⟨u, hu⟩ := h
  have hmul : x * ((u⁻¹ : (↥s)ˣ) : s) = 1 := by
    have h1 : ((u : s) * (u⁻¹ : (↥s)ˣ) : s) = 1 := Units.mul_inv u
    have h2 := congrArg (fun t : s => (t : K)) h1
    beta_reduce at h2
    rw [hu] at h2
    simpa using h2
  rw [inv_eq_of_mul_eq_one_right hmul]
  exact ((u⁻¹ : (↥s)ˣ) : s).2

end E150G

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

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
    (ℓ : CuspidalType.ProjLine q)

    (S : Subalgebra A₀ ↥F₀) (hS : ∀ f : ↥F₀, f ∈ S ↔ (f : ↥(fieldBar q M')) ∈ OIg ℓ) :
    Algebra.FormallySmooth A₀ ↥S := by
  classical

  let O : ValuationSubring ↥F₀ := (OIg ℓ).comap F₀.subtype
  have memO : ∀ f : ↥F₀, f ∈ O ↔ (f : ↥(fieldBar q M')) ∈ OIg ℓ := fun _ => ValuationSubring.mem_comap
  obtain ⟨γ, hγ, -, hOℓ⟩ := hIg ℓ
  have memℓ : ∀ g : ↥(fieldBar q M'), g ∈ OIg ℓ ↔ levelAutBar q M' ζ γ g ∈ OIg (lineInfty q) := by
    intro g; rw [hOℓ]; exact ValuationSubring.mem_comap
  obtain ⟨R, hR⟩ := ModularCurve.FullLevel.exists_regularProlongation_integers_eq_igusaGaussRing q hq M' hqM' A hA W hW hle R₀ hR₀ ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr
  have constA : ∀ x : AlgebraicClosure ℚ,
      algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x ∈ OIg (lineInfty q) ↔ x ∈ A := by
    intro x; rw [← hR]; exact R.algebraMap_mem_iff x
  have τconst : ∀ x : AlgebraicClosure ℚ,
      levelAutBar q M' ζ γ (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x) =
        algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x := fun x => AlgEquiv.commutes _ x

  have const_mem : ∀ a : A₀, algebraMap A₀ ↥F₀ a ∈ O := by
    intro a; rw [memO, hj₀, memℓ, τconst]; exact (constA _).mpr (ι a).2
  let c : A₀ →+* ↥O := (algebraMap A₀ ↥F₀).codRestrict O const_mem
  have hc_coe : ∀ a : A₀, ((c a : ↥O) : ↥F₀) = algebraMap A₀ ↥F₀ a := fun _ => rfl
  have hc : ∀ a ∈ maximalIdeal A₀, c a ∈ maximalIdeal ↥O := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hιa : ¬ IsUnit (ι a) := fun h => ((IsLocalRing.mem_maximalIdeal _).mp ha) (IsLocalHom.map_nonunit a h)

    have hinv : (algebraMap A₀ ↥F₀ a)⁻¹ ∈ O := E150G.inv_mem_of_isUnit' O (const_mem a) hu
    rw [memO] at hinv
    have : ((algebraMap A₀ ↥F₀ a)⁻¹ : ↥F₀) = (⟨(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')
        ((ι a : ↥A) : AlgebraicClosure ℚ))⁻¹, by rw [← hj₀]; exact (F₀.inv_mem (algebraMap A₀ ↥F₀ a).2)⟩ : ↥F₀) := by
      apply Subtype.ext; push_cast; rw [hj₀]
    rw [this] at hinv
    change (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ))⁻¹ ∈ OIg ℓ at hinv
    rw [← map_inv₀, memℓ, τconst, constA] at hinv

    by_cases h0 : ((ι a : ↥A) : AlgebraicClosure ℚ) = 0
    · have hι0 : ι a = 0 := Subtype.ext h0
      have ha0 : a = 0 := hι (by rw [hι0, map_zero])
      rw [ha0, map_zero] at hu
      exact not_isUnit_zero hu
    · have := E150G.isUnit_of_inv_mem' A (ι a).2 hinv h0
      exact hιa (by simpa using this)

  have hJO : (⟨_, hjF₀⟩ : ↥F₀) ∈ O := by
    obtain ⟨h, -⟩ := ModularCurve.FullLevel.isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss q M' hqM' A hle ζ γ hγ
      (OIg (lineInfty q)) hIg_inf (0 : ↥A)
    rw [memO, memℓ]
    simpa using h
  have hj33 : ∀ a : A₀, IsUnit ((⟨_, hJO⟩ : ↥O) - c a) := by
    intro a
    obtain ⟨h, hu⟩ := ModularCurve.FullLevel.isUnit_levelAutBar_jBar_sub_algebraMap_of_gauss q M' hqM' A hle ζ γ hγ
      (OIg (lineInfty q)) hIg_inf (ι a)

    have hw : ((⟨_, hJO⟩ : ↥O) - c a : ↥O) = ⟨(⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥F₀ a, sub_mem hJO (const_mem a)⟩ :=
      Subtype.ext rfl
    rw [hw]
    have hcoe : ((((⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥F₀ a : ↥F₀)) : ↥(fieldBar q M')) =
        (((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀) : ↥(fieldBar q M')) -
          algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) := by
      rw [← hj₀]; rfl
    have hτw : levelAutBar q M' ζ γ ((((⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥F₀ a : ↥F₀)) : ↥(fieldBar q M')) =
        levelAutBar q M' ζ γ (((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀) : ↥(fieldBar q M')) -
          algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) := by
      rw [hcoe, map_sub, τconst]

    have hne : levelAutBar q M' ζ γ (((⟨_, hjF₀⟩ : ↥F₀) : ↥F₀) : ↥(fieldBar q M')) -
          algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((ι a : ↥A) : AlgebraicClosure ℚ) ≠ 0 := by
      intro h0
      apply not_isUnit_zero (M₀ := ↥(OIg (lineInfty q)))
      convert hu <;> first | rfl | exact h0.symm
    have hinvG := E150G.inv_mem_of_isUnit' (OIg (lineInfty q)) h hu
    have hw0 : ((⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥F₀ a : ↥F₀) ≠ 0 := by
      intro h0
      apply hne
      rw [← hτw, h0]; simp
    apply E150G.isUnit_of_inv_mem' O (sub_mem hJO (const_mem a)) _ hw0
    rw [memO]
    change (((((⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥F₀ a : ↥F₀)) : ↥(fieldBar q M')))⁻¹ ∈ OIg ℓ
    rw [memℓ, map_inv₀, hτw]
    exact hinvG

  haveI : IsAlgClosed (ResidueField A₀) := by
    obtain ⟨k₀, π₀, hπ₀, -, -, hdvr, -, -, hres', -, -, -, ⟨e, -⟩⟩ :=
      ModularCurve.FullLevel.exists_admissible_smallConstants_of_descentBase q hq M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀
    exact IsAlgClosed.of_ringEquiv _ _ (IsLocalRing.ResidueField.mapEquiv e).symm

  obtain ⟨V, hVO, hVc, hVj, hVj'⟩ := E150G.exists_le_inv_mem_nonunits O c hc ⟨_, hJO⟩ hj33
  have hV : ∀ f : ↥F₀, f ∈ V → (f : ↥(fieldBar q M')) ∈ OIg ℓ := fun f hf => (memO f).mp (hVO hf)
  have hVlt : ∃ f : ↥F₀, (f : ↥(fieldBar q M')) ∈ OIg ℓ ∧ f ∉ V := ⟨_, (memO _).mp hJO, hVj'⟩

  rcases ModularCurve.FullLevel.exists_subalgebra_centred_formallySmooth_or_exists_forall_mem_nonunits_of_le_igusaRing_descent_local
      q hq M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ ℓ V hV hVlt with
    ⟨B, 𝔪, h𝔪, -, -, -, -, -, -, -, ⟨𝔮, h𝔮, hloc⟩, -, hBV, hcen, -, hsm⟩ | ⟨s, hbad⟩
  ·
    haveI h𝔪p : 𝔪.IsPrime := h𝔪.isPrime
    haveI h𝔮p : 𝔮.IsPrime := h𝔮
    have hO_desc : ∀ x : ↥F₀, x ∈ O ↔ ∃ b c : ↥B, c ∉ 𝔮 ∧ x * (c : ↥F₀) = (b : ↥F₀) :=
      fun x => (memO x).trans (hloc x)
    have hBinj : ∀ b : ↥B, (b : ↥F₀) = 0 → b = 0 := fun b hb => Subtype.ext hb

    have hqm : 𝔮 ≤ 𝔪 := by
      intro b hb
      by_cases hb0 : b = 0
      · rw [hb0]; exact 𝔪.zero_mem
      have hb0' : (b : ↥F₀) ≠ 0 := fun h => hb0 (hBinj b h)
      rw [hcen, ValuationSubring.mem_nonunits_iff_or]
      right
      intro hbinv
      have hbO : ((b : ↥F₀))⁻¹ ∈ O := hVO hbinv
      obtain ⟨b', c', hc', heq⟩ := (hO_desc _).mp hbO
      apply hc'
      have : c' = b * b' := by
        apply Subtype.ext
        have := congrArg (fun t => (b : ↥F₀) * t) heq
        simp only [← mul_assoc, mul_inv_cancel₀ hb0', one_mul] at this
        rw [this]; rfl
      rw [this]; exact 𝔮.mul_mem_right _ hb
    exact E150G.formallySmooth_of_le_of_localization B 𝔪 𝔮 hqm hsm S (fun x => (hS x).trans (hloc x))
  ·
    exfalso
    obtain ⟨a, h, hmax⟩ := ModularCurve.FullLevel.exists_jInvariant_sub_mem_maximalIdeal_drinfeldRing_descent q hq M' hqM' A hA W hW hle R₀ hR₀ π hπ hπP ζ OIg OSS hIg_inf hIg hIg_inj hIg_perm hSS_A hSS_over hSS_fix hSS_tr K₀ hπK₀ A₀ ι hι hιK₀ hres ϖ₀ hϖ₀ hϖ₀π F₀ hF₀ hjF₀ hj₀ s
    have hg : _root_.IsIntegral ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀)) ((⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥F₀ a : ↥F₀) := by
      have hmem : ((⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥F₀ a : ↥F₀) ∈ Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀) :=
        sub_mem (Algebra.subset_adjoin rfl) (Subalgebra.algebraMap_mem _ a)
      exact (isIntegral_algebraMap (R := ↥(Algebra.adjoin A₀ ({(⟨_, hjF₀⟩ : ↥F₀)} : Set ↥F₀))) (x := ⟨_, hmem⟩))
    have hgV : ((⟨_, hjF₀⟩ : ↥F₀) - algebraMap A₀ ↥F₀ a : ↥F₀) ∈ V := V.nonunits_subset (hbad _ hg ⟨h, hmax⟩)
    apply hVj'
    have key := add_mem hgV (hVc a)
    rwa [hc_coe, sub_add_cancel] at key

end S_ModularCurve_FullLevel_formallySmooth_subalgebra_of_mem_iff_mem_igusaRing_descent
end P2MW
export P2MW.S_ModularCurve_FullLevel_formallySmooth_subalgebra_of_mem_iff_mem_igusaRing_descent (solution)
