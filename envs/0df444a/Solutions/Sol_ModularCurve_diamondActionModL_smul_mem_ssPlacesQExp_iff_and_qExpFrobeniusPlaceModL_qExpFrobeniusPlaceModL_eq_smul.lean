-- Prove2me | solution 1 for ModularCurve.diamondActionModL_smul_mem_ssPlacesQExp_iff_and_qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/60a0a791-e659-5849-9d09-429c97dafbab

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_XHDRModelAtP_qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_diamondActionModL_smul_of_mem_ssPlacesQExp
import Theorems.Thm_ModularCurve_exists_xHDRModelAtP_atkinLehner_generic_chart
import Theorems.Thm_ModularCurve_DRLevel_exists_place_residueField_ringHom_comp_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_isDiamondPullbackModL_of_isAlgClosed
import Theorems.Thm_ModularCurve_IsDiamondPullbackModL_apply_eq_self_of_coe_mem_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_ModularCurve_exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed
import Theorems.Thm_ModularCurve_map_diamondActionModL_eq_diamondActionModL_map_of_coe_eq_coeffMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_diamondActionModL_smul_mem_ssPlacesQExp_iff_and_qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_smul
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA"
p2m_attr_erase "instance" "TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01"
p2m_attr_erase "simp" "CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply"
p2m_attr_erase "simp" "ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk"
p2m_attr_erase "simp" "ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false

open scoped MatrixGroups Pointwise

namespace Frob2Pen13

open AlgebraicCurve

theorem hasValue_smul {K F : Type*} [Field K] [Field F] [Algebra K F] (g : SemilinearAut K F) (v : Place K F)
    {x : F} {a : K} (h : v.HasValue x a) : (g • v).HasValue (g • x) (SemilinearAut.baseAut g a) := by
  obtain ⟨hx, hres⟩ := h
  have hmem : g • x ∈ (g • v).toValuationSubring := by
    rw [SemilinearAut.smul_toValuationSubring]
    exact ValuationSubring.smul_mem_pointwise_smul g x v.toValuationSubring hx
  refine ⟨hmem, ?_⟩
  have key : IsLocalRing.residue (g • v).toValuationSubring
      (SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨x, hx⟩) =
      SemilinearAut.smulResidueRingEquiv g v (IsLocalRing.residue v.toValuationSubring ⟨x, hx⟩) := by
    rw [SemilinearAut.smulResidueRingEquiv, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    rfl
  have hx' : (⟨g • x, hmem⟩ : (g • v).toValuationSubring) =
      SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨x, hx⟩ := rfl
  rw [hx', key, hres, SemilinearAut.smulResidueRingEquiv_algebraMap]

theorem hasValue_ofAlgAut_smul_iff {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (v : Place K F)
    {x : F} (hfix : σ x = x) (a : K) : (SemilinearAut.ofAlgAut σ • v).HasValue x a ↔ v.HasValue x a := by
  have hfix' : σ⁻¹ x = x := by
    show σ.symm x = x
    conv_lhs => rw [← hfix]
    exact σ.symm_apply_apply x
  constructor
  · intro h
    have h' := hasValue_smul (SemilinearAut.ofAlgAut σ⁻¹) _ h
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, SemilinearAut.ofAlgAut_smul, hfix',
      SemilinearAut.baseAut_ofAlgAut] at h'
    exact h'
  · intro h
    have h' := hasValue_smul (SemilinearAut.ofAlgAut σ) _ h
    rw [SemilinearAut.ofAlgAut_smul, hfix, SemilinearAut.baseAut_ofAlgAut] at h'
    exact h'

theorem ext_smul_eq {k L Fk FL : Type*} [Field k] [Field L] [Field Fk] [Field FL] [Algebra k Fk] [Algebra L FL]
    (ext : Place k Fk → Place L FL) (ι : Fk →+* FL)
    (hpre : ∀ (v : Place k Fk) (f : Fk), f ∈ v.toValuationSubring ↔ ι f ∈ (ext v).toValuationSubring)
    (huniq : ∀ (v : Place k Fk) (w : Place L FL), (∀ f : Fk, f ∈ v.toValuationSubring ↔ ι f ∈ w.toValuationSubring) → ext v = w)
    (σk : Fk ≃ₐ[k] Fk) (σL : FL ≃ₐ[L] FL) (hinv : ∀ x : Fk, ι (σk⁻¹ x) = σL⁻¹ (ι x)) (v : Place k Fk) :
    ext (SemilinearAut.ofAlgAut σk • v) = SemilinearAut.ofAlgAut σL • ext v := by
  refine huniq _ _ fun f => ?_
  rw [SemilinearAut.smul_toValuationSubring, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ← map_inv, ← map_inv, SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul, hpre, hinv]

end Frob2Pen13

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N) (H' : Subgroup (ZMod N)ˣ) :
    (∀ (d : (ZMod N)ˣ) (y : AlgebraicCurve.Place K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))),
        AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d)) • y ∈
            ModularCurve.ssPlacesQExp K (CohCarrier.GammaH N H') p ↔
          y ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH N H') p) ∧
    ∀ (e : (ZMod N)ˣ), ((e : (ZMod N)ˣ) : ZMod N) * (p : ZMod N) = 1 →
      ∀ y ∈ ModularCurve.ssPlacesQExp K (CohCarrier.GammaH N H') p,
        ModularCurve.qExpFrobeniusPlaceModL K (CohCarrier.GammaH N H') p
            (ModularCurve.qExpFrobeniusPlaceModL K (CohCarrier.GammaH N H') p y) =
          AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N e)) • y := by
  classical
  have hp : p.Prime := Fact.out

  obtain ⟨M, ⟨hpM, hpM2, hM0⟩, rfl⟩ : ∃ M : ℕ, (p ∣ M ∧ ¬ p ^ 2 ∣ M ∧ M ≠ 0) ∧ N = M / p :=
    ⟨N * p, ⟨dvd_mul_left p N, fun h => hpN (by
        rw [pow_two] at h
        exact (Nat.mul_dvd_mul_iff_right hp.pos).mp h), mul_ne_zero (NeZero.ne N) hp.ne_zero⟩,
      (Nat.mul_div_cancel N hp.pos).symm⟩
  haveI : NeZero M := ⟨hM0⟩
  obtain ⟨H, hHp, rfl⟩ : ∃ H : Subgroup (ZMod M)ˣ,
      (∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) ∧ H' = ModularCurve.infSubgroup p M H hpM := by
    refine ⟨H'.comap (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)), fun u hu => ?_, ?_⟩
    · rw [Subgroup.mem_comap, hu]; exact one_mem _
    · exact (Subgroup.map_comap_eq_self_of_surjective (ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpM)) H').symm

  have hNK : ((M / p : ℕ) : K) ≠ 0 := fun h => hpN ((CharP.cast_eq_zero_iff K p (M / p)).mp h)
  obtain ⟨ρ₀, hρ₀⟩ := ModularCurve.exists_isDiamondPullbackModL_of_isAlgClosed K (M / p) hNK (ModularCurve.infSubgroup p M H hpM)
  have hρK := ModularCurve.isDiamondPullbackModL_diamondActionModL ⟨ρ₀, hρ₀⟩
  have hfix : ∀ (γ : CongruenceSubgroup.Gamma0 (M / p)) (x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))), (x : LaurentSeries K) = ModularCurve.jqModC K →
      ModularCurve.diamondActionModL K (M / p) (ModularCurve.infSubgroup p M H hpM) γ x = x := fun γ x hx =>
    ModularCurve.IsDiamondPullbackModL.apply_eq_self_of_coe_mem_qExpFunctionFieldC_gamma0 K (M / p) _ hρK γ x
      (hx ▸ ModularCurve.intFormRatiosC_subset K _ (ModularCurve.jqModC_mem_intFormRatiosC K _))
  refine ⟨fun d y => ?_, ?_⟩
  · simp only [ModularCurve.mem_ssPlacesQExp_iff, ModularCurve.IsSSPlaceQExp]
    constructor
    · rintro ⟨x, a, hxj, hval, ha⟩
      exact ⟨x, a, hxj, (Frob2Pen13.hasValue_ofAlgAut_smul_iff _ y (hfix _ x hxj) a).1 hval, ha⟩
    · rintro ⟨x, a, hxj, hval, ha⟩
      exact ⟨x, a, hxj, (Frob2Pen13.hasValue_ofAlgAut_smul_iff _ y (hfix _ x hxj) a).2 hval, ha⟩

  intro e he y hy
  have hT : ModularGroup.T ∈ (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) := ModularCurve.translation_mem_GammaH _ _

  let k : Type := AlgebraicClosure (ZMod p)
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  letI : Algebra k K := (IsAlgClosed.lift (R := ZMod p) (M := K) (S := k)).toRingHom.toAlgebra

  obtain ⟨A, hA, instC, instI, ρ, hρ, -, -⟩ := ModularCurve.DRLevel.exists_place_residueField_ringHom_comp_eq p k
    ((algebraMap (ZMod p) k).comp (GaloisRep.ratLocalizedAtResidue p))
  haveI : CharP (IsLocalRing.ResidueField ↥A) p := instC
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := instI
  letI : Algebra (ZMod p) (IsLocalRing.ResidueField ↥A) := ZMod.algebra _ p
  letI : Algebra k (IsLocalRing.ResidueField ↥A) :=
    (IsAlgClosed.lift (R := ZMod p) (M := IsLocalRing.ResidueField ↥A) (S := k)).toRingHom.toAlgebra

  have hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)) :=
    ModularCurve.intFormRatiosC_subset ℚ ⊤ (ModularCurve.jqModC_mem_intFormRatiosC ℚ ⊤)
  obtain ⟨𝔛, -, -, -⟩ := ModularCurve.exists_xHDRModelAtP_atkinLehner_generic_chart p M H hpM hpM2 hHp hj
  have hdia0 := ModularCurve.XHDRModelAtP.exists_placeOfPoint_fibreMap_dia0_eq_diamondActionModL_smul_of_ker_le
    p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ
  have h82 := ModularCurve.XHDRModelAtP.qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_diamondActionModL_smul_of_mem_ssPlacesQExp
    p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ hdia0 e he

  obtain ⟨xk, -, htrk, hfdk⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed k (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) hT
  obtain ⟨xK, -, htrK, hfdK⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) hT
  obtain ⟨xA, -, htrA, hfdA⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
    (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) hT
  haveI := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htrk hfdk
  haveI := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htrK hfdK
  haveI := AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htrA hfdA

  have hmemK : ∀ x : ↥(ModularCurve.qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), ((ModularCurve.coeffMap (algebraMap k K)).comp (SubringClass.subtype _)) x ∈
      ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) := fun x => by
    rw [ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC k K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))]
    exact IntermediateField.subset_adjoin K _ ⟨x, x.2, rfl⟩
  have hmemA : ∀ x : ↥(ModularCurve.qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), ((ModularCurve.coeffMap (algebraMap k (IsLocalRing.ResidueField ↥A))).comp (SubringClass.subtype _)) x ∈
      ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) := fun x => by
    rw [ModularCurve.qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC k (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))]
    exact IntermediateField.subset_adjoin _ _ ⟨x, x.2, rfl⟩
  let ιK : ↥(ModularCurve.qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) →+* ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) := RingHom.codRestrict _ _ hmemK
  let ιA : ↥(ModularCurve.qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) →+* ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) := RingHom.codRestrict _ _ hmemA
  have hιK : ∀ x : ↥(ModularCurve.qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), ((ιK x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries K) = ModularCurve.coeffMap (algebraMap k K) (x : LaurentSeries k) :=
    fun x => rfl
  have hιA : ∀ x : ↥(ModularCurve.qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), ((ιA x : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
      ModularCurve.coeffMap (algebraMap k (IsLocalRing.ResidueField ↥A)) (x : LaurentSeries k) :=
    fun x => rfl

  obtain ⟨extK, -, hpreK, huniqK, -, -, -, hssK, hssimgK, hFrK⟩ :=
    ModularCurve.exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed p k K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))
      ⟨xk, htrk, hfdk⟩ ⟨xK, htrK, hfdK⟩ ιK hιK
  obtain ⟨extA, hinjA, hpreA, huniqA, -, -, -, hssA, -, hFrA⟩ :=
    ModularCurve.exists_injective_place_extension_ssPlacesQExp_qExpFrobeniusPlaceModL_of_isAlgClosed p k (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))
      ⟨xk, htrk, hfdk⟩ ⟨xA, htrA, hfdA⟩ ιA hιA

  have hNk : ((M / p : ℕ) : k) ≠ 0 := fun h => hpN ((CharP.cast_eq_zero_iff k p (M / p)).mp h)
  have hinvK : ∀ x : ↥(ModularCurve.qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), ιK ((ModularCurve.diamondActionModL k (M / p) (ModularCurve.infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) e))⁻¹ x) =
      (ModularCurve.diamondActionModL K (M / p) (ModularCurve.infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) e))⁻¹ (ιK x) := fun x => by
    rw [← map_inv, ← map_inv]
    exact ModularCurve.map_diamondActionModL_eq_diamondActionModL_map_of_coe_eq_coeffMap k K (M / p) hNk _ ιK hιK _ x
  have hinvA : ∀ x : ↥(ModularCurve.qExpFunctionFieldC k (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))), ιA ((ModularCurve.diamondActionModL k (M / p) (ModularCurve.infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) e))⁻¹ x) =
      (ModularCurve.diamondActionModL (IsLocalRing.ResidueField ↥A) (M / p) (ModularCurve.infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) e))⁻¹ (ιA x) :=
    fun x => by
    rw [← map_inv, ← map_inv]
    exact ModularCurve.map_diamondActionModL_eq_diamondActionModL_map_of_coe_eq_coeffMap k (IsLocalRing.ResidueField ↥A) (M / p) hNk _ ιA hιA _ x

  obtain ⟨v, rfl⟩ := hssimgK y hy
  have hv : v ∈ ModularCurve.ssPlacesQExp k (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p := (hssK v).2 hy
  have key := h82 (extA v) ((hssA v).1 hv)
  have e1 : extA (ModularCurve.qExpFrobeniusPlaceModL k (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p (ModularCurve.qExpFrobeniusPlaceModL k (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p v)) = ModularCurve.qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p (ModularCurve.qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p (extA v)) :=
    (hFrA _).trans (congrArg _ (hFrA v))
  have e2 := Frob2Pen13.ext_smul_eq extA ιA hpreA huniqA
    (ModularCurve.diamondActionModL k (M / p) (ModularCurve.infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) e))
    (ModularCurve.diamondActionModL (IsLocalRing.ResidueField ↥A) (M / p) (ModularCurve.infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) e))
    hinvA v
  have key3 := hinjA (e1.trans (key.trans e2.symm))
  have f1 : extK (ModularCurve.qExpFrobeniusPlaceModL k (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p (ModularCurve.qExpFrobeniusPlaceModL k (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p v)) =
      ModularCurve.qExpFrobeniusPlaceModL K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p (ModularCurve.qExpFrobeniusPlaceModL K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p (extK v)) :=
    (hFrK _).trans (congrArg _ (hFrK v))
  exact f1.symm.trans ((congrArg extK key3).trans (Frob2Pen13.ext_smul_eq extK ιK hpreK huniqK _ _ hinvK v))

end S_ModularCurve_diamondActionModL_smul_mem_ssPlacesQExp_iff_and_qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_smul
end P2MW
export P2MW.S_ModularCurve_diamondActionModL_smul_mem_ssPlacesQExp_iff_and_qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_smul (solution)
