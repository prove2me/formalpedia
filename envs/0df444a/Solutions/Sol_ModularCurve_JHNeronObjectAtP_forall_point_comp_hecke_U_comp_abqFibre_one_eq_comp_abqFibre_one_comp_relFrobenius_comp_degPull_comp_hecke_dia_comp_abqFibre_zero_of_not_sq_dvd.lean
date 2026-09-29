-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.forall_point_comp_hecke_U_comp_abqFibre_one_eq_comp_abqFibre_one_comp_relFrobenius_comp_degPull_comp_hecke_dia_comp_abqFibre_zero_of_not_sq_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/141c0ba6-e727-5cbd-b19b-419b89ff7c42

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_toPic0Pair_ptsSp_symm_hecke_U_eq_blockOp
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_hecke_dia_eq_glueMap
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_levelData_ptsSp_frobeniusPushforward_eq_schemeHomOverComp_frobenius_ptsSp_of_hsp
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Theorems.Thm_ModularCurve_isNodeStable_ofAlgAut_diamondActionModL_of_forall_mem_iff_mem_ssNodePairsQExp_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_forall_point_comp_hecke_U_comp_abqFibre_one_eq_comp_abqFibre_one_comp_relFrobenius_comp_degPull_comp_hecke_dia_comp_abqFibre_zero_of_not_sq_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice"
p2m_attr_erase "simp" "PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ"
p2m_attr_erase "simp" "ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace PtsSpelling

section P1

variable {R R' : Type} [CommRing R] [CommRing R'] {X Y : Scheme.{0}}
  (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}

theorem toFibrePt_coe_comp_pullbackMap (φ : SchemeHomOver g f) (x : SchemeHomOver ι g)
    (h₁ : g ≫ 𝟙 _ = φ.1 ≫ f) (h₂ : ι ≫ 𝟙 _ = 𝟙 _ ≫ ι) :
    (toFibrePt x).1 ≫ pullback.map g ι f ι φ.1 (𝟙 _) (𝟙 _) h₁ h₂ =
      (toFibrePt (NeronModelInfra.schemeHomOverComp x φ)).1 := by
  apply pullback.hom_ext
  · simp only [toFibrePt, overId, RelativeGroupLaw.baseChangePointOfBase_coe, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc, NeronModelInfra.schemeHomOverComp_coe]
  · simp only [toFibrePt, overId, RelativeGroupLaw.baseChangePointOfBase_coe, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, Category.comp_id]

theorem coe_comp_pullbackMap_eq_toFibrePt (φ : SchemeHomOver g f)
    (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (RelativeGroupLaw.baseChangeStr ι g))
    (h₁ : g ≫ 𝟙 _ = φ.1 ≫ f) (h₂ : ι ≫ 𝟙 _ = 𝟙 _ ≫ ι) :
    y.1 ≫ pullback.map g ι f ι φ.1 (𝟙 _) (𝟙 _) h₁ h₂ =
      (toFibrePt (NeronModelInfra.schemeHomOverComp (ofFibrePt y) φ)).1 := by
  rw [← toFibrePt_coe_comp_pullbackMap ι φ (ofFibrePt y) h₁ h₂]
  congr 2

  apply Subtype.ext
  apply pullback.hom_ext
  · simp only [toFibrePt, ofFibrePt, overId, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst,
      RelativeGroupLaw.baseChangePointToBase_coe]
  · simp only [toFibrePt, ofFibrePt, overId, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd]
    exact y.2

theorem toFibrePt_ofFibrePt (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (RelativeGroupLaw.baseChangeStr ι g)) :
    toFibrePt (ofFibrePt y) = y := by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp only [toFibrePt, ofFibrePt, overId, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst,
      RelativeGroupLaw.baseChangePointToBase_coe]
  · simp only [toFibrePt, ofFibrePt, overId, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_snd]
    exact y.2.symm

theorem toFibrePt_coe_fst (x : SchemeHomOver ι g) : (toFibrePt x).1 ≫ pullback.fst g ι = x.1 := by
  simp only [toFibrePt, overId, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]

theorem toFibrePt_coe_comp_eq_toFibrePt_fibreMap
    (φ : SchemeHomOver (RelativeGroupLaw.baseChangeStr ι g) (RelativeGroupLaw.baseChangeStr ι f)) (w : SchemeHomOver ι g) :
    (toFibrePt w).1 ≫ φ.1 = (toFibrePt (fibreMap φ w)).1 := by
  show (toFibrePt w).1 ≫ φ.1 = (toFibrePt (ofFibrePt (NeronModelInfra.schemeHomOverComp (toFibrePt w) φ))).1
  rw [toFibrePt_ofFibrePt, NeronModelInfra.schemeHomOverComp_coe]

end P1

section K1

variable {R κ : Type} [CommRing R] [Field κ] {X : Scheme.{0}}
  (s : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R))
  (p : ℕ) [Fact p.Prime] [CharP κ p]

theorem coe_comp_relFrobenius_eq_lift_frobenius_twist
    (hp0 : (p : Γ(RelativeGroupLaw.baseChangeScheme s f, ⊤)) = 0)
    (hFrob : (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme s f) p 1 Fact.out hp0 ≫ pullback.fst f s) ≫ f = pullback.snd f s ≫ s)
    (hs : Spec.map (CommRingCat.ofHom (frobenius κ p)) ≫ s = s)
    (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) (RelativeGroupLaw.baseChangeStr s f)) :
    y.1 ≫ pullback.lift (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme s f) p 1 Fact.out hp0 ≫ pullback.fst f s) (pullback.snd f s) hFrob =
      pullback.lift (Spec.map (CommRingCat.ofHom (frobenius κ p)) ≫ y.1 ≫ pullback.fst f s) (𝟙 _)
        (by
          have hy : y.1 ≫ pullback.snd f s = 𝟙 _ := y.2
          rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc y.1, hy, Category.id_comp]
          simpa using hs) := by
  have hκ : (p : κ) = 0 := CharP.cast_eq_zero κ p

  have hnat := Scheme.frobenius_comp y.1 p 1 Fact.out (Scheme.natCast_eq_zero_ΓSpec hκ) hp0
  have hSpec : (Spec (CommRingCat.of κ)).frobenius p 1 Fact.out (Scheme.natCast_eq_zero_ΓSpec hκ) =
      Spec.map (CommRingCat.ofHom (frobenius κ p)) := by
    rw [Scheme.frobenius_Spec p 1 Fact.out hκ]
    congr 2
    ext x
    rw [powCharRingHom_apply, pow_one, frobenius_def]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, ← Category.assoc, ← hnat, hSpec, Category.assoc]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    exact y.2

end K1

end PtsSpelling

open ModularCurve.JHNeronObjectAtP (Fbar) in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (hspΛ : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥A).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)))
      (_ : (Dw : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) =
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt A ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s₀) = Pic0.mk Dw)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P)

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (Wbar : JH M H →+ JH M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hWbar : ∀ x : JH M H, Wbar x = wgen • x)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (S : Set ℕ)
    (hUPgen : ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) x + Wbar x = αpull 1 (O.degPts 0 x))

    (hp0 : (p : Γ((RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) Λ.f), ⊤)) = 0)

    (hFrobΛ : (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) Λ.f) p 1 Fact.out hp0 ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA)) ≫ Λ.f =
      pullback.snd Λ.f (resPt A ≫ Λ.σA) ≫ (resPt A ≫ Λ.σA))

    (dM : (ZMod M)ˣ) (hdM : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) dM = pb) :
    ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g),
      x.1 ≫ (NeronModelInfra.schemeHomOverComp
        (⟨pullback.map O.g (resPt A ≫ Λ.σA) O.g (resPt A ≫ Λ.σA) (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1 (𝟙 _) (𝟙 _)
            (by rw [Category.comp_id]; exact ((O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).2).symm)
            (by rw [Category.comp_id, Category.id_comp]),
          by rw [RelativeGroupLaw.baseChangeStr, pullback.lift_snd, Category.comp_id]⟩ :
          SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g))
        (O.abqFibre 1)).1 =
      x.1 ≫ (NeronModelInfra.schemeHomOverComp (O.abqFibre 1)
        (NeronModelInfra.schemeHomOverComp
          (⟨pullback.lift (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) Λ.f) p 1 Fact.out hp0 ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA)) (pullback.snd Λ.f (resPt A ≫ Λ.σA)) hFrobΛ,
            pullback.lift_snd _ _ _⟩ :
            SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f))
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp
          (⟨pullback.map Λ.f (resPt A ≫ Λ.σA) O.g (resPt A ≫ Λ.σA) (degPull 0).1 (𝟙 _) (𝟙 _)
              (by rw [Category.comp_id]; exact ((degPull 0).2).symm)
              (by rw [Category.comp_id, Category.id_comp]),
            by rw [RelativeGroupLaw.baseChangeStr, RelativeGroupLaw.baseChangeStr, pullback.lift_snd, Category.comp_id]⟩ :
            SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g))
          (⟨pullback.map O.g (resPt A ≫ Λ.σA) O.g (resPt A ≫ Λ.σA) (O.hecke S (CohCarrier.Gen.dia dM)).1 (𝟙 _) (𝟙 _)
              (by rw [Category.comp_id]; exact ((O.hecke S (CohCarrier.Gen.dia dM)).2).symm)
              (by rw [Category.comp_id, Category.id_comp]),
            by rw [RelativeGroupLaw.baseChangeStr, pullback.lift_snd, Category.comp_id]⟩ :
            SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g)))
          (O.abqFibre 0)))).1 := by
  classical
  intro x

  let x' : SchemeHomOver (resPt A ≫ Λ.σA) O.g := ofFibrePt x
  let ξ := O.ptsSp.symm x'
  have hx' : O.ptsSp ξ = x' := O.ptsSp.apply_symm_apply x'
  let z : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) := (GluedPic0.toPic0Pair O.ssFinset ξ).2

  have hndvd : ¬ p ∣ M / p := fun h => hpM2 (by
    obtain ⟨c, hc⟩ := h
    exact ⟨c, by rw [← Nat.div_mul_cancel hpM, hc]; ring⟩)
  have hstab : SemilinearAut.IsNodeStable O.ssFinset
      (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) dM)))) :=
    ModularCurve.isNodeStable_ofAlgAut_diamondActionModL_of_forall_mem_iff_mem_ssNodePairsQExp_of_not_dvd (ResidueField ↥A) p (M / p) hndvd
      (infSubgroup p M H hpM) O.ssFinset O.mem_ssFinset_iff _

  have hL : GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (NeronModelInfra.schemeHomOverComp x' (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)))) =
      AlgebraicCurve.Pic0Pair.blockOp Fstar (((p : ℤ) - 1) • AddMonoidHom.id _) 0 (δ.comp F) (GluedPic0.toPic0Pair O.ssFinset ξ) := by
    have h := ModularCurve.JHNeronObjectAtP.toPic0Pair_ptsSp_symm_hecke_U_eq_blockOp p M H hpM hj 𝔛 A hA Λ O ρ hρ hσA hsp hspΛ hdia0
      F Finv Fstar hF hFinv hFstar pb hpb δ hδ αpull degPull hpull hpullsp Wbar wgen hWbar hwgen S hUPgen ξ
    rwa [hx'] at h
  have hL2 : (GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (NeronModelInfra.schemeHomOverComp x' (O.hecke S (CohCarrier.Gen.U p Fact.out hpM))))).2 = δ (F z) := by
    rw [hL]
    rcases hξ : GluedPic0.toPic0Pair O.ssFinset ξ with ⟨u, v⟩
    simp only [AlgebraicCurve.Pic0Pair.blockOp_apply, AddMonoidHom.zero_apply, zero_add, AddMonoidHom.coe_comp, Function.comp_apply]
    show δ (F v) = δ (F z)
    simp only [z, hξ]

  have habq1 : ∀ w : SchemeHomOver (resPt A ≫ Λ.σA) O.g, fibreMap (O.abqFibre 1) w = Λ.ptsSp (GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm w)).2 := by
    intro w
    have h := O.abqFibre_ptsSp (O.ptsSp.symm w) 1
    rw [O.ptsSp.apply_symm_apply, if_neg (show (1 : Fin 2) ≠ 0 by decide)] at h
    rw [← h, Equiv.apply_symm_apply]
  have habq0 : ∀ w : SchemeHomOver (resPt A ≫ Λ.σA) O.g, fibreMap (O.abqFibre 0) w = Λ.ptsSp (GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm w)).1 := by
    intro w
    have h := O.abqFibre_ptsSp (O.ptsSp.symm w) 0
    rw [O.ptsSp.apply_symm_apply, if_pos rfl] at h
    rw [← h, Equiv.apply_symm_apply]
  have hxx : x = toFibrePt x' := (PtsSpelling.toFibrePt_ofFibrePt (resPt A ≫ Λ.σA) x).symm

  have e₂ : (resPt A ≫ Λ.σA) ≫ 𝟙 _ = 𝟙 _ ≫ (resPt A ≫ Λ.σA) := by rw [Category.comp_id, Category.id_comp]
  have e₁U : O.g ≫ 𝟙 _ = (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1 ≫ O.g := by
    rw [Category.comp_id]; exact ((O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).2).symm
  have e₁D : O.g ≫ 𝟙 _ = (O.hecke S (CohCarrier.Gen.dia dM)).1 ≫ O.g := by
    rw [Category.comp_id]; exact ((O.hecke S (CohCarrier.Gen.dia dM)).2).symm
  have e₁P : Λ.f ≫ 𝟙 _ = (degPull 0).1 ≫ O.g := by
    rw [Category.comp_id]; exact ((degPull 0).2).symm

  have hLHS : x.1 ≫ (NeronModelInfra.schemeHomOverComp
        (⟨pullback.map O.g (resPt A ≫ Λ.σA) O.g (resPt A ≫ Λ.σA) (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1 (𝟙 _) (𝟙 _)
            (by rw [Category.comp_id]; exact ((O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).2).symm)
            (by rw [Category.comp_id, Category.id_comp]),
          by rw [RelativeGroupLaw.baseChangeStr, pullback.lift_snd, Category.comp_id]⟩ :
          SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g))
        (O.abqFibre 1)).1 = (toFibrePt (Λ.ptsSp (δ (F z)))).1 := by
    rw [NeronModelInfra.schemeHomOverComp_coe, ← Category.assoc,
      PtsSpelling.coe_comp_pullbackMap_eq_toFibrePt (resPt A ≫ Λ.σA) (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)) x e₁U e₂,
      PtsSpelling.toFibrePt_coe_comp_eq_toFibrePt_fibreMap, habq1, hL2]

  have hs : Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)) ≫ (resPt A ≫ Λ.σA) = (resPt A ≫ Λ.σA) := by
    haveI hP : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).mpr (Nat.prime_iff_prime_int.mp Fact.out)
    haveI := GaloisRep.isLocalization_ratLocalizedAt (p := p) Fact.out
    have hring : (frobenius (ResidueField ↥A) p).comp ((IsLocalRing.residue ↥A).comp ρ) = (IsLocalRing.residue ↥A).comp ρ :=
      IsLocalization.ringHom_ext (Ideal.span {(p : ℤ)}).primeCompl (Subsingleton.elim _ _)
    rw [hσA]
    show Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫
        Spec.map (CommRingCat.ofHom ρ) = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ Spec.map (CommRingCat.ofHom ρ)
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]
  let τF : SchemeHomOver (resPt A ≫ Λ.σA) (resPt A ≫ Λ.σA) := ⟨Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)), hs⟩

  have hFD : ∀ c : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), Λ.ptsSp (F c) = GoodReductionJacobian.schemeHomOverComp τF.1 τF.2 (Λ.ptsSp c) :=
    ModularCurve.JHNeronObjectAtP.levelData_ptsSp_frobeniusPushforward_eq_schemeHomOverComp_frobenius_ptsSp_of_hsp p M H hpM hpM2 hHp
      hj 𝔛 A hA Λ O ρ hρ hσA hsp F hF τF rfl

  have hR2 : ∀ y₁ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f,
      (toFibrePt y₁).1 ≫ pullback.lift (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) Λ.f) p 1 Fact.out hp0 ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA))
        (pullback.snd Λ.f (resPt A ≫ Λ.σA)) hFrobΛ = (toFibrePt (GoodReductionJacobian.schemeHomOverComp τF.1 τF.2 y₁)).1 := by
    intro y₁
    rw [PtsSpelling.coe_comp_relFrobenius_eq_lift_frobenius_twist (resPt A ≫ Λ.σA) Λ.f p hp0 hFrobΛ hs (toFibrePt y₁)]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, PtsSpelling.toFibrePt_coe_fst, PtsSpelling.toFibrePt_coe_fst,
        GoodReductionJacobian.schemeHomOverComp_coe]
    · rw [pullback.lift_snd]
      exact ((toFibrePt (GoodReductionJacobian.schemeHomOverComp τF.1 τF.2 y₁)).2).symm

  let w₂ : SchemeHomOver (resPt A ≫ Λ.σA) O.g := NeronModelInfra.schemeHomOverComp (Λ.ptsSp (F z)) (degPull 0)
  have hw₂ : (GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm w₂)).1 = F z := by
    have h := hpullsp 0 (Λ.ptsSp (F z))
    rw [if_pos rfl] at h
    show (GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (NeronModelInfra.schemeHomOverComp (Λ.ptsSp (F z)) (degPull 0)))).1 = F z
    rw [h, Equiv.symm_apply_apply]
  let w₃ : SchemeHomOver (resPt A ≫ Λ.σA) O.g := NeronModelInfra.schemeHomOverComp w₂ (O.hecke S (CohCarrier.Gen.dia dM))
  have hw₃ : (GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm w₃)).1 = δ (F z) := by
    have hdia := ModularCurve.JHNeronObjectAtP.ptsSp_symm_schemeHomOverComp_hecke_dia_eq_glueMap p M H hpM hj 𝔛 A hA Λ O ρ hρ hσA hsp hdia0 S dM
      hstab (O.ptsSp.symm w₂)
    rw [O.ptsSp.apply_symm_apply] at hdia
    show (GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (NeronModelInfra.schemeHomOverComp w₂ (O.hecke S (CohCarrier.Gen.dia dM))))).1 = δ (F z)
    rw [hdia, GluedPic0.toPic0Pair_glueMap_eq_blockOp]
    rcases hξ₂ : GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm w₂) with ⟨u₂, v₂⟩
    have hu₂ : u₂ = F z := by rw [← hw₂, hξ₂]
    simp only [AlgebraicCurve.Pic0Pair.blockOp_apply, AddMonoidHom.zero_apply, add_zero, DistribSMul.toAddMonoidHom_apply, hu₂, hdM, hδ]
  have hRHS : x.1 ≫ (NeronModelInfra.schemeHomOverComp (O.abqFibre 1)
        (NeronModelInfra.schemeHomOverComp
          (⟨pullback.lift (Scheme.frobenius (RelativeGroupLaw.baseChangeScheme (resPt A ≫ Λ.σA) Λ.f) p 1 Fact.out hp0 ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA)) (pullback.snd Λ.f (resPt A ≫ Λ.σA)) hFrobΛ,
            pullback.lift_snd _ _ _⟩ :
            SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f))
          (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp
          (⟨pullback.map Λ.f (resPt A ≫ Λ.σA) O.g (resPt A ≫ Λ.σA) (degPull 0).1 (𝟙 _) (𝟙 _)
              (by rw [Category.comp_id]; exact ((degPull 0).2).symm)
              (by rw [Category.comp_id, Category.id_comp]),
            by rw [RelativeGroupLaw.baseChangeStr, RelativeGroupLaw.baseChangeStr, pullback.lift_snd, Category.comp_id]⟩ :
            SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g))
          (⟨pullback.map O.g (resPt A ≫ Λ.σA) O.g (resPt A ≫ Λ.σA) (O.hecke S (CohCarrier.Gen.dia dM)).1 (𝟙 _) (𝟙 _)
              (by rw [Category.comp_id]; exact ((O.hecke S (CohCarrier.Gen.dia dM)).2).symm)
              (by rw [Category.comp_id, Category.id_comp]),
            by rw [RelativeGroupLaw.baseChangeStr, pullback.lift_snd, Category.comp_id]⟩ :
            SchemeHomOver (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g)))
          (O.abqFibre 0)))).1 = (toFibrePt (Λ.ptsSp (δ (F z)))).1 := by
    simp only [NeronModelInfra.schemeHomOverComp_coe]
    rw [hxx, ← Category.assoc, PtsSpelling.toFibrePt_coe_comp_eq_toFibrePt_fibreMap, habq1]

    rw [← Category.assoc, hR2, ← hFD, ← Category.assoc, ← Category.assoc,
      PtsSpelling.toFibrePt_coe_comp_pullbackMap (resPt A ≫ Λ.σA) (degPull 0) (Λ.ptsSp (F z)) e₁P e₂,
      PtsSpelling.toFibrePt_coe_comp_pullbackMap (resPt A ≫ Λ.σA) (O.hecke S (CohCarrier.Gen.dia dM)) _ e₁D e₂,
      PtsSpelling.toFibrePt_coe_comp_eq_toFibrePt_fibreMap, habq0]
    show (toFibrePt (Λ.ptsSp (GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm w₃)).1)).1 = _
    rw [hw₃]
  rw [hLHS, hRHS]

end S_ModularCurve_JHNeronObjectAtP_forall_point_comp_hecke_U_comp_abqFibre_one_eq_comp_abqFibre_one_comp_relFrobenius_comp_degPull_comp_hecke_dia_comp_abqFibre_zero_of_not_sq_dvd
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_forall_point_comp_hecke_U_comp_abqFibre_one_eq_comp_abqFibre_one_comp_relFrobenius_comp_degPull_comp_hecke_dia_comp_abqFibre_zero_of_not_sq_dvd (solution)
