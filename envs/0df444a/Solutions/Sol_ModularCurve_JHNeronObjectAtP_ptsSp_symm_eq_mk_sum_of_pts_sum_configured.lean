-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.ptsSp_symm_eq_mk_sum_of_pts_sum_configured
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/4d01b358-ad5d-59d5-9989-830afe83d678

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Theorems.Thm_ModularCurve_XHDRModelAtP_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_eq_of_isSeparated_of_valuationRing_of_fst_eq
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_eq_mk_sum_of_pts_sum_configured
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero"
p2m_attr_erase "simp" "PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_eq_mk_sum_of_pts_sum_configured.ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP"

open scoped MatrixGroups

open _root_.ModularCurve.JHNeronObjectAtP (Fbar)

namespace ModularCurve p2m_export "ModularCurve" "XHDRModelAtP XHDRModelAtP.placeOn0 XHDRModelAtP.placeOn1 mem_ssNodePairsQExp_iff xHFunctionFieldBar JH qExpFunctionFieldC jqModC JHNeronObjectAtP.LevelData JHNeronObjectAtP JZeroNeronObjectAtP XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter" namespace JHNeronObjectAtP p2m_export "ModularCurve.JHNeronObjectAtP" "Fbar LevelData ptsSp comm ssFinset mk pts surjective g pts_add separated G smooth ptsSp_add mem_ssFinset_iff L" end ModularCurve.JHNeronObjectAtP
p2m_open_scoped "ModularCurve ModularCurve.JHNeronObjectAtP" in
set_option maxHeartbeats 12800000 in

theorem ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_pts_sum_zsmul_ptsSp_symm_eq_sum
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    {ι : Type*} (t : Finset ι) (zz : ι → JH M H) (n : ι → ℤ) (ss : ι → SchemeHomOver Λ.σA O.g)
    (hss : ∀ k ∈ t, (O.pts (zz k)).1 = barPt A ≫ (ss k).1) :
    ∃ S : SchemeHomOver Λ.σA O.g,
      (O.pts (∑ k ∈ t, n k • zz k)).1 = barPt A ≫ S.1 ∧
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ S) =
        ∑ k ∈ t, n k • O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (ss k)) := by
  classical

  letI Gσ : CommGroup (SchemeHomOver Λ.σA O.g) := { O.L.pointGroup Λ.σA with mul_comm := O.comm Λ.σA }
  letI Gg : CommGroup (SchemeHomOver (genPt p) O.g) := { O.L.pointGroup (genPt p) with mul_comm := O.comm (genPt p) }
  letI Gr : CommGroup (SchemeHomOver (resPt A ≫ Λ.σA) O.g) :=
    { O.L.pointGroup (resPt A ≫ Λ.σA) with mul_comm := O.comm (resPt A ≫ Λ.σA) }

  let gen : SchemeHomOver Λ.σA O.g →* SchemeHomOver (genPt p) O.g :=
    MonoidHom.mk' (fun X => GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA X)
      (fun X Y => O.L.mul_natural Λ.σA (genPt p) (barPt A) Λ.hσA X Y)

  let φ : Multiplicative (JH M H) →* SchemeHomOver (genPt p) O.g :=
    MonoidHom.mk' (fun x => O.pts x.toAdd) (fun x y => O.pts_add x.toAdd y.toAdd)

  have R1 : ∀ U V : SchemeHomOver (resPt A ≫ Λ.σA) O.g,
      O.ptsSp.symm (O.L.mul _ U V) = O.ptsSp.symm U + O.ptsSp.symm V := by
    intro U V
    apply O.ptsSp.injective
    rw [Equiv.apply_symm_apply, O.ptsSp_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    apply Subtype.ext
    simp only [toFibrePt, ofFibrePt, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase]
    have hn := congrArg Subtype.val (O.L.mul_natural (resPt A ≫ Λ.σA) (𝟙 _ ≫ resPt A ≫ Λ.σA) (𝟙 _) rfl U V)
    rw [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp] at hn
    rw [hn]
    have hU : GoodReductionJacobian.schemeHomOverComp (𝟙 _) rfl U = overId U := Subtype.ext (Category.id_comp _)
    have hV : GoodReductionJacobian.schemeHomOverComp (𝟙 _) rfl V = overId V := Subtype.ext (Category.id_comp _)
    rw [hU, hV]
  let sp : Additive (SchemeHomOver Λ.σA O.g) →+ GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset :=
    AddMonoidHom.mk' (fun X => O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ X.toMul))
      (fun X' Y' => by
        obtain ⟨X, rfl⟩ := Additive.ofMul.surjective X'
        obtain ⟨Y, rfl⟩ := Additive.ofMul.surjective Y'
        show O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (O.L.mul Λ.σA X Y)) =
          O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ X) +
            O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ Y)
        have hn := O.L.mul_natural Λ.σA (resPt A ≫ Λ.σA) (resPt A) rfl X Y
        have e1 : ∀ W : SchemeHomOver Λ.σA O.g, GoodReductionJacobian.schemeHomOverComp (resPt A) rfl W =
            NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ W := fun W => Subtype.ext rfl
        rw [e1, e1, e1] at hn
        rw [hn, R1])

  refine ⟨∏ k ∈ t, ss k ^ n k, ?_, ?_⟩
  ·
    have hgen : ∀ k ∈ t, gen (ss k) = φ (Multiplicative.ofAdd (zz k)) := fun k hk =>
      Subtype.ext (hss k hk).symm
    have h1 : gen (∏ k ∈ t, ss k ^ n k) = φ (Multiplicative.ofAdd (∑ k ∈ t, n k • zz k)) := by
      rw [map_prod, ofAdd_sum, map_prod]
      refine Finset.prod_congr rfl fun k hk => ?_
      rw [map_zpow, hgen k hk, ofAdd_zsmul, map_zpow]
    have h2 := congrArg Subtype.val h1
    exact h2.symm
  ·
    have h1 : sp (Additive.ofMul (∏ k ∈ t, ss k ^ n k)) = ∑ k ∈ t, n k • sp (Additive.ofMul (ss k)) := by
      rw [ofMul_prod, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ofMul_zpow, map_zsmul]
    exact h1

p2m_open_scoped "ModularCurve ModularCurve.JHNeronObjectAtP" in
set_option maxHeartbeats 6400000 in

theorem ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_pts_add_sum_zsmul_ptsSp_symm_eq_add_sum
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (S₀ : SchemeHomOver Λ.σA O.g) (z₀ : JH M H) (hS₀ : (O.pts z₀).1 = barPt A ≫ S₀.1)
    {ι : Type*} (t : Finset ι) (zz : ι → JH M H) (n : ι → ℤ) (ss : ι → SchemeHomOver Λ.σA O.g)
    (hss : ∀ k ∈ t, (O.pts (zz k)).1 = barPt A ≫ (ss k).1) :
    ∃ S : SchemeHomOver Λ.σA O.g,
      (O.pts (z₀ + ∑ k ∈ t, n k • zz k)).1 = barPt A ≫ S.1 ∧
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ S) =
        O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ S₀) +
          ∑ k ∈ t, n k • O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (ss k)) := by
  classical
  obtain ⟨S, h1, h2⟩ := ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_pts_sum_zsmul_ptsSp_symm_eq_sum p M H hpM A hA Λ O
    (Finset.insertNone t) (fun o => o.elim z₀ zz) (fun o => o.elim 1 n) (fun o => o.elim S₀ ss)
    (by
      intro o ho
      rcases o with _ | k
      · exact hS₀
      · exact hss k (Finset.some_mem_insertNone.mp ho))
  refine ⟨S, ?_, ?_⟩
  · rw [Finset.sum_insertNone] at h1
    simpa only [Option.elim, one_zsmul] using h1
  · rw [Finset.sum_insertNone] at h2
    simpa only [Option.elim, one_zsmul] using h2

theorem pairsum_sum_zsmul_const {G : Type*} [AddCommGroup G] {ι : Type*} (s : Finset ι) (n : ι → ℤ) (x : G) :
    ∑ i ∈ s, n i • x = (∑ i ∈ s, n i) • x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, add_zsmul]

theorem pairsum_sum_filter_zsmul_base_eq_zero {G : Type*} [AddCommGroup G] {k : ℕ} (c : Fin k → Fin 2) (n : Fin k → ℤ)
    (β : Fin k → Fin k) (hββ : ∀ i i', c i = c i' → β i = β i') (f : Fin k → G) (j : Fin 2)
    (hn : ∑ i ∈ Finset.univ.filter (fun i => c i = j), n i = 0) :
    ∑ i ∈ Finset.univ.filter (fun i => c i = j), n i • f (β i) = 0 := by
  classical
  by_cases h : (Finset.univ.filter (fun i => c i = j)) = ∅
  · rw [h, Finset.sum_empty]
  obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr h
  have hc₀ : c i₀ = j := (Finset.mem_filter.mp hi₀).2
  rw [Finset.sum_congr rfl (fun i hi => by rw [hββ i i₀ ((Finset.mem_filter.mp hi).2.trans hc₀.symm)]), pairsum_sum_zsmul_const, hn,
    zero_zsmul]

theorem pairsum_sum_eq_sum_filter_add {G : Type*} [AddCommMonoid G] {k : ℕ} (c : Fin k → Fin 2) (f : Fin k → G) :
    ∑ i, f i = ∑ i ∈ Finset.univ.filter (fun i => c i = 0), f i + ∑ i ∈ Finset.univ.filter (fun i => c i = 1), f i := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => c i = 0)]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
  constructor
  · intro h
    have h' : (c i).val ≠ 0 := fun h' => h (Fin.ext h')
    exact Fin.ext (by have := (c i).isLt; simp only [Fin.val_one]; omega)
  · intro h h0
    rw [h] at h0
    exact absurd h0 (by decide)

p2m_open_scoped "ModularCurve ModularCurve.JHNeronObjectAtP" in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 12800000 in

theorem ModularCurve.JHNeronObjectAtP.pairsum
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    {k : ℕ} (c : Fin k → Fin 2) (n : Fin k → ℤ)
    (hn₀ : ∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i = 0)
    (hn₁ : ∑ i ∈ Finset.univ.filter (fun i => c i = 1), n i = 0)
    (β : Fin k → Fin k) (hββ : ∀ i i', c i = c i' → β i = β i')
    (plY : Fin k → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (plP : Fin k → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (Dv : ↥(Divisor.degZero (K := (AlgebraicClosure ℚ)) (F := ↥(xHFunctionFieldBar M H)))) (hDv : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = ∑ i, n i • Finsupp.single (plY i) 1)
    (x : ↥(GluingData.admissible O.ssFinset))
    (hx₁ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 = ∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i • Finsupp.single (plP i) 1)
    (hx₂ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 = ∑ i ∈ Finset.univ.filter (fun i => c i = 1), n i • Finsupp.single (plP i) 1)
    (hx₃ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0)
    (pairDv : Fin k → ↥(Divisor.degZero (K := (AlgebraicClosure ℚ)) (F := ↥(xHFunctionFieldBar M H))))
    (hpairDv : ∀ i, (pairDv i : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = Finsupp.single (plY i) 1 - Finsupp.single (plY (β i)) 1)
    (pairX : Fin k → ↥(GluingData.admissible O.ssFinset))
    (hpairX₁ : ∀ i, (pairX i : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 = if c i = 0 then Finsupp.single (plP i) 1 - Finsupp.single (plP (β i)) 1 else 0)
    (hpairX₂ : ∀ i, (pairX i : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 = if c i = 1 then Finsupp.single (plP i) 1 - Finsupp.single (plP (β i)) 1 else 0)
    (hpairX₃ : ∀ i, (pairX i : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0)
    (ss : Fin k → SchemeHomOver Λ.σA O.g)
    (hss_gen : ∀ i, (O.pts (Pic0.mk (pairDv i))).1 = barPt A ≫ (ss i).1)
    (hss_sp : ∀ i, O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (ss i)) = GluedPic0.mk O.ssFinset (pairX i)) :
    ∃ S : SchemeHomOver Λ.σA O.g,
      (O.pts (Pic0.mk Dv)).1 = barPt A ≫ S.1 ∧
      O.ptsSp.symm (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ S) = GluedPic0.mk O.ssFinset x := by
  classical
  obtain ⟨S, hS, hSx⟩ := ModularCurve.JHNeronObjectAtP.exists_schemeHomOver_pts_sum_zsmul_ptsSp_symm_eq_sum p M H hpM A hA Λ O
    Finset.univ (fun i => Pic0.mk (pairDv i)) n ss (fun i _ => hss_gen i)

  let mkH : ↥(Divisor.degZero (K := (AlgebraicClosure ℚ)) (F := ↥(xHFunctionFieldBar M H))) →+ JH M H := QuotientAddGroup.mk' _
  have hmkH : ∀ D : ↥(Divisor.degZero (K := (AlgebraicClosure ℚ)) (F := ↥(xHFunctionFieldBar M H))), mkH D = Pic0.mk D := fun _ => rfl
  have hgen : ∑ i, n i • Pic0.mk (pairDv i) = Pic0.mk Dv := by
    have h1 : mkH (∑ i, n i • pairDv i) = mkH Dv := by
      refine congrArg mkH (Subtype.ext ?_)
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [AddSubgroupClass.coe_zsmul, hpairDv, hDv, smul_sub, Finset.sum_sub_distrib]
      rw [sub_eq_self, pairsum_sum_eq_sum_filter_add c,
        pairsum_sum_filter_zsmul_base_eq_zero c n β hββ (fun i => (Finsupp.single (plY i) 1 : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) 0 hn₀,
        pairsum_sum_filter_zsmul_base_eq_zero c n β hββ (fun i => (Finsupp.single (plY i) 1 : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) 1 hn₁, add_zero]
    rw [map_sum] at h1
    simp only [map_zsmul, hmkH] at h1
    exact h1

  have hsp : ∑ i, n i • GluedPic0.mk O.ssFinset (pairX i) = GluedPic0.mk O.ssFinset x := by
    have h1 : GluedPic0.mk O.ssFinset (∑ i, n i • pairX i) = GluedPic0.mk O.ssFinset x := by
      refine congrArg (GluedPic0.mk O.ssFinset) (Subtype.ext (Prod.ext ?_ (Prod.ext ?_ ?_)))
      · rw [AddSubmonoidClass.coe_finsetSum, Prod.fst_sum, hx₁]
        simp only [AddSubgroupClass.coe_zsmul, Prod.smul_fst, hpairX₁, smul_ite, smul_zero, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          smul_sub, Finset.sum_sub_distrib]
        rw [pairsum_sum_filter_zsmul_base_eq_zero c n β hββ (fun i => (Finsupp.single (plP i) 1 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) 0 hn₀, sub_zero]
      · rw [AddSubmonoidClass.coe_finsetSum, Prod.snd_sum, Prod.fst_sum, hx₂]
        simp only [AddSubgroupClass.coe_zsmul, Prod.smul_snd, Prod.smul_fst, hpairX₂, smul_ite, smul_zero, Finset.sum_ite,
          Finset.sum_const_zero, add_zero, smul_sub, Finset.sum_sub_distrib]
        rw [pairsum_sum_filter_zsmul_base_eq_zero c n β hββ (fun i => (Finsupp.single (plP i) 1 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))) 1 hn₁, sub_zero]
      · rw [AddSubmonoidClass.coe_finsetSum, Prod.snd_sum, Prod.snd_sum, hx₃]
        simp only [AddSubgroupClass.coe_zsmul, Prod.smul_snd, hpairX₃, smul_zero, Finset.sum_const_zero]
    rw [map_sum] at h1
    simp only [map_zsmul] at h1
    exact h1
  refine ⟨S, ?_, ?_⟩
  · rw [← hgen]; exact hS
  · rw [hSx]
    exact (Finset.sum_congr rfl fun i _ => by rw [hss_sp i]).trans hsp

namespace F2aAux

theorem placeOfPoint_ne_placeOn_of_smooth
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (i : Fin 2)
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (husm : Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) :
    (𝔛.Mfib A hA ρ hρ).placeOfPoint P ≠ (if i = 0 then 𝔛.placeOn0 A hA ρ hρ n else 𝔛.placeOn1 A hA ρ hρ n) := by

  have hsm : uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∈
      (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ))) ⁻¹ᵁ 𝔛.smoothLocus) := by
    show (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
      (uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))
    rw [← Scheme.Hom.comp_apply, huκ₁, Scheme.Hom.comp_apply]
    exact husm ⟨_, rfl⟩
  have hnot := (ModularCurve.XHDRModelAtP.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter p M H hpM hpM2 hj 𝔛 A hA ρ hρ _).1 hsm
  rw [← hP] at hnot
  obtain ⟨⟨hb, hbpl⟩, ⟨ha, hapl⟩⟩ := 𝔛.node_pin A hA ρ hρ n
  have hinvE : ∀ z, (𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hcond : (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) =
      (𝔛.comp A hA ρ hρ 1).base ((pullback.snd (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) := by
    have := congrArg (fun f => f.base n) (pullback.condition (f := 𝔛.comp A hA ρ hρ 0) (g := 𝔛.comp A hA ρ hρ 1))
    simpa only [Scheme.Hom.comp_apply] using this
  intro heq
  apply hnot
  fin_cases i
  ·
    simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte] at heq ⊢
    have hPeq : P = ⟨_, ha⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.1 (heq.trans hapl.symm)
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [hPeq, Scheme.Hom.comp_apply]
    show (𝔛.comp A hA ρ hρ 0).base ((𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base _)) ∈ _
    rw [hinvE, hcond]
    exact ⟨_, rfl⟩
  ·
    simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte] at heq ⊢
    have hPeq : P = ⟨_, hb⟩ := (𝔛.Mfib A hA ρ hρ).placeOfPoint_bijective.1 (heq.trans hbpl.symm)
    refine ⟨?_, ⟨_, rfl⟩⟩
    rw [hPeq, Scheme.Hom.comp_apply]
    show (𝔛.comp A hA ρ hρ 1).base ((𝔛.efib A hA ρ hρ).base ((inv (𝔛.efib A hA ρ hρ)).base _)) ∈ _
    rw [hinvE, ← hcond]
    exact ⟨_, rfl⟩

end F2aAux

open _root_.ModularCurve.JHNeronObjectAtP (Fbar)

set_option synthInstance.maxHeartbeats 6400000 in
set_option maxHeartbeats 32000000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
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

    (k : ℕ) (c : Fin k → Fin 2)
    (y : Fin k → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : Fin k → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : ∀ i, barPt A ≫ (u i).1 = (y i).1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (husm : ∀ i, Set.range (u i).1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ : Fin k → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)))
    (huκ₁ : ∀ i, uκ i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (u i).1)
    (huκ₂ : ∀ i, uκ i ≫ pullback.snd _ _ = 𝟙 _)
    (P : Fin k → closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : ∀ i, (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ (c i)).base (P i).1 = (uκ i).base (IsLocalRing.closedPoint (ResidueField ↥A)))

    (n : Fin k → ℤ)
    (hn₀ : ∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i = 0)
    (hn₁ : ∑ i ∈ Finset.univ.filter (fun i => c i = 1), n i = 0)

    (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
    (hDv : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = ∑ i, n i • Finsupp.single (𝔛.Meta.pointEquivPlace (y i)) 1)
    (x : ↥(GluingData.admissible O.ssFinset))
    (hx₁ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
      ∑ i ∈ Finset.univ.filter (fun i => c i = 0), n i • Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint (P i)) 1)
    (hx₂ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
      ∑ i ∈ Finset.univ.filter (fun i => c i = 1), n i • Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint (P i)) 1)
    (hx₃ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0) :
    (∃ s : SchemeHomOver Λ.σA O.g, (O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1) ∧
    ∀ s : SchemeHomOver Λ.σA O.g, (O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1 →
      O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset x := by
  classical

  haveI hCO : IsCurveOver (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      (𝔛.Mfib A hA ρ hρ).toBase (𝔛.Mfib A hA ρ hρ).ffEquiv (𝔛.Mfib A hA ρ hρ).ffEquiv_algebraMap
  have hdegF : ∀ v : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)), v.deg = 1 := fun v => by
    haveI := IsCurveOver.finiteResidue (K := ResidueField ↥A) (F := Fbar p M H hpM (ResidueField ↥A)) v
    exact (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField v).mpr
      IsAlgClosed.algebraMap_bijective_of_isIntegral.2
  haveI hCOgen : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    AlgebraicCurve.isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      𝔛.Meta.toBase 𝔛.Meta.ffEquiv 𝔛.Meta.ffEquiv_algebraMap
  have hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), v.deg = 1 := fun v => by
    haveI := IsCurveOver.finiteResidue (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) v
    exact (AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField v).mpr
      IsAlgClosed.algebraMap_bijective_of_isIntegral.2
  have hpdeg : ∀ {K F : Type} [Field K] [Field F] [Algebra K F] (hdeg : ∀ v : Place K F, v.deg = 1) (P Q : Place K F),
      (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor K F) ∈ Divisor.degZero (K := K) (F := F) ∧
      ∀ w : Place K F, P ≠ w → Q ≠ w → (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor K F) w = 0 := by
    intro K F _ _ _ hdeg P Q
    refine ⟨?_, fun w hP hQ => ?_⟩
    · rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg, hdeg, sub_self]
    · rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply, if_neg hP, if_neg hQ, sub_zero]

  have hoffSS : ∀ (i : Fin k) (s : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))), s ∈ O.ssFinset →
      (c i = 0 → (𝔛.Mfib A hA ρ hρ).placeOfPoint (P i) ≠ s.1) ∧ (c i = 1 → (𝔛.Mfib A hA ρ hρ).placeOfPoint (P i) ≠ s.2) := by
    intro i s hs
    have hs' := (O.mem_ssFinset_iff s).1 hs
    rw [mem_ssNodePairsQExp_iff] at hs'
    obtain ⟨hy, hs1⟩ := hs'
    have hoff := F2aAux.placeOfPoint_ne_placeOn_of_smooth p M H hpM hpM2 hj 𝔛 A hA ρ hρ (c i) (u i) (husm i) (uκ i) (huκ₁ i) (P i) (hP i)
      ((𝔛.nodeEquiv A hA ρ hρ).symm ⟨s.2, hy⟩)
    constructor
    · intro hc
      rw [hc] at hoff
      simpa only [Fin.isValue, ↓reduceIte, XHDRModelAtP.placeOn0, Equiv.apply_symm_apply, ← hs1] using hoff
    · intro hc
      rw [hc] at hoff
      simpa only [Fin.isValue, one_ne_zero, ↓reduceIte, XHDRModelAtP.placeOn1, Equiv.apply_symm_apply] using hoff

  let β : Fin k → Fin k := fun i => Classical.choose (⟨i, rfl⟩ : ∃ i', c i' = c i)
  have hβc : ∀ i, c (β i) = c i := fun i => Classical.choose_spec (⟨i, rfl⟩ : ∃ i', c i' = c i)
  have hββ : ∀ i i', c i = c i' → β i = β i' := by
    intro i i' h
    show Classical.choose _ = Classical.choose _
    congr 1
    · rw [h]

  have hpairadm : ∀ i, (((if c i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint (P i)) 1 -
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint (P (β i))) 1 else 0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),
      (if c i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint (P i)) 1 -
        Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint (P (β i))) 1 else 0 : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),
      (0 : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)) : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) ∈ GluingData.admissible O.ssFinset := by
    intro i
    have hd := hpdeg hdegF ((𝔛.Mfib A hA ρ hρ).placeOfPoint (P i)) ((𝔛.Mfib A hA ρ hρ).placeOfPoint (P (β i)))
    rw [GluingData.mem_admissible]
    refine ⟨?_, ?_, fun s hs => ⟨?_, ?_⟩⟩
    · show (if c i = 0 then _ else _ : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) ∈ _
      split_ifs
      · exact hd.1
      · exact zero_mem _
    · show (if c i = 1 then _ else _ : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) ∈ _
      split_ifs
      · exact hd.1
      · exact zero_mem _
    · show (if c i = 0 then _ else _ : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) s.1 = 0
      split_ifs with hc
      · exact hd.2 s.1 ((hoffSS i s hs).1 hc) ((hoffSS (β i) s hs).1 ((hβc i).trans hc))
      · rfl
    · show (if c i = 1 then _ else _ : Divisor (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) s.2 = 0
      split_ifs with hc
      · exact hd.2 s.2 ((hoffSS i s hs).2 hc) ((hoffSS (β i) s hs).2 ((hβc i).trans hc))
      · rfl
  have hpair : ∀ i, ∃ s : SchemeHomOver Λ.σA O.g,
      (O.pts (Pic0.mk ⟨Finsupp.single (𝔛.Meta.pointEquivPlace (y i)) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace (y (β i))) 1,
        (hpdeg hdeg1 _ _).1⟩)).1 = barPt A ≫ s.1 ∧
      O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset ⟨_, hpairadm i⟩ := by
    intro i
    exact hsp (c i) (y i) (u i) (hu i) (husm i) (uκ i) (huκ₁ i) (huκ₂ i) (P i) (hP i)
      (y (β i)) (u (β i)) (hu (β i)) (husm (β i)) (uκ (β i)) (huκ₁ (β i)) (huκ₂ (β i)) (P (β i)) (by rw [← hβc i]; exact hP (β i))
      ⟨_, _⟩ rfl ⟨_, hpairadm i⟩ rfl rfl rfl
  choose ss hss_gen hss_sp using hpair

  have hPAIRSUM : ∃ S : SchemeHomOver Λ.σA O.g, (O.pts (Pic0.mk Dv)).1 = barPt A ≫ S.1 ∧
      O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ S) = GluedPic0.mk O.ssFinset x :=
    ModularCurve.JHNeronObjectAtP.pairsum p M H hpM A hA Λ O c n hn₀ hn₁ β hββ
      (fun i => 𝔛.Meta.pointEquivPlace (y i)) (fun i => (𝔛.Mfib A hA ρ hρ).placeOfPoint (P i))
      Dv hDv x hx₁ hx₂ hx₃ (fun i => ⟨_, (hpdeg hdeg1 _ _).1⟩) (fun i => rfl) (fun i => ⟨_, hpairadm i⟩)
      (fun i => rfl) (fun i => rfl) (fun i => rfl) ss hss_gen hss_sp

  obtain ⟨S, hSgen, hSsp⟩ := hPAIRSUM
  refine ⟨⟨S, hSgen⟩, fun s hs => ?_⟩
  haveI : IsSeparated O.g := O.separated
  letI : Algebra (R p) ↥A := ρ.toAlgebra
  have hgen_eq : Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) ≫ s.1 =
      Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) ≫ S.1 := by
    show barPt A ≫ _ = barPt A ≫ _
    rw [← hs, ← hSgen]
  have hsS := @AlgebraicGeometry.SchemeHomOver.eq_of_isSeparated_of_valuationRing_of_fst_eq (R p) _ O.G O.g _ ↥A _ _ _ _
    (AlgebraicClosure ℚ) _ _ _ _ (IsScalarTower.of_algebraMap_eq' hρ.symm) ⟨s.1, s.2.trans hσA⟩ ⟨S.1, S.2.trans hσA⟩ hgen_eq
  have hsS0 : s.1 = S.1 := by
    have h := congrArg Subtype.val hsS
    exact h
  have hsS1 : s = S := Subtype.ext hsS0
  rw [hsS1, hSsp]

end S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_eq_mk_sum_of_pts_sum_configured
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_ptsSp_symm_eq_mk_sum_of_pts_sum_configured (solution)
