-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_residueCarrier_of_ne_zero_of_prolongationDatum_offDiag_of_wgen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/8d0b1848-78ae-5fb7-bd8b-939cb8e67314

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_verticalUnit_atkinLehner_eq_mul_inv_residue_eq_prod_ssJSet_of_prolongationDatum_offDiag_of_wgen
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_residueCarrier_pow_of_verticalUnit_of_prolongationDatum_offDiag_of_wgen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_residueCarrier_of_ne_zero_of_prolongationDatum_offDiag_of_wgen
p2m_attr_erase "instance" "AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul"
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ValuationSubring.instIsAlgClosedResidueField ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_jqNGen ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

noncomputable section

namespace CarrierSol

section ValueGroup

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem valuation_natCast_eq_one_of_coprime {p n : ℕ} (hp : A.valuation (p : L) < 1)
    (hn : Nat.Coprime p n) : A.valuation (n : L) = 1 := by
  have hle : A.valuation (n : L) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A n)
  by_contra hne
  have hlt : A.valuation (n : L) < 1 := lt_of_le_of_ne hle hne

  have hbez : ((p : ℤ) * Nat.gcdA p n + (n : ℤ) * Nat.gcdB p n : ℤ) = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, Nat.Coprime.gcd_eq_one hn]; rfl
  have hL : (p : L) * (Nat.gcdA p n : L) + (n : L) * (Nat.gcdB p n : L) = 1 := by
    have := congrArg (fun z : ℤ => (z : L)) hbez
    push_cast at this
    exact this
  have h1 : A.valuation ((p : L) * (Nat.gcdA p n : L)) < 1 := by
    rw [map_mul]
    calc A.valuation (p : L) * A.valuation (Nat.gcdA p n : L)
        ≤ A.valuation (p : L) * 1 := by
          gcongr
          exact (A.valuation_le_one_iff _).mpr (intCast_mem A _)
      _ < 1 := by rw [mul_one]; exact hp
  have h2 : A.valuation ((n : L) * (Nat.gcdB p n : L)) < 1 := by
    rw [map_mul]
    calc A.valuation (n : L) * A.valuation (Nat.gcdB p n : L)
        ≤ A.valuation (n : L) * 1 := by
          gcongr
          exact (A.valuation_le_one_iff _).mpr (intCast_mem A _)
      _ < 1 := by rw [mul_one]; exact hlt
  have := Valuation.map_add_lt A.valuation h1 h2
  rw [hL, map_one] at this
  exact lt_irrefl _ this

theorem exists_valuation_natCast_eq_pow {p : ℕ} (hpr : p.Prime) (hp : A.valuation (p : L) < 1)
    {n : ℕ} (hn : n ≠ 0) : ∃ k : ℕ, A.valuation (n : L) = A.valuation (p : L) ^ k := by
  obtain ⟨k, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hpr.one_lt.ne'
  refine ⟨k, ?_⟩
  push_cast
  rw [map_mul, map_pow, valuation_natCast_eq_one_of_coprime A hp ((Nat.Prime.coprime_iff_not_dvd hpr).mpr hn'),
    mul_one]

theorem exists_valuation_intCast_eq_pow {p : ℕ} (hpr : p.Prime) (hp : A.valuation (p : L) < 1)
    {n : ℤ} (hn : n ≠ 0) : ∃ k : ℕ, A.valuation (n : L) = A.valuation (p : L) ^ k := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact_mod_cast exists_valuation_natCast_eq_pow A hpr hp (by exact_mod_cast hn)
  · obtain ⟨k, hk⟩ := exists_valuation_natCast_eq_pow A hpr hp (n := m) (by rintro rfl; simp at hn)
    exact ⟨k, by push_cast; rw [Valuation.map_neg]; exact hk⟩

theorem exists_pow_valuation_mul_pow_eq_pow [CharZero L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L]
    {p : ℕ} (hpr : p.Prime) (hp : A.valuation (p : L) < 1) (x : L) (hx : x ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ a b : ℕ, A.valuation x ^ m * A.valuation (p : L) ^ a = A.valuation (p : L) ^ b := by
  classical
  obtain ⟨P, hP0, hPx⟩ : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)
  set v := A.valuation with hv

  set g : ℕ → L := fun i => ((P.coeff i : ℤ) : L) * x ^ i with hg
  have hsum : ∑ i ∈ P.support, g i = 0 := by
    have h := hPx
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at h
    simpa only [hg, eq_intCast] using h
  have hne : P.support.Nonempty := Polynomial.nonempty_support_iff.mpr hP0
  have hgi : ∀ i ∈ P.support, v (g i) ≠ 0 := by
    intro i hi
    rw [Valuation.ne_zero_iff]
    exact mul_ne_zero (by exact_mod_cast Polynomial.mem_support_iff.mp hi) (pow_ne_zero _ hx)

  obtain ⟨i, hi, j, hj, hij, hvij⟩ : ∃ i ∈ P.support, ∃ j ∈ P.support, i ≠ j ∧ v (g i) = v (g j) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j, hj, hjmax⟩ := P.support.exists_max_image (fun i => v (g i)) hne
    have hlt : ∀ i ∈ P.support \ {j}, v (g i) < v (g j) := by
      intro i hi
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
      exact lt_of_le_of_ne (hjmax i hi.1) (hcon i hi.1 j hj hi.2)
    have hsumv := Valuation.map_sum_eq_of_lt v hj hlt
    rw [hsum, map_zero] at hsumv
    exact hgi j hj hsumv.symm

  wlog hlt : i < j generalizing i j
  · exact this j hj i hi hij.symm hvij.symm (lt_of_le_of_ne (not_lt.mp hlt) hij.symm)
  obtain ⟨ki, hki⟩ := exists_valuation_intCast_eq_pow A hpr hp (Polynomial.mem_support_iff.mp hi)
  obtain ⟨kj, hkj⟩ := exists_valuation_intCast_eq_pow A hpr hp (Polynomial.mem_support_iff.mp hj)
  refine ⟨j - i, Nat.sub_pos_of_lt hlt, kj, ki, ?_⟩
  have h1 : v (g i) = v (p : L) ^ ki * v x ^ i := by rw [hg]; simp only [map_mul, map_pow, hki, hv]
  have h2 : v (g j) = v (p : L) ^ kj * v x ^ j := by rw [hg]; simp only [map_mul, map_pow, hkj, hv]
  rw [h1, h2] at hvij
  have hxi : v x ^ i ≠ 0 := pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr hx)
  have : v x ^ (j - i) * v (p : L) ^ kj * v x ^ i = v (p : L) ^ ki * v x ^ i := by
    rw [hvij, mul_comm (v x ^ (j - i)), mul_assoc, ← pow_add, Nat.sub_add_cancel hlt.le]
  exact mul_right_cancel₀ hxi this

theorem exists_pow_eq_and_lt_valuation [CharZero L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] [IsAlgClosed L]
    {p : ℕ} (hpr : p.Prime) (hp : A.valuation (p : L) < 1) (hp0 : (p : L) ≠ 0)
    (c ϖ : L) (hc0 : c ≠ 0) (hc : A.valuation c < 1) (hϖ0 : ϖ ≠ 0) (hϖ : A.valuation ϖ < 1)
    (N : ℕ) (hN : 0 < N) :
    ∃ (ϖ₀ : L) (k : ℕ), 0 < k ∧ ϖ₀ ^ (N * k) = ϖ ∧ A.valuation c < A.valuation ϖ₀ ∧ A.valuation ϖ₀ < 1 := by
  set v := A.valuation with hv
  have hvp0 : 0 < v (p : L) := (Valuation.pos_iff v).mpr hp0
  obtain ⟨m, hm, a, b, hab⟩ := exists_pow_valuation_mul_pow_eq_pow A hpr hp ϖ hϖ0
  obtain ⟨m', hm', a', b', hab'⟩ := exists_pow_valuation_mul_pow_eq_pow A hpr hp c hc0

  have hlt : a < b := by
    by_contra h
    have h' : b ≤ a := not_lt.mp h
    have hvm : v ϖ ^ m < 1 := pow_lt_one₀ zero_le' hϖ hm.ne'
    have : v (p : L) ^ b < v (p : L) ^ a := by
      rw [← hab]
      calc v ϖ ^ m * v (p : L) ^ a < 1 * v (p : L) ^ a := by gcongr; exact pow_pos hvp0 a
        _ = v (p : L) ^ a := one_mul _
    exact absurd ((pow_lt_pow_iff_right_of_lt_one₀ hvp0 hp).mp this) (not_lt.mpr h')
  have hlt' : a' < b' := by
    by_contra h
    have h' : b' ≤ a' := not_lt.mp h
    have hvm : v c ^ m' < 1 := pow_lt_one₀ zero_le' hc hm'.ne'
    have : v (p : L) ^ b' < v (p : L) ^ a' := by
      rw [← hab']
      calc v c ^ m' * v (p : L) ^ a' < 1 * v (p : L) ^ a' := by gcongr; exact pow_pos hvp0 a'
        _ = v (p : L) ^ a' := one_mul _
    exact absurd ((pow_lt_pow_iff_right_of_lt_one₀ hvp0 hp).mp this) (not_lt.mpr h')
  set k := (b - a) * m' + 1 with hk
  have hk0 : 0 < k := Nat.succ_pos _
  obtain ⟨ϖ₀, hϖ₀⟩ := IsAlgClosed.exists_pow_nat_eq ϖ (Nat.mul_pos hN hk0)
  refine ⟨ϖ₀, k, hk0, hϖ₀, ?_, ?_⟩
  ·
    by_contra hge
    have hle : v ϖ₀ ≤ v c := not_lt.mp hge

    have h1 : v ϖ ^ (m * m') * v (p : L) ^ (a * m') = v (p : L) ^ (b * m') := by
      have := congrArg (fun z => z ^ m') hab
      simpa only [mul_pow, ← pow_mul] using this
    have h2 : v c ^ (m' * (N * k * m)) * v (p : L) ^ (a' * (N * k * m)) = v (p : L) ^ (b' * (N * k * m)) := by
      have := congrArg (fun z => z ^ (N * k * m)) hab'
      simpa only [mul_pow, ← pow_mul] using this
    have hϖpow : v ϖ = v ϖ₀ ^ (N * k) := by rw [← hϖ₀, map_pow]
    have hle2 : v ϖ ^ (m * m') ≤ v c ^ (m' * (N * k * m)) := by
      rw [hϖpow, ← pow_mul, show N * k * (m * m') = m' * (N * k * m) by ring]
      exact pow_le_pow_left₀ zero_le' hle _
    have key : v (p : L) ^ (b * m' + a' * (N * k * m)) ≤ v (p : L) ^ (b' * (N * k * m) + a * m') := by
      calc v (p : L) ^ (b * m' + a' * (N * k * m))
          = v ϖ ^ (m * m') * v (p : L) ^ (a * m') * v (p : L) ^ (a' * (N * k * m)) := by rw [pow_add, h1]
        _ ≤ v c ^ (m' * (N * k * m)) * v (p : L) ^ (a * m') * v (p : L) ^ (a' * (N * k * m)) := by
            gcongr
        _ = v c ^ (m' * (N * k * m)) * v (p : L) ^ (a' * (N * k * m)) * v (p : L) ^ (a * m') :=
            mul_right_comm _ _ _
        _ = v (p : L) ^ (b' * (N * k * m) + a * m') := by rw [h2, pow_add]
    have hexp : b' * (N * k * m) + a * m' ≤ b * m' + a' * (N * k * m) :=
      (pow_le_pow_iff_right_of_lt_one₀ hvp0 hp).mp key

    have hb' : 1 ≤ b' - a' := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hlt')
    have hNm : 1 ≤ N * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hN.ne' hm.ne')
    have : (b' - a') * (N * k * m) ≤ (b - a) * m' := by
      have e1 : b' * (N * k * m) = (b' - a') * (N * k * m) + a' * (N * k * m) := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hlt'.le]
      have e2 : b * m' = (b - a) * m' + a * m' := by rw [← Nat.add_mul, Nat.sub_add_cancel hlt.le]
      omega
    have h3 : (b - a) * m' < (b' - a') * (N * k * m) := by
      calc (b - a) * m' < k := Nat.lt_succ_self _
        _ = 1 * (1 * k * 1) := by ring
        _ ≤ (b' - a') * (N * k * m) := by
            have : 1 * k * 1 ≤ N * k * m := by
              calc 1 * k * 1 = k := by ring
                _ ≤ (N * m) * k := Nat.le_mul_of_pos_left k hNm
                _ = N * k * m := by ring
            exact Nat.mul_le_mul hb' this
    omega
  ·
    by_contra hge
    have hle : 1 ≤ v ϖ₀ := not_lt.mp hge
    have : 1 ≤ v ϖ := by
      rw [← hϖ₀, map_pow]
      exact one_le_pow₀ hle
    exact absurd hϖ (not_lt.mpr this)

end ValueGroup

section RUnits

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def IsRUnit (R : RegularProlongation A F Fbar) (f : F) : Prop :=
  ∃ h : f ∈ R.integers, R.residue ⟨f, h⟩ ≠ 0

variable (R : RegularProlongation A F Fbar)

theorem IsRUnit.ne_zero {R : RegularProlongation A F Fbar} {f : F} (hf : IsRUnit R f) : f ≠ 0 := by
  rintro rfl
  obtain ⟨h, hr⟩ := hf
  exact hr (by rw [show (⟨(0 : F), h⟩ : R.integers) = 0 from rfl, map_zero])

theorem isRUnit_one : IsRUnit R (1 : F) :=
  ⟨one_mem _, by rw [show (⟨(1 : F), one_mem _⟩ : R.integers) = 1 from rfl, map_one]; exact one_ne_zero⟩

theorem IsRUnit.mul {R : RegularProlongation A F Fbar} {f g : F} (hf : IsRUnit R f) (hg : IsRUnit R g) :
    IsRUnit R (f * g) := by
  obtain ⟨hf, hrf⟩ := hf
  obtain ⟨hg, hrg⟩ := hg
  refine ⟨mul_mem hf hg, ?_⟩
  rw [show (⟨f * g, mul_mem hf hg⟩ : R.integers) = ⟨f, hf⟩ * ⟨g, hg⟩ from rfl, map_mul]
  exact mul_ne_zero hrf hrg

theorem IsRUnit.pow {R : RegularProlongation A F Fbar} {f : F} (hf : IsRUnit R f) (k : ℕ) : IsRUnit R (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact isRUnit_one R
  | succ k ih => rw [pow_succ]; exact ih.mul hf

theorem IsRUnit.inv {R : RegularProlongation A F Fbar} {f : F} (hf : IsRUnit R f) : IsRUnit R f⁻¹ := by
  obtain ⟨hmem, hres⟩ := hf
  have hu : IsUnit (⟨f, hmem⟩ : R.integers) := R.isUnit_of_residue_ne_zero hres
  have hv1 : R.integers.valuation f = 1 := (R.integers.valuation_eq_one_iff ⟨f, hmem⟩).mp hu
  have hv1' : R.integers.valuation f⁻¹ = 1 := by rw [map_inv₀, hv1, inv_one]
  have hmem' : f⁻¹ ∈ R.integers := (R.integers.valuation_le_one_iff _).mp hv1'.le
  refine ⟨hmem', R.residue_ne_zero_of_isUnit ?_⟩
  exact (R.integers.valuation_eq_one_iff ⟨f⁻¹, hmem'⟩).mpr hv1'

theorem isRUnit_algebraMap {x : L} (hx : A.valuation x = 1) : IsRUnit R (algebraMap L F x) := by
  have hxA : x ∈ A := (A.valuation_le_one_iff x).mp hx.le
  have hmem : algebraMap L F x ∈ R.integers := (R.algebraMap_mem_iff x).mpr hxA
  refine ⟨hmem, ?_⟩
  have h := R.residue_algebraMap ⟨x, hxA⟩
  rw [show (⟨algebraMap L F ((⟨x, hxA⟩ : A) : L), (R.algebraMap_mem_iff _).mpr (⟨x, hxA⟩ : A).2⟩ : R.integers) =
      ⟨algebraMap L F x, hmem⟩ from rfl] at h
  rw [h, map_ne_zero_iff _ (algebraMap (ResidueField A) Fbar).injective,
    IsLocalRing.residue_ne_zero_iff_isUnit, A.valuation_eq_one_iff]
  exact hx

end RUnits

section Carriers

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {K F : Type*} [Field K] [Field F] [Algebra K F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def Supp (Q : Place K F → Prop) (h : F) : Prop := ∀ V : Place K F, V.ord h ≠ 0 → Q V

def Carr (R₁ R₂ : RegularProlongation A F Fbar) (Q : Place K F → Prop) (a : L) (h : F) : Prop :=
  IsRUnit R₁ h ∧ IsRUnit R₂ ((algebraMap L F a)⁻¹ * h) ∧ Supp Q h

variable (R₁ R₂ : RegularProlongation A F Fbar) (Q : Place K F → Prop)

theorem supp_mul {Q : Place K F → Prop} {h h' : F} (hh : h ≠ 0) (hh' : h' ≠ 0) (hs : Supp Q h) (hs' : Supp Q h') :
    Supp Q (h * h') := by
  intro V hV
  rw [Place.ord_mul _ hh hh'] at hV
  by_cases hVh : V.ord h = 0
  · rw [hVh, zero_add] at hV
    exact hs' V hV
  · exact hs V hVh

theorem supp_inv {Q : Place K F → Prop} {h : F} (hs : Supp Q h) : Supp Q h⁻¹ := by
  intro V hV
  rw [Place.ord_inv] at hV
  exact hs V (fun h0 => hV (by rw [h0, neg_zero]))

theorem supp_one : Supp Q (1 : F) := fun V hV => absurd (Place.ord_one V) hV

theorem carr_one : Carr R₁ R₂ Q (1 : L) (1 : F) := by
  refine ⟨isRUnit_one _, ?_, supp_one Q⟩
  rw [map_one, inv_one, mul_one]
  exact isRUnit_one _

variable {R₁ R₂ Q}

theorem Carr.mul {a b : L} {h h' : F} (hc : Carr R₁ R₂ Q a h) (hc' : Carr R₁ R₂ Q b h') :
    Carr R₁ R₂ Q (a * b) (h * h') := by
  obtain ⟨u1, u2, us⟩ := hc
  obtain ⟨u1', u2', us'⟩ := hc'
  refine ⟨u1.mul u1', ?_, supp_mul u1.ne_zero u1'.ne_zero us us'⟩
  have : (algebraMap L F (a * b))⁻¹ * (h * h') = ((algebraMap L F a)⁻¹ * h) * ((algebraMap L F b)⁻¹ * h') := by
    rw [map_mul, mul_inv]; ring
  rw [this]
  exact u2.mul u2'

theorem Carr.pow {a : L} {h : F} (hc : Carr R₁ R₂ Q a h) : ∀ k : ℕ, Carr R₁ R₂ Q (a ^ k) (h ^ k)
  | 0 => by rw [pow_zero, pow_zero]; exact carr_one R₁ R₂ Q
  | k + 1 => by rw [pow_succ, pow_succ]; exact (Carr.pow hc k).mul hc

theorem Carr.inv {a : L} {h : F} (hc : Carr R₁ R₂ Q a h) : Carr R₁ R₂ Q a⁻¹ h⁻¹ := by
  obtain ⟨u1, u2, us⟩ := hc
  refine ⟨u1.inv, ?_, supp_inv us⟩
  have : (algebraMap L F a⁻¹)⁻¹ * h⁻¹ = ((algebraMap L F a)⁻¹ * h)⁻¹ := by
    rw [map_inv₀, inv_inv, mul_inv, inv_inv]
  rw [this]
  exact u2.inv

theorem Carr.unit_mul {u a : L} {h : F} (hu : A.valuation u = 1) (hc : Carr R₁ R₂ Q a h) :
    Carr R₁ R₂ Q (u * a) h := by
  obtain ⟨u1, u2, us⟩ := hc
  refine ⟨u1, ?_, us⟩
  have hu' : A.valuation u⁻¹ = 1 := by rw [map_inv₀, hu, inv_one]
  have : (algebraMap L F (u * a))⁻¹ * h = algebraMap L F u⁻¹ * ((algebraMap L F a)⁻¹ * h) := by
    rw [map_mul, mul_inv, map_inv₀]; ring
  rw [this]
  exact (isRUnit_algebraMap R₂ hu').mul u2

theorem exists_carr_of_band [CharZero L] [Algebra ℚ L] [Algebra.IsAlgebraic ℚ L] [IsAlgClosed L]
    {p : ℕ} (hpr : p.Prime) (hp : A.valuation (p : L) < 1) (hp0 : (p : L) ≠ 0)
    {c : L} (hc0 : c ≠ 0) (hc : A.valuation c < 1) {N : ℕ} (hN : 0 < N)
    (band : ∀ ϖ₀ : L, A.valuation c < A.valuation ϖ₀ → A.valuation ϖ₀ < 1 → ∃ h : F, Carr R₁ R₂ Q (ϖ₀ ^ N) h)
    (ϖ : L) (hϖ : ϖ ≠ 0) : ∃ h : F, Carr R₁ R₂ Q ϖ h := by

  have carr_lt : ∀ a : L, a ≠ 0 → A.valuation a < 1 → ∃ h : F, Carr R₁ R₂ Q a h := by
    intro a ha0 ha
    obtain ⟨ϖ₀, k, hk, hroot, hband1, hband2⟩ :=
      exists_pow_eq_and_lt_valuation A hpr hp hp0 c a hc0 hc ha0 ha N hN
    obtain ⟨h₀, hh₀⟩ := band ϖ₀ hband1 hband2
    refine ⟨h₀ ^ k, ?_⟩
    have := hh₀.pow k
    rwa [← pow_mul, hroot] at this
  rcases lt_trichotomy (A.valuation ϖ) 1 with hlt | heq | hgt
  · exact carr_lt ϖ hϖ hlt
  · have hone := (carr_one R₁ R₂ Q).unit_mul heq
    rw [mul_one] at hone
    exact ⟨1, hone⟩
  · have hinv : A.valuation ϖ⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hgt
    obtain ⟨h, hh⟩ := carr_lt ϖ⁻¹ (inv_ne_zero hϖ) hinv
    have := hh.inv
    rw [inv_inv] at this
    exact ⟨h⁻¹, this⟩

end Carriers

end CarrierSol

end

open CarrierSol

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))

    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)

    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (ϖ : AlgebraicClosure ℚ) (hϖ : ϖ ≠ 0) :
    ∃ h : ↥(xHFunctionFieldBar M H), h ≠ 0 ∧
      (∃ h₁ : h ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨h, h₁⟩ ≠ 0) ∧
      (∃ h₂ : (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ϖ)⁻¹ * h ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨_, h₂⟩ ≠ 0) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        V.ord h ≠ 0 → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V → ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V →
          ∃ s ∈ SS, Psp.reduceFst α hα V = s.1) := by

  obtain ⟨G, m, c, S₀, n, e, hG₁, hc, hGres, hθG, hGY, hGinf, hGzero⟩ :=
    ModularCurve.XHDRModelAtP.exists_verticalUnit_atkinLehner_eq_mul_inv_residue_eq_prod_ssJSet_of_prolongationDatum_offDiag_of_wgen
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat'
      hO hRL hNV hθgal hβ_coe
  obtain ⟨N, hN, htwist⟩ :=
    ModularCurve.XHDRModelAtP.exists_residueCarrier_pow_of_verticalUnit_of_prolongationDatum_offDiag_of_wgen
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat'
      hO hRL hNV hθgal hβ_coe G m c S₀ n e hG₁ hc hGres hθG hGY hGinf hGzero

  have hp : (p : ℕ).Prime := Fact.out
  have hvp : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).mp hA
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨h, hu1, hu2, hs⟩ := exists_carr_of_band (R₁ := Rpd.R₁) (R₂ := Rpd.R₂)
    (Q := fun V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) =>
      ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V → ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V →
        ∃ s ∈ SS, Psp.reduceFst α hα V = s.1)
    hp hvp hp0 hc.1 hc.2 hN
    (fun ϖ₀ h1 h2 => by
      obtain ⟨h, -, hu1, hu2, hs⟩ := htwist ϖ₀ h1 h2
      exact ⟨h, hu1, hu2, hs⟩)
    ϖ hϖ
  exact ⟨h, hu1.ne_zero, hu1, hu2, hs⟩

end S_ModularCurve_XHDRModelAtP_exists_residueCarrier_of_ne_zero_of_prolongationDatum_offDiag_of_wgen
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_residueCarrier_of_ne_zero_of_prolongationDatum_offDiag_of_wgen (solution)
