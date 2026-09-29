-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.cuspLawInfty_prolongationDatum_offDiag_of_residue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/7e04b211-a0b0-5f30-ae9e-c9ede07d2ebe

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_XHDRModelAtP_mapDomain_reduceFst_eq_ord_add_ord_of_norm_prolongationDatum
import Theorems.Thm_ModularCurve_XHDRModelAtP_cuspLocalSemicontinuity_prolongationDatum_of_residue
import Theorems.Thm_ModularCurve_XHDRModelAtP_strongPoleCancellation_prolongationDatum
import Theorems.Thm_ModularCurve_XHDRModelAtP_not_isAffinePlace_reduceFst_of_isInftySide_prolongationDatum
import Theorems.Thm_ModularCurve_XHDRModelAtP_isCuspidal_of_not_isAffinePlace_reduceFst_prolongationDatum
import Theorems.Thm_ModularCurve_XHDRModelAtP_reduceFst_eq_frob_reduceSnd_of_isZeroSide_prolongationDatum
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffinePlace_prolongationDatum
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_not_isInftySide_of_isZeroSide
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_cuspLawInfty_prolongationDatum_offDiag_of_residue
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.TwoChart.isOpenImmersion_fInf ModularCurve.TwoChart.isOpenImmersion_ιFin ModularCurve.TwoChart.isOpenImmersion_ιInf ModularCurve.TwoChart.isOpenImmersion_fFin ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.toRingAut_coeffSemilinearAut"
p2m_attr_erase "simp" "ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.TwoChart.coe_jChartFin ModularCurve.TwoChart.ιFin_modelTo ModularCurve.TwoChart.ιInf_modelTo ModularCurve.TwoChart.ιInf_modelTo_assoc ModularCurve.TwoChart.coe_jInvChartInf ModularCurve.TwoChart.ιFin_modelTo_assoc ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace Ws49
namespace CuspLawInfH

theorem mapDomain_apply_eq_sum {ι κ' : Type*} (r : ι → κ') [DecidableEq κ'] (D : ι →₀ ℤ) (b : κ') :
    Finsupp.mapDomain r D b = ∑ a ∈ D.support with r a = b, D a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [Finsupp.sum, Finsupp.single_apply]
  rw [Finset.sum_filter]

theorem mapDomain_filter_apply {ι κ' : Type*} (r : ι → κ') (q : ι → Prop) [DecidablePred q]
    [DecidableEq κ'] (D : ι →₀ ℤ) (b : κ') :
    Finsupp.mapDomain r (D.filter q) b = ∑ a ∈ D.support with (q a ∧ r a = b), D a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [Finsupp.sum, Finsupp.support_filter, Finsupp.filter_apply, Finsupp.single_apply]
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hp : q a <;> by_cases hr : r a = b <;> simp [hp, hr]

open Classical in

theorem sum_not_fst_eq {ι σ : Type*} (rF rS : ι → σ) (P₁ P₂ : ι → Prop) (D : ι →₀ ℤ) (b : σ) (u : σ)
    (h12 : ∀ W, rF W = b → ¬ P₁ W → (P₂ W ∧ rS W = u)) (h21 : ∀ W, P₂ W → rS W = u → (rF W = b ∧ ¬ P₁ W)) :
    (∑ W ∈ D.support with (rF W = b ∧ ¬ P₁ W), D W) = Finsupp.mapDomain rS (D.filter P₂) u := by
  rw [mapDomain_filter_apply]
  refine Finset.sum_congr (Finset.filter_congr (fun W _ => ?_)) (fun _ _ => rfl)
  constructor
  · rintro ⟨hW, hns⟩
    exact h12 W hW hns
  · rintro ⟨hz, hWu⟩
    exact h21 W hz hWu

open Classical in

theorem fst_add_snd_eq {ι σ : Type*} (rF rS : ι → σ) (P₁ P₂ : ι → Prop) (D : ι →₀ ℤ) (b : σ) (u : σ) (T : ℤ)
    (h12 : ∀ W, rF W = b → ¬ P₁ W → (P₂ W ∧ rS W = u)) (h21 : ∀ W, P₂ W → rS W = u → (rF W = b ∧ ¬ P₁ W))
    (hall : Finsupp.mapDomain rF D b = T) :
    Finsupp.mapDomain rF (D.filter P₁) b + Finsupp.mapDomain rS (D.filter P₂) u = T := by
  rw [mapDomain_apply_eq_sum] at hall
  rw [mapDomain_filter_apply, ← sum_not_fst_eq rF rS P₁ P₂ D b u h12 h21]
  have hsplit := Finset.sum_filter_add_sum_filter_not (D.support.filter (fun W => rF W = b)) (fun W => P₁ W) (fun W => D W)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have hside : (∑ W ∈ D.support with (P₁ W ∧ rF W = b), D W) = ∑ W ∈ D.support with (rF W = b ∧ P₁ W), D W :=
    Finset.sum_congr (Finset.filter_congr (fun W _ => and_comm)) (fun _ _ => rfl)
  rw [hside, hsplit, hall]

theorem ne_zero_of_residue_ne_zero {L : Type*} [Field L] {A : ValuationSubring L} {F Fb : Type*} [Field F] [Algebra L F] [Field Fb]
    [Algebra (IsLocalRing.ResidueField ↥A) Fb]
    (R : RegularProlongation A F Fb) {f : F} (h : f ∈ R.integers) (hr : R.residue ⟨f, h⟩ ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact hr (map_zero R.residue)

theorem residue_mk_mul {L : Type*} [Field L] {A : ValuationSubring L} {F Fb : Type*} [Field F] [Algebra L F] [Field Fb]
    [Algebra (IsLocalRing.ResidueField ↥A) Fb]
    (R : RegularProlongation A F Fb) {f g : F} (hf : f ∈ R.integers) (hg : g ∈ R.integers) :
    R.residue ⟨f * g, R.integers.mul_mem _ _ hf hg⟩ = R.residue ⟨f, hf⟩ * R.residue ⟨g, hg⟩ := by
  rw [← map_mul]
  rfl

theorem isCurveOver_xHFunctionFieldBar (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) :
    IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar N H') :=
  (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) N H').1

open Classical in

theorem cuspLaw_of_poleFree {L : Type*} [Field L] {A : ValuationSubring L} {F Fb : Type*} [Field F] [Algebra L F] [Field Fb]
    [Algebra (IsLocalRing.ResidueField ↥A) Fb] [HasPrincipalDivisors L F]
    (R₁ R₂ : RegularProlongation A F Fb)
    (rF rS : Place L F → Place (IsLocalRing.ResidueField ↥A) Fb) (P₁ P₂ : Place L F → Prop)
    (Q : Place (IsLocalRing.ResidueField ↥A) Fb → Prop)
    (φ : Place (IsLocalRing.ResidueField ↥A) Fb → Place (IsLocalRing.ResidueField ↥A) Fb) (hφ : Function.Surjective φ)
    (hS1 : ∀ c, P₁ c → Q (rF c))
    (hS3 : ∀ u W, P₂ W → rS W = u → rF W = φ u)
    (pole_free : ∀ (g : F) (h₁ : g ∈ R₁.integers) (h₂ : g ∈ R₂.integers), R₁.residue ⟨g, h₁⟩ ≠ 0 → R₂.residue ⟨g, h₂⟩ ≠ 0 →
      ∀ E : Divisor L F, (∀ W, E W = W.ord g) → ∀ u, Q (φ u) →
        (∀ W, P₁ W → rF W = φ u → 0 ≤ E W) → (∀ W, P₂ W → rS W = u → 0 ≤ E W) →
        Finsupp.mapDomain rF (E.filter P₁) (φ u) = (φ u).ord (R₁.residue ⟨g, h₁⟩))
    (hpcc : ∀ (f : F), f ≠ 0 → ∀ u, ∃ (h : F) (hh₁ : h ∈ R₁.integers) (hh₂ : h ∈ R₂.integers),
      R₁.residue ⟨h, hh₁⟩ ≠ 0 ∧ R₂.residue ⟨h, hh₂⟩ ≠ 0 ∧ (∀ W, rF W = φ u → 0 ≤ W.ord h) ∧ (∀ W, rF W = φ u → 0 ≤ W.ord (f * h)))
    (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers) (hr₁ : R₁.residue ⟨f, h₁⟩ ≠ 0) (hr₂ : R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor L F) (hD : ∀ W, D W = W.ord f) (c : Place L F) (hc : P₁ c) :
    Finsupp.mapDomain rF (D.filter P₁) (rF c) = (rF c).ord (R₁.residue ⟨f, h₁⟩) := by
  have hv : Q (rF c) := hS1 c hc
  obtain ⟨u, hu_eq⟩ := hφ (rF c)
  rw [← hu_eq] at hv ⊢
  have hf0 : f ≠ 0 := ne_zero_of_residue_ne_zero R₁ h₁ hr₁
  obtain ⟨h, hh₁, hh₂, hs₁, hs₂, hph, hpfh⟩ := hpcc f hf0 u
  have hh0 : h ≠ 0 := ne_zero_of_residue_ne_zero R₁ hh₁ hs₁
  obtain ⟨E, hE, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) h hh0
  have hDE : ∀ W, (D + E) W = W.ord (f * h) := by
    intro W
    rw [Finsupp.add_apply, hD W, hE W, W.ord_mul hf0 hh0]
  have hfh₁ : f * h ∈ R₁.integers := R₁.integers.mul_mem _ _ h₁ hh₁
  have hfh₂ : f * h ∈ R₂.integers := R₂.integers.mul_mem _ _ h₂ hh₂
  have hres : R₁.residue ⟨f * h, hfh₁⟩ = R₁.residue ⟨f, h₁⟩ * R₁.residue ⟨h, hh₁⟩ := residue_mk_mul R₁ h₁ hh₁
  have hrfh₁ : R₁.residue ⟨f * h, hfh₁⟩ ≠ 0 := by rw [hres]; exact mul_ne_zero hr₁ hs₁
  have hrfh₂ : R₂.residue ⟨f * h, hfh₂⟩ ≠ 0 := by rw [residue_mk_mul R₂ h₂ hh₂]; exact mul_ne_zero hr₂ hs₂
  have hA' := pole_free (f * h) hfh₁ hfh₂ hrfh₁ hrfh₂ (D + E) hDE u hv
    (fun W _ hWu => by rw [hDE W]; exact hpfh W hWu)
    (fun W hW hWu => by rw [hDE W]; exact hpfh W (hS3 u W hW hWu))
  have hB' := pole_free h hh₁ hh₂ hs₁ hs₂ E hE u hv
    (fun W _ hWu => by rw [hE W]; exact hph W hWu)
    (fun W hW hWu => by rw [hE W]; exact hph W (hS3 u W hW hWu))
  rw [Finsupp.filter_add, Finsupp.mapDomain_add, Finsupp.add_apply, hB', hres, (φ u).ord_mul hr₁ hs₁] at hA'
  omega

open Classical in

theorem cuspLawInfty_generic {L : Type*} [Field L] {A : ValuationSubring L} {F Fb : Type*} [Field F] [Algebra L F] [Field Fb]
    [Algebra (IsLocalRing.ResidueField ↥A) Fb] [HasPrincipalDivisors L F]
    (R₁ R₂ : RegularProlongation A F Fb)
    (rF rS : Place L F → Place (IsLocalRing.ResidueField ↥A) Fb) (P₁ P₂ Cu : Place L F → Prop)
    (Af : Place (IsLocalRing.ResidueField ↥A) Fb → Prop)
    (φ : Place (IsLocalRing.ResidueField ↥A) Fb → Place (IsLocalRing.ResidueField ↥A) Fb) (hφ : Function.Bijective φ)
    (hNI : ∀ (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers), R₁.residue ⟨f, h₁⟩ ≠ 0 → R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor L F, (∀ W, D W = W.ord f) → ∀ u,
        Finsupp.mapDomain rF D (φ u) = (φ u).ord (R₁.residue ⟨f, h₁⟩) + u.ord (R₂.residue ⟨f, h₂⟩))
    (hS1 : ∀ c, P₁ c → ¬ Af (rF c))
    (hCusp : ∀ W, ¬ Af (rF W) → Cu W)
    (hDicho : ∀ W, Cu W → P₁ W ∨ P₂ W)
    (hDisj : ∀ W, P₂ W → ¬ P₁ W)
    (hSide : ∀ W, P₂ W → rF W = φ (rS W))
    (hS4 : ∀ u, ¬ Af (φ u) → (∃ c, P₁ c ∧ rF c = φ u) ∧ (∃ c, P₂ c ∧ rS c = u))
    (hL1 : ∀ (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers), R₁.residue ⟨f, h₁⟩ ≠ 0 → R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor L F, (∀ W, D W = W.ord f) → ∀ v,
        (∃ c, P₁ c ∧ rF c = v) → (∀ W, P₁ W → rF W = v → 0 ≤ D W) →
        Finsupp.mapDomain rF (D.filter P₁) v ≤ v.ord (R₁.residue ⟨f, h₁⟩))
    (hL2 : ∀ (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers), R₁.residue ⟨f, h₁⟩ ≠ 0 → R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ D : Divisor L F, (∀ W, D W = W.ord f) → ∀ u,
        (∃ c, P₂ c ∧ rS c = u) → (∀ W, P₂ W → rS W = u → 0 ≤ D W) →
        Finsupp.mapDomain rS (D.filter P₂) u ≤ u.ord (R₂.residue ⟨f, h₂⟩))
    (hpcc : ∀ (f : F), f ≠ 0 → ∀ u, ∃ (h : F) (hh₁ : h ∈ R₁.integers) (hh₂ : h ∈ R₂.integers),
      R₁.residue ⟨h, hh₁⟩ ≠ 0 ∧ R₂.residue ⟨h, hh₂⟩ ≠ 0 ∧ (∀ W, rF W = φ u → 0 ≤ W.ord h) ∧ (∀ W, rF W = φ u → 0 ≤ W.ord (f * h)))
    (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers) (hr₁ : R₁.residue ⟨f, h₁⟩ ≠ 0) (hr₂ : R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor L F) (hD : ∀ W, D W = W.ord f) (c : Place L F) (hc : P₁ c) :
    Finsupp.mapDomain rF (D.filter P₁) (rF c) = (rF c).ord (R₁.residue ⟨f, h₁⟩) := by

  have hS3 : ∀ u W, P₂ W → rS W = u → (rF W = φ u ∧ ¬ P₁ W) := by
    intro u W hz hWu
    exact ⟨by rw [hSide W hz, hWu], hDisj W hz⟩
  have hS2 : ∀ u W, ¬ Af (φ u) → rF W = φ u → ¬ P₁ W → (P₂ W ∧ rS W = u) := by
    intro u W hu hW hns
    have hcW : Cu W := hCusp W (by rw [hW]; exact hu)
    rcases hDicho W hcW with hinf | hz
    · exact (hns hinf).elim
    · refine ⟨hz, hφ.1 ?_⟩
      rw [← hSide W hz, hW]

  have two_side : ∀ (g : F) (h₁ : g ∈ R₁.integers) (h₂ : g ∈ R₂.integers), R₁.residue ⟨g, h₁⟩ ≠ 0 → R₂.residue ⟨g, h₂⟩ ≠ 0 →
      ∀ E : Divisor L F, (∀ W, E W = W.ord g) → ∀ u, ¬ Af (φ u) →
        Finsupp.mapDomain rF (E.filter P₁) (φ u) + Finsupp.mapDomain rS (E.filter P₂) u =
          (φ u).ord (R₁.residue ⟨g, h₁⟩) + u.ord (R₂.residue ⟨g, h₂⟩) :=
    fun g h₁ h₂ hr₁ hr₂ E hE u hu =>
      fst_add_snd_eq _ _ _ _ E _ u _ (fun W hW hns => hS2 u W hu hW hns) (fun W hz hWu => hS3 u W hz hWu) (hNI g h₁ h₂ hr₁ hr₂ E hE u)

  have pole_free : ∀ (g : F) (h₁ : g ∈ R₁.integers) (h₂ : g ∈ R₂.integers), R₁.residue ⟨g, h₁⟩ ≠ 0 → R₂.residue ⟨g, h₂⟩ ≠ 0 →
      ∀ E : Divisor L F, (∀ W, E W = W.ord g) → ∀ u, ¬ Af (φ u) →
        (∀ W, P₁ W → rF W = φ u → 0 ≤ E W) → (∀ W, P₂ W → rS W = u → 0 ≤ E W) →
        Finsupp.mapDomain rF (E.filter P₁) (φ u) = (φ u).ord (R₁.residue ⟨g, h₁⟩) := by
    intro g h₁ h₂ hr₁ hr₂ E hE u hu hp₁ hp₂
    have hkey := two_side g h₁ h₂ hr₁ hr₂ E hE u hu
    obtain ⟨hex_inf, hex_zero⟩ := hS4 u hu
    have hl₁ := hL1 g h₁ h₂ hr₁ hr₂ E hE (φ u) hex_inf hp₁
    have hl₂ := hL2 g h₁ h₂ hr₁ hr₂ E hE u hex_zero hp₂
    omega
  exact cuspLaw_of_poleFree R₁ R₂ rF rS P₁ P₂ (fun v => ¬ Af v) φ hφ.2 hS1 (fun u W hz hWu => (hS3 u W hz hWu).1)
    pole_free hpcc f h₁ h₂ hr₁ hr₂ D hD c hc

end Ws49.CuspLawInfH

open Ws49.CuspLawInfH in
open Classical in
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

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

    (hcomp : (∀ (i : Fin 2)
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
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)))

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
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0)) :
    Rpd.CuspLawInfty α hα := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := isCurveOver_xHFunctionFieldBar M H

  have hN := ModularCurve.XHDRModelAtP.exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hres₂α
  have hNI := ModularCurve.XHDRModelAtP.mapDomain_reduceFst_eq_ord_add_ord_of_norm_prolongationDatum p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcomp hN
  have hL := ModularCurve.XHDRModelAtP.cuspLocalSemicontinuity_prolongationDatum_of_residue p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hres₂α hcomp
  unfold JHPlaceSpecialization.ProlongationDatum.CuspLawInfty
  intro f h₁ h₂ hr₁ hr₂ D hD c hc
  exact cuspLawInfty_generic Rpd.R₁ Rpd.R₂ (Psp.reduceFst α hα) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A)) (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p)
    (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (ΓN p M H hpM))
    hNI
    (fun c hc => ModularCurve.XHDRModelAtP.not_isAffinePlace_reduceFst_of_isInftySide_prolongationDatum p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcomp c hc)
    (fun W hW => ModularCurve.XHDRModelAtP.isCuspidal_of_not_isAffinePlace_reduceFst_prolongationDatum p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcomp W hW)
    (fun W hW => ModularCurve.JHPlaceSpecialization.isInftySide_or_isZeroSide_of_isCuspidal p M H hpM A hA W hW)
    (fun W hW => ModularCurve.JHPlaceSpecialization.not_isInftySide_of_isZeroSide p M H hpM A hA W hW)
    (fun W hz => ModularCurve.XHDRModelAtP.reduceFst_eq_frob_reduceSnd_of_isZeroSide_prolongationDatum p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcomp hcompat' W hz)
    (fun u hu => ModularCurve.XHDRModelAtP.exists_isInftySide_reduceFst_eq_and_isZeroSide_reduceSnd_eq_of_not_isAffinePlace_prolongationDatum p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcomp u hu)
    hL.1 hL.2
    (ModularCurve.XHDRModelAtP.strongPoleCancellation_prolongationDatum p M H hpM hpM2 A θ α hα Psp Rpd hres₂α)
    f h₁ h₂ hr₁ hr₂ D hD c hc

end S_ModularCurve_XHDRModelAtP_cuspLawInfty_prolongationDatum_offDiag_of_residue
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_cuspLawInfty_prolongationDatum_offDiag_of_residue (solution)
