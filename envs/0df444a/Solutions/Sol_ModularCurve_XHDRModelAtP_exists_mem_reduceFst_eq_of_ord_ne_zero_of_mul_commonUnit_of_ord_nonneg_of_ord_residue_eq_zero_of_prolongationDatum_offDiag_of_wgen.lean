-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_mem_reduceFst_eq_of_ord_ne_zero_of_mul_commonUnit_of_ord_nonneg_of_ord_residue_eq_zero_of_prolongationDatum_offDiag_of_wgen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/0e0ff934-7fdf-52c9-a6af-acb3f9518f1d

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_iff_not_isAffinePlace_reduceFst_and_hasValue_reduceFst_of_ord_pos
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_isZeroSide
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Theorems.Thm_ModularCurve_diamondActionModL_smul_mem_ssPlacesQExp_iff_and_qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_smul
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Theorems.Thm_AlgebraicCurve_Place_smul_restrictAlong
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_mk_mem_maximalIdeal_iff
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_mem_reduceFst_eq_of_ord_ne_zero_of_mul_commonUnit_of_ord_nonneg_of_ord_residue_eq_zero_of_prolongationDatum_offDiag_of_wgen
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ValuationSubring.instIsAlgClosedResidueField ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

noncomputable section

namespace PosLawSol

section FinsuppPositivity

variable {ι κ : Type*}

theorem mapDomain_apply_eq_sum [DecidableEq κ] (f : ι → κ) (D : ι →₀ ℤ) (w : κ) :
    Finsupp.mapDomain f D w = ∑ a ∈ D.support, if f a = w then D a else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.single_apply]

theorem apply_eq_zero_of_mapDomain_eq_zero_of_nonneg (f : ι → κ) (D : ι →₀ ℤ) (w : κ)
    (hnn : ∀ a, f a = w → 0 ≤ D a) (h0 : Finsupp.mapDomain f D w = 0) :
    ∀ a, f a = w → D a = 0 := by
  classical
  rw [mapDomain_apply_eq_sum] at h0
  have hterm : ∀ a ∈ D.support, 0 ≤ (if f a = w then D a else 0) := by
    intro a _
    split_ifs with h
    · exact hnn a h
    · exact le_rfl
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h0
  intro a ha
  by_cases hmem : a ∈ D.support
  · have := hall a hmem
    rwa [if_pos ha] at this
  · exact Finsupp.notMem_support_iff.mp hmem

theorem apply_eq_zero_of_mapDomain_filter_eq_zero_of_nonneg (f : ι → κ) (D : ι →₀ ℤ) (P : ι → Prop) [DecidablePred P] (w : κ)
    (hnn : ∀ a, P a → f a = w → 0 ≤ D a) (h0 : Finsupp.mapDomain f (D.filter P) w = 0) :
    ∀ a, P a → f a = w → D a = 0 := by
  have h := apply_eq_zero_of_mapDomain_eq_zero_of_nonneg f (D.filter P) w (fun a ha => by
    rw [Finsupp.filter_apply]
    split_ifs with hP
    · exact hnn a hP ha
    · exact le_rfl) h0
  intro a hP ha
  have := h a ha
  rwa [Finsupp.filter_apply, if_pos hP] at this

end FinsuppPositivity

section Values

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hasValue_add {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasValue_neg {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) : v.HasValue (-g) (-a) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨neg_mem hg, ?_⟩
  have hx : (⟨-g, neg_mem hg⟩ : v.toValuationSubring) = -⟨g, hg⟩ := rfl
  rw [hx, map_neg, hr, map_neg]

theorem hasValue_sub {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact hasValue_add h (hasValue_neg h')

theorem hasValue_pow {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact Place.hasValue_one v
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem hasValue_iff_ord (v : Place K F) (g : F) (a : K) :
    v.HasValue g a ↔ g - algebraMap K F a = 0 ∨ 0 < v.ord (g - algebraMap K F a) := by
  constructor
  · rintro ⟨hg, hr⟩
    have hmem : g - algebraMap K F a ∈ v.toValuationSubring := sub_mem hg (v.algebraMap_mem' a)
    have hres : residue v.toValuationSubring ⟨g - algebraMap K F a, hmem⟩ = 0 := by
      have hx : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring) = ⟨g, hg⟩ - algebraMap K v.toValuationSubring a := by
        apply Subtype.ext; simp [Place.coe_algebraMap]
      rw [hx, map_sub, hr, Place.residue_algebraMap, sub_self]
    have hmax : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
      rw [← IsLocalRing.residue_eq_zero_iff]; exact hres
    exact (Place.mk_mem_maximalIdeal_iff v hmem).mp hmax
  · intro h
    have hmem : g - algebraMap K F a ∈ v.toValuationSubring := by
      rcases h with h | h
      · rw [h]; exact zero_mem _
      · exact (Place.mem_iff_ord_nonneg v (fun h0 => by rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h)).mpr h.le
    have hmax : (⟨g - algebraMap K F a, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
      (Place.mk_mem_maximalIdeal_iff v hmem).mpr h
    have hg : g ∈ v.toValuationSubring := by
      have : g = (g - algebraMap K F a) + algebraMap K F a := by ring
      rw [this]; exact add_mem hmem (v.algebraMap_mem' a)
    refine ⟨hg, ?_⟩
    have hx : (⟨g, hg⟩ : v.toValuationSubring) = ⟨g - algebraMap K F a, hmem⟩ + algebraMap K v.toValuationSubring a := by
      apply Subtype.ext; simp [Place.coe_algebraMap]
    rw [hx, map_add, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, zero_add, Place.residue_algebraMap]

theorem hasValue_restrictAlong_iff {F' : Type*} [Field F'] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (x : F) (a : K) :
    (w.restrictAlong φ hφ).HasValue x a ↔ w.HasValue (φ x) a := by
  rw [hasValue_iff_ord, hasValue_iff_ord]
  have hφ' : φ (x - algebraMap K F a) = φ x - algebraMap K F' a := by rw [map_sub, AlgHom.commutes]
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have h0 : x - algebraMap K F a = 0 ↔ φ x - algebraMap K F' a = 0 := by
    rw [← hφ', map_eq_zero_iff φ hinj]
  have he := Place.one_le_ramificationIndexAlong φ hφ w
  have hord : w.ord (φ x - algebraMap K F' a) = Place.ramificationIndexAlong φ w * (w.restrictAlong φ hφ).ord (x - algebraMap K F a) := by
    rw [← hφ', Place.ord_restrictAlong]
  rw [h0, hord]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (mul_pos (by exact_mod_cast he) h)
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr (pos_of_mul_pos_right h (by exact_mod_cast (zero_le_one.trans he)))

theorem ord_sub_algebraMap_of_ord_neg (v : Place K F) {x : F} (hx : v.ord x < 0) (a : K) :
    v.ord (x - algebraMap K F a) = v.ord x := by
  have hx0 : x ≠ 0 := fun h => by rw [h, Place.ord_zero] at hx; exact lt_irrefl _ hx
  by_cases ha : a = 0
  · rw [ha, map_zero, sub_zero]
  · rw [sub_eq_add_neg, ← map_neg]
    apply Place.ord_add_eq_of_lt v hx0 (by rw [map_ne_zero_iff _ (algebraMap K F).injective]; exact neg_ne_zero.mpr ha)
    rw [Place.ord_algebraMap]; exact hx

theorem ofAlgAut_smul_place (σ : F ≃ₐ[K] F) (P : Place K F) : SemilinearAut.ofAlgAut σ • P = σ • P := by
  refine Place.ext (SetLike.ext fun x => ?_)
  rw [SemilinearAut.smul_toValuationSubring, Place.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  rfl

theorem ord_algEquiv_smul (σ : F ≃ₐ[K] F) (P : Place K F) (g : F) : (σ • P).ord g = P.ord (σ.symm g) := by
  conv_lhs => rw [← σ.apply_symm_apply g]
  exact Place.ord_smul σ P _

theorem hasValue_algEquiv_smul_iff (σ : F ≃ₐ[K] F) (P : Place K F) (g : F) (a : K) :
    (σ • P).HasValue g a ↔ P.HasValue (σ.symm g) a := by
  rw [hasValue_iff_ord, hasValue_iff_ord, ord_algEquiv_smul, map_sub, AlgEquiv.commutes]
  have : g - algebraMap K F a = 0 ↔ σ.symm g - algebraMap K F a = 0 := by
    rw [← map_eq_zero_iff σ.symm σ.symm.injective, map_sub, AlgEquiv.commutes]
  rw [this]

end Values

section Kit

theorem not_dvd_div (p M : ℕ) [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) : ¬ p ∣ M / p := fun h => hpM2 <| by
  rw [pow_two, ← Nat.div_mul_cancel hpM]
  exact Nat.mul_dvd_mul_right h p

theorem delta_frob (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (pb : (ZMod (M / p))ˣ)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w) = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ w) := by
  rw [hδ, hδ]
  exact (ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) (not_dvd_div p M hpM hpM2)
    (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) w).symm

theorem frob_injective (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] : Function.Injective (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) :=
  (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)).injective

theorem fixed_frob_iff (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (pb : (ZMod (M / p))ˣ)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (y : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p y) ↔ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ y := by
  unfold JHPlaceSpecialization.Fixed
  rw [delta_frob p M H hpM hpM2 A hA pb δ hδ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p y)]
  constructor
  · intro h
    exact frob_injective p M H hpM hpM2 A hA h
  · intro h
    rw [h]

theorem fixed_delta (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (pb : (ZMod (M / p))ˣ)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (y : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (h : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ y) : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (δ y) := by
  unfold JHPlaceSpecialization.Fixed at h ⊢
  rw [← delta_frob p M H hpM hpM2 A hA pb δ hδ y, ← delta_frob p M H hpM hpM2 A hA pb δ hδ, h]

theorem ofAlgAut_inv_smul_smul {K F : Type*} [Field K] [Field F] [Algebra K F] {G : Type*} [Group G]
    (f : G →* (F ≃ₐ[K] F)) (γ : G) (w : Place K F) :
    SemilinearAut.ofAlgAut (f γ⁻¹) • SemilinearAut.ofAlgAut (f γ) • w = w := by
  rw [map_inv, map_inv, inv_smul_smul]

theorem delta_inv_smul (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (pb : (ZMod (M / p))ˣ)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) :
    SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)⁻¹) • δ w = w := by
  have h := hδ w
  rw [h]
  exact ofAlgAut_inv_smul_smul (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)) _ w

theorem not_isAffinePlace_delta (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (pb : (ZMod (M / p))ˣ)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hw : ¬ JHPlaceSpecialization.IsAffinePlace p M H hpM A w) : ¬ JHPlaceSpecialization.IsAffinePlace p M H hpM A (δ w) := by
  intro h
  apply hw
  have h2 := (ModularCurve.JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
    p M H hpM A hA).2 (CuspForm.gammaLift (M / p) pb)⁻¹ (δ w) h
  rwa [delta_inv_smul p M H hpM hpM2 A hA pb δ hδ w] at h2

theorem isAffinePlace_delta_frob (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (pb : (ZMod (M / p))ˣ)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hw : JHPlaceSpecialization.IsAffinePlace p M H hpM A w) : JHPlaceSpecialization.IsAffinePlace p M H hpM A (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w)) := by
  have h := ModularCurve.JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL p M H hpM A hA
  rw [hδ]
  exact h.2 _ _ (h.1 w hw)

theorem isCuspidal_or_affine_fixed_of_not_strict (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (pb : (ZMod (M / p))ˣ)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (Psp : JHPlaceSpecialization p M H hpM A)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hxb : ((xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (h1 : ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V) (h2 : ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V) :
    JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V ∨ (JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα V) ∧ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V)) := by
  by_cases haff : JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα V)
  · right
    refine ⟨haff, ?_⟩
    rcases hTD V with hT | hT
    ·
      have hfix2 : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V) := by
        by_contra hnf
        exact h2 ⟨hT, hnf⟩
      rw [hT]
      exact (fixed_frob_iff p M H hpM hpM2 A hA pb δ hδ _).mpr hfix2
    ·
      by_contra hnf
      exact h1 ⟨hT, hnf⟩
  · left
    exact ((ModularCurve.JHPlaceSpecialization.isCuspidal_iff_not_isAffinePlace_reduceFst_and_hasValue_reduceFst_of_ord_pos
      p M H hpM hpM2 A hA Psp α hα hα_coe x hx xb hxb V).1).mpr haff

theorem jqModC_coeff_pow (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p] (k : ℤ) :
    ((jqModC κ).coeff k) ^ p = (jqModC κ).coeff k := by
  rw [← map_jqModC (Int.castRingHom κ), HahnSeries.map_coeff]
  show ((Int.castRingHom κ) ((jqModC ℤ).coeff k)) ^ p = _
  rw [eq_intCast, ← frobenius_def, map_intCast]

theorem ne_zero_of_coe_eq_jqModC (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hxb : ((xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A)) : xb ≠ 0 := by
  intro h0
  have h1 : ((xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)).coeff (-1) = 0 := by
    rw [h0]; rfl
  rw [hxb, ← map_jqModC (Int.castRingHom (ResidueField ↥A)), HahnSeries.map_coeff] at h1
  have hc : (jqModC ℤ).coeff (-1) = 1 := by
    rw [jqModC, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
      show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum, map_one]
  rw [hc, map_one] at h1
  exact one_ne_zero h1

theorem frob_apply_eq_pow (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hxb : ((xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A)) :
    qExpFrobeniusModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p xb = xb ^ p := by
  apply Subtype.ext
  rw [coe_qExpFrobeniusModL, SubmonoidClass.coe_pow, hxb]
  exact qExpand_eq_pow_of_coeff_fixed (ResidueField ↥A) p _ (jqModC_coeff_pow (ResidueField ↥A) p)

theorem hasValue_frob (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hxb : ((xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (b : ResidueField ↥A) (hv : v.HasValue xb b) : (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v).HasValue xb (b ^ p) := by
  show (v.restrictAlong (qExpFrobeniusModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) _).HasValue xb (b ^ p)
  rw [hasValue_restrictAlong_iff, frob_apply_eq_pow p M H hpM hpM2 A hA xb hxb]
  exact hasValue_pow hv p

theorem mem_of_mem_frob (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hxb : ((xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hv : (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∈ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v).toValuationSubring) : (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∈ v.toValuationSubring := by
  have hv' : qExpFrobeniusModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p xb ∈ v.toValuationSubring := hv
  rw [frob_apply_eq_pow p M H hpM hpM2 A hA xb hxb] at hv'
  have hxb0 : xb ≠ 0 := ne_zero_of_coe_eq_jqModC p M H hpM hpM2 A hA xb hxb
  have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [Place.mem_iff_ord_nonneg v (pow_ne_zero _ hxb0)] at hv'
  rw [Place.mem_iff_ord_nonneg v hxb0]
  have : v.ord ((xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ^ p) = (p : ℤ) * v.ord (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
    rw [← zpow_natCast, Place.ord_zpow]
  rw [this] at hv'
  by_contra hneg
  push Not at hneg
  have : (p : ℤ) * v.ord (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) < 0 := mul_neg_of_pos_of_neg hp hneg
  omega

theorem mem_ss_of_frob_mem_ss (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hxb : ((xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (b : ResidueField ↥A) (hv : v.HasValue xb b) (h : qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) : v ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p := by
  classical
  obtain ⟨x', c, hx', hc, hcss⟩ := h
  have hxx : x' = xb := Subtype.ext (by rw [hx', hxb])
  rw [hxx] at hc
  have hcb : c = b ^ p := hc.unique (hasValue_frob p M H hpM hpM2 A hA xb hxb v b hv)
  refine ⟨xb, b, hxb, hv, ?_⟩
  have := (ModularCurve.pow_mem_ssJSet_iff (K := ResidueField ↥A) p b).mp (by rw [← hcb]; convert hcss)
  convert this

theorem exists_frob_eq_of_mem_ss (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hxb : ((xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (h : v ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) : ∃ y ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p, qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p y = v := by
  classical
  obtain ⟨y, rfl⟩ := (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)).surjective v
  refine ⟨y, ?_, rfl⟩
  obtain ⟨x', b, hx', hb, hbss⟩ := h
  have hxx : x' = xb := Subtype.ext (by rw [hx', hxb])
  rw [hxx] at hb

  have hmem : (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∈ y.toValuationSubring := mem_of_mem_frob p M H hpM hpM2 A hA xb hxb y hb.mem
  obtain ⟨a, ha, -⟩ := Place.exists_hasValue_of_surjective y
    ((ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar p M H hpM hpM2
      (ResidueField ↥A)).2.2 y) hmem
  exact mem_ss_of_frob_mem_ss p M H hpM hpM2 A hA xb hxb y a ha ⟨xb, b, hxb, hb, hbss⟩

theorem delta_frob_props (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hxb : ((xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (pb : (ZMod (M / p))ˣ)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (haff : JHPlaceSpecialization.IsAffinePlace p M H hpM A v) (hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v) (hnss : v ∉ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) :
    JHPlaceSpecialization.IsAffinePlace p M H hpM A (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v)) ∧ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v)) ∧ δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v) ∉ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p := by
  refine ⟨isAffinePlace_delta_frob p M H hpM hpM2 A hA pb δ hδ v haff,
    fixed_delta p M H hpM hpM2 A hA pb δ hδ _ ((fixed_frob_iff p M H hpM hpM2 A hA pb δ hδ v).mpr hfix), fun hss => hnss ?_⟩
  have h1 : qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p := by
    rw [hδ] at hss
    exact ((ModularCurve.diamondActionModL_smul_mem_ssPlacesQExp_iff_and_qExpFrobeniusPlaceModL_qExpFrobeniusPlaceModL_eq_smul
      (ResidueField ↥A) p (M / p) (not_dvd_div p M hpM hpM2) (infSubgroup p M H hpM)).1 pb (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v)).mp hss
  obtain ⟨x', b, hx', hb⟩ := haff
  have hxx : x' = xb := Subtype.ext (by rw [hx', hxb])
  rw [hxx] at hb
  exact mem_ss_of_frob_mem_ss p M H hpM hpM2 A hA xb hxb v b hb h1

theorem reduceSnd_eq_delta_reduceFst_smul (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (Psp : JHPlaceSpecialization p M H hpM A) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V = δ (Psp.reduceFst α hα (θ.symm • V)) := by
  unfold JHPlaceSpecialization.reduceSnd JHPlaceSpecialization.reduceFst
  congr 1
  have h := Place.smul_restrictAlong α (θ.toAlgHom.comp α) hα hβ θ.symm 1 (fun x => by simp) V
  rw [one_smul] at h
  rw [h]

theorem coe_theta_of_coe_eq_jqModC (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    ((θ x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) := by
  have hjN : jq ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) := by
    show jqModC ℚ ∈ qExpFunctionFieldC ℚ _
    exact qExpFunctionFieldC_mono ℚ le_top hj
  have hmem : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) := by
    rw [hx, ← map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))]
    exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hjN
  set J' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := ⟨_, hmem⟩ with hJ'
  have hαJ : α J' = x := Subtype.ext (by rw [hα_coe])
  rw [← hαJ, show θ (α J') = (θ.toAlgHom.comp α) J' from rfl, hβ_coe, hJ', hx]

theorem isCuspidal_smul_of_isZeroSide (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hV : JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V) :
    JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) (θ.symm • V) := by
  intro x hx a
  rw [ord_algEquiv_smul, AlgEquiv.symm_symm, map_sub, AlgEquiv.commutes]
  exact hV.1 (θ x) (coe_theta_of_coe_eq_jqModC p M H hpM hj θ α hα_coe hβ_coe x hx) a

end Kit

end PosLawSol

end

open PosLawSol

set_option maxHeartbeats 6400000 in
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

    (Hh Kk : ↥(xHFunctionFieldBar M H)) (hH0 : Hh ≠ 0) (hK0 : Kk ≠ 0)
    (h₁ : Hh * Kk ∈ Rpd.R₁.integers) (hr₁ : Rpd.R₁.residue ⟨Hh * Kk, h₁⟩ ≠ 0)
    (h₂ : Hh * Kk ∈ Rpd.R₂.integers) (hr₂ : Rpd.R₂.residue ⟨Hh * Kk, h₂⟩ ≠ 0)

    (hHpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V ∨ (JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα V) ∧ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V))) → 0 ≤ V.ord Hh)
    (hKpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V ∨ (JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα V) ∧ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V))) → 0 ≤ V.ord Kk)

    (hres : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (¬ JHPlaceSpecialization.IsAffinePlace p M H hpM A w ∨ (JHPlaceSpecialization.IsAffinePlace p M H hpM A w ∧ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ w ∧ w ∉ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)) →
      w.ord (Rpd.R₁.residue ⟨Hh * Kk, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0 ∧ w.ord (Rpd.R₂.residue ⟨Hh * Kk, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = 0) :
    ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord Hh ≠ 0 → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V → ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V → ∃ s ∈ SS, Psp.reduceFst α hα V = s.1 := by
  classical
  intro V hVH hn1 hn2

  have hjM : jq ∈ xHFunctionField M H := by
    show jqModC ℚ ∈ qExpFunctionFieldC ℚ _
    exact qExpFunctionFieldC_mono ℚ le_top hj
  set x : ↥(xHFunctionFieldBar M H) := ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hjM⟩ with hxdef
  have hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := map_jqModC _
  have hyA : coeffMap A.subtype (jqModC ↥A) ∈ xHFunctionFieldBar M H := by
    rw [show coeffMap A.subtype (jqModC ↥A) = jqModC (AlgebraicClosure ℚ) from map_jqModC _, ← hx]; exact x.2
  obtain ⟨hxbmem, hxbres⟩ := Rpd.residue₁_coeffMap (jqModC ↥A) hyA
  set xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) := Rpd.R₁.residue ⟨_, hxbmem⟩ with hxbdef
  have hxb : ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := by
    rw [hxbdef, hxbres]; exact map_jqModC _

  haveI := ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar M H
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (Hh * Kk) (mul_ne_zero hH0 hK0)
  have hDsum : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), D W = W.ord Hh + W.ord Kk := fun W => by rw [hD W, Place.ord_mul _ hH0 hK0]

  have key : ∀ (hpV : JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V ∨ (JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα V) ∧ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V))), D V = 0 → False := by
    intro hpV hDV
    rw [hDsum] at hDV
    have h1 := hHpole V hpV
    have h2 := hKpole V hpV
    exact hVH (by omega)

  rcases isCuspidal_or_affine_fixed_of_not_strict p M H hpM hpM2 A hA θ α hα hβ pb δ hδ Psp hα_coe hTD x hx xb hxb V hn1 hn2 with
    hcusp | ⟨haff, hfix⟩
  ·
    exfalso
    rcases ModularCurve.JHPlaceSpecialization.isInftySide_or_isZeroSide_of_isCuspidal p M H hpM A hA V hcusp with hinf | hzero
    ·
      have hlaw := hmodel.2.2.1 (Hh * Kk) h₁ h₂ hr₁ hr₂ D hD V hinf
      have hna : ¬ JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα V) :=
        ((ModularCurve.JHPlaceSpecialization.isCuspidal_iff_not_isAffinePlace_reduceFst_and_hasValue_reduceFst_of_ord_pos
          p M H hpM hpM2 A hA Psp α hα hα_coe x hx xb hxb V).1).mp hcusp
      rw [(hres _ (Or.inl hna)).1] at hlaw
      refine key (Or.inl hcusp) (apply_eq_zero_of_mapDomain_filter_eq_zero_of_nonneg _ D _ _ ?_ hlaw V hinf rfl)
      intro C hC _
      rw [hDsum]
      exact add_nonneg (hHpole C (Or.inl hC.1)) (hKpole C (Or.inl hC.1))
    ·
      have hlaw := hmodel.2.2.2 (Hh * Kk) h₁ h₂ hr₁ hr₂ D hD V hzero
      have hcusp' : JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) (θ.symm • V) := isCuspidal_smul_of_isZeroSide p M H hpM A hj θ α hα_coe hβ_coe V hzero
      have hna' : ¬ JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα (θ.symm • V)) :=
        ((ModularCurve.JHPlaceSpecialization.isCuspidal_iff_not_isAffinePlace_reduceFst_and_hasValue_reduceFst_of_ord_pos
          p M H hpM hpM2 A hA Psp α hα hα_coe x hx xb hxb (θ.symm • V)).1).mp hcusp'
      have hna : ¬ JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V) := by
        rw [reduceSnd_eq_delta_reduceFst_smul p M H hpM A θ α hα hβ δ Psp V]
        exact not_isAffinePlace_delta p M H hpM hpM2 A hA pb δ hδ _ hna'
      rw [(hres _ (Or.inl hna)).2] at hlaw
      refine key (Or.inl hcusp) (apply_eq_zero_of_mapDomain_filter_eq_zero_of_nonneg _ D _ _ ?_ hlaw V hzero rfl)
      intro C hC _
      have hCc : JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) C := ModularCurve.JHPlaceSpecialization.isCuspidal_of_isZeroSide p M H A C hC
      rw [hDsum]
      exact add_nonneg (hHpole C (Or.inl hCc)) (hKpole C (Or.inl hCc))
  ·
    set v := Psp.reduceFst α hα V with hvdef
    by_cases hss : v ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
    ·
      obtain ⟨y, hy, hyv⟩ := exists_frob_eq_of_mem_ss p M H hpM hpM2 A hA xb hxb v hss
      refine ⟨(v, y), (hSS _).mpr ⟨hy, hyv.symm⟩, rfl⟩
    ·
      exfalso
      have hlaw := hO (Hh * Kk) h₁ h₂ hr₁ hr₂ D hD v hfix haff
      obtain ⟨haff', hfix', hnss'⟩ := delta_frob_props p M H hpM hpM2 A hA xb hxb pb δ hδ v haff hfix hss
      rw [(hres v (Or.inr ⟨haff, hfix, hss⟩)).1, (hres _ (Or.inr ⟨haff', hfix', hnss'⟩)).2, add_zero] at hlaw
      refine key (Or.inr ⟨haff, hfix⟩) (apply_eq_zero_of_mapDomain_eq_zero_of_nonneg _ D v ?_ hlaw V rfl)
      intro W hW
      rw [hDsum]
      have hW' : JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα W) ∧ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα W) := by rw [hW]; exact ⟨haff, hfix⟩
      exact add_nonneg (hHpole W (Or.inr hW')) (hKpole W (Or.inr hW'))

end S_ModularCurve_XHDRModelAtP_exists_mem_reduceFst_eq_of_ord_ne_zero_of_mul_commonUnit_of_ord_nonneg_of_ord_residue_eq_zero_of_prolongationDatum_offDiag_of_wgen
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_mem_reduceFst_eq_of_ord_ne_zero_of_mul_commonUnit_of_ord_nonneg_of_ord_residue_eq_zero_of_prolongationDatum_offDiag_of_wgen (solution)
