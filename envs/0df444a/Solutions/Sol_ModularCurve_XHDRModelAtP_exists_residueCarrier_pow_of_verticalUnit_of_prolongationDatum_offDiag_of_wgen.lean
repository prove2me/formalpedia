-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_residueCarrier_pow_of_verticalUnit_of_prolongationDatum_offDiag_of_wgen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/da7c9203-7109-5766-8386-7a4289ab3cf5

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_mem_reduceFst_eq_of_ord_ne_zero_of_mul_commonUnit_of_ord_nonneg_of_ord_residue_eq_zero_of_prolongationDatum_offDiag_of_wgen
import Theorems.Thm_AlgebraicCurve_SemilinearAut_eq_of_baseAut_eq_of_forall_smul_place_eq
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_iff_not_isAffinePlace_reduceFst_and_hasValue_reduceFst_of_ord_pos
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_isZeroSide
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_finite_setOf_fixed_of_eq_gammaLift
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Theorems.Thm_AlgebraicCurve_Place_smul_restrictAlong
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_mk_mem_maximalIdeal_iff
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_residueCarrier_pow_of_verticalUnit_of_prolongationDatum_offDiag_of_wgen
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.SmoothProperCurve

open scoped MatrixGroups

noncomputable section

namespace TwistSol

section Residues

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

def HasRes (R : RegularProlongation A F Fbar) (f : F) (r : Fbar) : Prop :=
  ∃ h : f ∈ R.integers, R.residue ⟨f, h⟩ = r

variable (R : RegularProlongation A F Fbar)

theorem HasRes.mem {R : RegularProlongation A F Fbar} {f : F} {r : Fbar} (h : HasRes R f r) : f ∈ R.integers := h.1

theorem HasRes.residue_eq {R : RegularProlongation A F Fbar} {f : F} {r : Fbar} (h : HasRes R f r) (hm : f ∈ R.integers) :
    R.residue ⟨f, hm⟩ = r := h.2

theorem hasRes_one : HasRes R (1 : F) 1 :=
  ⟨one_mem _, by rw [show (⟨(1 : F), one_mem _⟩ : R.integers) = 1 from rfl, map_one]⟩

theorem HasRes.mul {R : RegularProlongation A F Fbar} {f g : F} {r s : Fbar} (hf : HasRes R f r) (hg : HasRes R g s) :
    HasRes R (f * g) (r * s) := by
  obtain ⟨hf, rfl⟩ := hf
  obtain ⟨hg, rfl⟩ := hg
  exact ⟨mul_mem hf hg, by rw [show (⟨f * g, mul_mem hf hg⟩ : R.integers) = ⟨f, hf⟩ * ⟨g, hg⟩ from rfl, map_mul]⟩

theorem HasRes.add {R : RegularProlongation A F Fbar} {f g : F} {r s : Fbar} (hf : HasRes R f r) (hg : HasRes R g s) :
    HasRes R (f + g) (r + s) := by
  obtain ⟨hf, rfl⟩ := hf
  obtain ⟨hg, rfl⟩ := hg
  exact ⟨add_mem hf hg, by rw [show (⟨f + g, add_mem hf hg⟩ : R.integers) = ⟨f, hf⟩ + ⟨g, hg⟩ from rfl, map_add]⟩

theorem HasRes.sub {R : RegularProlongation A F Fbar} {f g : F} {r s : Fbar} (hf : HasRes R f r) (hg : HasRes R g s) :
    HasRes R (f - g) (r - s) := by
  obtain ⟨hf, rfl⟩ := hf
  obtain ⟨hg, rfl⟩ := hg
  exact ⟨sub_mem hf hg, by rw [show (⟨f - g, sub_mem hf hg⟩ : R.integers) = ⟨f, hf⟩ - ⟨g, hg⟩ from rfl, map_sub]⟩

theorem HasRes.pow {R : RegularProlongation A F Fbar} {f : F} {r : Fbar} (hf : HasRes R f r) (n : ℕ) : HasRes R (f ^ n) (r ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact hasRes_one R
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hf

theorem HasRes.inv {R : RegularProlongation A F Fbar} {f : F} {r : Fbar} (hf : HasRes R f r) (hr : r ≠ 0) : HasRes R f⁻¹ r⁻¹ := by
  obtain ⟨hmem, rfl⟩ := hf
  have hu : IsUnit (⟨f, hmem⟩ : R.integers) := R.isUnit_of_residue_ne_zero hr
  have hv1 : R.integers.valuation f = 1 := (R.integers.valuation_eq_one_iff ⟨f, hmem⟩).mp hu
  have hv1' : R.integers.valuation f⁻¹ = 1 := by rw [map_inv₀, hv1, inv_one]
  have hmem' : f⁻¹ ∈ R.integers := (R.integers.valuation_le_one_iff _).mp hv1'.le
  refine ⟨hmem', ?_⟩
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hr (by rw [show (⟨(0 : F), hmem⟩ : R.integers) = 0 from rfl, map_zero])
  have hprod : (⟨f⁻¹, hmem'⟩ : R.integers) * ⟨f, hmem⟩ = 1 := Subtype.ext (by simp [inv_mul_cancel₀ hf0])
  have := congrArg R.residue hprod
  rw [map_mul, map_one] at this
  exact eq_inv_of_mul_eq_one_left this

theorem HasRes.div {R : RegularProlongation A F Fbar} {f g : F} {r s : Fbar} (hf : HasRes R f r) (hg : HasRes R g s) (hs : s ≠ 0) :
    HasRes R (f / g) (r / s) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]; exact hf.mul (hg.inv hs)

theorem hasRes_algebraMap {x : L} (hx : x ∈ A) :
    HasRes R (algebraMap L F x) (algebraMap (ResidueField A) Fbar (IsLocalRing.residue A ⟨x, hx⟩)) :=
  ⟨(R.algebraMap_mem_iff x).mpr hx, R.residue_algebraMap ⟨x, hx⟩⟩

theorem hasRes_algebraMap_zero {x : L} (hx : A.valuation x < 1) : HasRes R (algebraMap L F x) 0 := by
  have hxA : x ∈ A := (A.valuation_le_one_iff x).mp hx.le
  have h := hasRes_algebraMap R hxA
  have h0 : IsLocalRing.residue A ⟨x, hxA⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]; exact hx
  rwa [h0, map_zero] at h

theorem HasRes.ne_zero {R : RegularProlongation A F Fbar} {f : F} {r : Fbar} (h : HasRes R f r) (hr : r ≠ 0) : f ≠ 0 := by
  rintro rfl
  obtain ⟨hm, hres⟩ := h
  exact hr (by rw [← hres, show (⟨(0 : F), hm⟩ : R.integers) = 0 from rfl, map_zero])

end Residues

section Orders

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pow_nat (v : Place K F) (f : F) (n : ℕ) : v.ord (f ^ n) = (n : ℤ) * v.ord f := by
  rw [← zpow_natCast, Place.ord_zpow]

theorem ord_prod {ι : Type*} (v : Place K F) (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      Place.ord_mul _ (hf a (Finset.mem_insert_self a s)) (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem ord_sub_algebraMap_of_ord_neg (v : Place K F) {x : F} (hx : v.ord x < 0) (a : K) :
    v.ord (x - algebraMap K F a) = v.ord x := by
  have hx0 : x ≠ 0 := fun h => by rw [h, Place.ord_zero] at hx; exact lt_irrefl _ hx
  by_cases ha : a = 0
  · rw [ha, map_zero, sub_zero]
  · rw [sub_eq_add_neg, ← map_neg]
    apply Place.ord_add_eq_of_lt v hx0 (by rw [map_ne_zero_iff _ (algebraMap K F).injective]; exact neg_ne_zero.mpr ha)
    rw [Place.ord_algebraMap]; exact hx

theorem ord_add_algebraMap_nonneg (v : Place K F) {x : F} (hx : x ∈ v.toValuationSubring) (a : K) :
    0 ≤ v.ord (algebraMap K F a + x) := by
  by_cases h0 : algebraMap K F a + x = 0
  · rw [h0, Place.ord_zero]
  · exact (Place.mem_iff_ord_nonneg v h0).mp (add_mem (v.algebraMap_mem' a) hx)

theorem mem_of_ord_eq_zero (v : Place K F) {x : F} (hx0 : x ≠ 0) (hx : v.ord x = 0) : x ∈ v.toValuationSubring :=
  (Place.mem_iff_ord_nonneg v hx0).mpr hx.ge

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

theorem ord_sub_algebraMap_eq_zero_of_hasValue_ne {v : Place K F} {g : F} {β : K} (h : v.HasValue g β) {a : K} (hne : β ≠ a) :
    v.ord (g - algebraMap K F a) = 0 :=
  (hasValue_sub h (Place.hasValue_algebraMap v a)).ord_eq_zero (sub_ne_zero.mpr hne)

theorem ord_algEquiv_smul (σ : F ≃ₐ[K] F) (P : Place K F) (g : F) : (σ • P).ord g = P.ord (σ.symm g) := by
  conv_lhs => rw [← σ.apply_symm_apply g]
  exact Place.ord_smul σ P _

theorem hasValue_algEquiv_smul_iff (σ : F ≃ₐ[K] F) (P : Place K F) (g : F) (a : K) :
    (σ • P).HasValue g a ↔ P.HasValue (σ.symm g) a := by
  rw [hasValue_iff_ord, hasValue_iff_ord, ord_algEquiv_smul, map_sub, AlgEquiv.commutes]
  have : g - algebraMap K F a = 0 ↔ σ.symm g - algebraMap K F a = 0 := by
    rw [← map_eq_zero_iff σ.symm σ.symm.injective, map_sub, AlgEquiv.commutes]
  rw [this]

end Orders

section Series

open HahnSeries

theorem coeffMap_qExpandK {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n]
    (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

theorem coeff_jqModC_neg_one (K : Type*) [CommRing K] : (jqModC K).coeff (-1) = 1 := by
  rw [← map_jqModC (Int.castRingHom K), HahnSeries.map_coeff]
  have hc : (jqModC ℤ).coeff (-1) = 1 := by
    rw [jqModC, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
      show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum, map_one]
  rw [hc, map_one]

theorem jqModC_ne_C (K : Type*) [CommRing K] [Nontrivial K] (a : K) : jqModC K ≠ HahnSeries.C a := by
  intro h
  have := congrArg (fun z : LaurentSeries K => z.coeff (-1)) h
  simp only [coeff_jqModC_neg_one, HahnSeries.C_apply, HahnSeries.coeff_single_of_ne (show (-1 : ℤ) ≠ 0 by norm_num)] at this
  exact one_ne_zero this

theorem jqModC_coeff_pow (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p] (k : ℤ) :
    ((jqModC κ).coeff k) ^ p = (jqModC κ).coeff k := by
  rw [← map_jqModC (Int.castRingHom κ), HahnSeries.map_coeff]
  show ((Int.castRingHom κ) ((jqModC ℤ).coeff k)) ^ p = _
  rw [eq_intCast, ← frobenius_def, map_intCast]

theorem jqModC_pow_eq_qExpand (κ : Type*) [Field κ] (p : ℕ) [Fact p.Prime] [CharP κ p] :
    (jqModC κ) ^ p = qExpand κ p (jqModC κ) :=
  (qExpand_eq_pow_of_coeff_fixed κ p _ (jqModC_coeff_pow κ p)).symm

end Series

section Model

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)

abbrev Pt : Type :=
  {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}

abbrev toX (z : Pt 𝔛) : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X p (ΓM M H) hj :=
  z.1 ≫ 𝔛.eeta ≫ pullback.fst _ _

theorem toX_toBase (z : Pt 𝔛) :
    toX 𝔛 z ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
  simp only [toX, Category.assoc]
  rw [pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, z.2, Category.id_comp]

def push (φ : X p (ΓM M H) hj ⟶ X p (ΓM M H) hj) (hφ : φ ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj) (z : Pt 𝔛) : Pt 𝔛 :=
  ⟨pullback.lift (toX 𝔛 z ≫ φ) (𝟙 _) (by rw [Category.assoc, hφ, toX_toBase, Category.id_comp]) ≫ inv 𝔛.eeta, by
    rw [Category.assoc, show inv 𝔛.eeta ≫ 𝔛.Meta.toBase = pullback.snd _ _ from by
      rw [IsIso.inv_comp_eq]; exact 𝔛.heeta.symm, pullback.lift_snd]⟩

theorem toX_push (φ : X p (ΓM M H) hj ⟶ X p (ΓM M H) hj) (hφ : φ ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj) (z : Pt 𝔛) :
    toX 𝔛 (push 𝔛 φ hφ z) = toX 𝔛 z ≫ φ := by
  show (pullback.lift (toX 𝔛 z ≫ φ) (𝟙 _) _ ≫ inv 𝔛.eeta) ≫ 𝔛.eeta ≫ pullback.fst _ _ = _
  rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

theorem smul_smul_smul_place_eq
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : Pt 𝔛), y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
        𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (d : (ZMod M)ˣ)
    (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    SemilinearAut.ofAlgAut θ • SemilinearAut.ofAlgAut θ • SemilinearAut.ofAlgAut (diamondAutHBar M H d) • W = W := by
  obtain ⟨y₂, rfl⟩ := 𝔛.Meta.pointEquivPlace.surjective W
  set y₁ := push 𝔛 𝔛.w.hom 𝔛.w_over y₂ with hy₁
  set y := push 𝔛 𝔛.w.hom 𝔛.w_over y₁ with hy
  have h₁ : toX 𝔛 y₁ = toX 𝔛 y₂ ≫ 𝔛.w.hom := toX_push 𝔛 _ _ _
  have h₀ : toX 𝔛 y = toX 𝔛 y₁ ≫ 𝔛.w.hom := toX_push 𝔛 _ _ _
  have e₂ : 𝔛.Meta.pointEquivPlace y₂ = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y₁ :=
    hwgen y₁ y₂ (by simpa only [toX, Category.assoc] using h₁.symm)
  have e₁ : 𝔛.Meta.pointEquivPlace y₁ = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y :=
    hwgen y y₁ (by simpa only [toX, Category.assoc] using h₀.symm)
  have hyd : toX 𝔛 y = toX 𝔛 y₂ ≫ (𝔛.dia d).hom := by
    rw [h₀, h₁, Category.assoc, 𝔛.w_sq d hd]
  have e₀ : 𝔛.Meta.pointEquivPlace y = SemilinearAut.ofAlgAut (diamondAutHBar M H d) • 𝔛.Meta.pointEquivPlace y₂ :=
    𝔛.dia_generic d y₂ y (by simpa only [toX, Category.assoc] using hyd)
  rw [← e₀, ← e₁, ← e₂]

theorem apply_apply_diamond_eq
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : Pt 𝔛), y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
        𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (d : (ZMod M)ˣ)
    (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1)
    (x : ↥(xHFunctionFieldBar M H)) : θ (θ (diamondAutHBar M H d x)) = x := by
  obtain ⟨hI, hE⟩ := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H
  haveI := hI
  haveI := hE
  have key : SemilinearAut.ofAlgAut (θ * θ * diamondAutHBar M H d) = (1 : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) := by
    refine AlgebraicCurve.SemilinearAut.eq_of_baseAut_eq_of_forall_smul_place_eq _ _ (by simp) fun W => ?_
    rw [map_mul, map_mul, mul_smul, mul_smul, one_smul]
    exact smul_smul_smul_place_eq 𝔛 θ hwgen d hd W
  have h := congrArg (fun g : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) => g • x) key
  simpa only [SemilinearAut.ofAlgAut_smul, AlgEquiv.mul_apply, one_smul] using h

theorem exists_unitsMap_mul_eq_one (hpM' : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) :
    ∃ d : (ZMod M)ˣ, ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM') d : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 := by
  have hp : p.Prime := Fact.out
  have hnd : ¬ p ∣ M / p := fun h => hpM2 <| by
    rw [pow_two, ← Nat.div_mul_cancel hpM']
    exact Nat.mul_dvd_mul_right h p
  have hcop : Nat.Coprime p (M / p) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnd
  obtain ⟨d, hd⟩ := ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd hpM') (ZMod.unitOfCoprime p hcop)⁻¹
  refine ⟨d, ?_⟩
  rw [hd, ← ZMod.coe_unitOfCoprime p hcop, ← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem theta_theta_sub (hpM2 : ¬ p ^ 2 ∣ M)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : Pt 𝔛), y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
        𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) (b : AlgebraicClosure ℚ) :
    θ (θ (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) b)) = x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) b := by
  obtain ⟨d, hd⟩ := exists_unitsMap_mul_eq_one (p := p) (M := M) hpM hpM2
  have hdx : diamondAutHBar M H d x = x :=
    ModularCurve.diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0 M H d x jq
      (qExpFunctionFieldC_mono ℚ le_top hj) (by rw [hx]; exact (map_jqModC _).symm)
  have hdxb : diamondAutHBar M H d (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) b) = x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) b := by
    rw [map_sub, hdx, AlgEquiv.commutes]
  conv_lhs => rw [← hdxb]
  exact apply_apply_diamond_eq 𝔛 θ hwgen d hd _

end Model

section Kit

theorem coe_algebraMap_eq_C (M : ℕ) (H : Subgroup (ZMod M)ˣ) (b : AlgebraicClosure ℚ) :
    ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) b : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.C b := by
  rw [SubalgebraClass.coe_algebraMap]
  show HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (algebraMap (AlgebraicClosure ℚ) (PowerSeries (AlgebraicClosure ℚ)) b) = _
  rw [PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]

theorem ne_algebraMap_of_coe_eq_jqModC (M : ℕ) (H : Subgroup (ZMod M)ˣ) (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) (b : AlgebraicClosure ℚ) :
    x ≠ algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) b := by
  intro h
  have := congrArg (fun z : ↥(xHFunctionFieldBar M H) => (z : LaurentSeries (AlgebraicClosure ℚ))) h
  simp only [hx, coe_algebraMap_eq_C] at this
  exact jqModC_ne_C _ b this

theorem ne_algebraMap_of_coe_eq_qExpand (p M : ℕ) [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (x' : ↥(xHFunctionFieldBar M H)) (hx' : ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ))) (b : AlgebraicClosure ℚ) :
    x' ≠ algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) b := by
  intro h
  have := congrArg (fun z : ↥(xHFunctionFieldBar M H) => (z : LaurentSeries (AlgebraicClosure ℚ)).coeff ((p : ℤ) * (-1))) h
  simp only [hx', coe_algebraMap_eq_C, qExpand_coeff_mul, coeff_jqModC_neg_one, HahnSeries.C_apply] at this
  rw [HahnSeries.coeff_single_of_ne] at this
  · exact one_ne_zero this
  · have : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    omega

theorem ne_zero_of_coe_eq_jqModC (M : ℕ) (H : Subgroup (ZMod M)ˣ) (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) : x ≠ 0 := by
  have h := ne_algebraMap_of_coe_eq_jqModC M H x hx 0
  rwa [map_zero] at h

theorem ne_zero_of_coe_eq_qExpand (p M : ℕ) [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (x' : ↥(xHFunctionFieldBar M H)) (hx' : ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ))) : x' ≠ 0 := by
  have h := ne_algebraMap_of_coe_eq_qExpand p M H x' hx' 0
  rwa [map_zero] at h

theorem coe_theta_of_coe_eq_jqModC (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
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

theorem ord_sub_eq_of_cuspidal (M : ℕ) (H : Subgroup (ZMod M)ˣ) (A : ValuationSubring (AlgebraicClosure ℚ)) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (y : ↥(xHFunctionFieldBar M H))
    (hcusp : ∀ a : ↥A, V.ord (y - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) ≤ 0)
    (hy : ∀ b : AlgebraicClosure ℚ, y ≠ algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) b) (b : AlgebraicClosure ℚ) (hb : b ∈ A) :
    V.ord (y - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) b) = V.ord y ∧ V.ord y ≤ 0 := by
  have h0 : V.ord y ≤ 0 := by
    have := hcusp ⟨0, zero_mem A⟩
    simpa using this
  refine ⟨?_, h0⟩
  rcases lt_or_eq_of_le h0 with hlt | heq
  · exact ord_sub_algebraMap_of_ord_neg V hlt b
  · have hy0 : y ≠ 0 := by have := hy 0; rwa [map_zero] at this
    have hmem : y ∈ V.toValuationSubring := mem_of_ord_eq_zero V hy0 heq
    have hmem' : y - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) b ∈ V.toValuationSubring := sub_mem hmem (V.algebraMap_mem' b)
    have hge : 0 ≤ V.ord (y - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) b) :=
      (Place.mem_iff_ord_nonneg V (sub_ne_zero.mpr (hy b))).mp hmem'
    have hle := hcusp ⟨b, hb⟩
    rw [heq]
    exact le_antisymm hle hge

theorem surjective_algebraMap_residueField (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    Function.Surjective (algebraMap (AlgebraicClosure ℚ) V.ResidueField) := by
  haveI := (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1
  exact (Place.deg_eq_one_iff_surjective_algebraMap_residueField V).mp (IsCurveOver.forall_deg_eq_one_of_isAlgClosed V)

theorem isCuspidal'_and_ord_of_isInftySide (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hV : JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) V) (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) (x' : ↥(xHFunctionFieldBar M H)) (hx' : ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ))) :
    JHPlaceSpecialization.IsCuspidal' (p := p) (M := M) (H := H) (A := A) V ∧ V.ord x' = (p : ℤ) * V.ord x := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨hcusp, x₀, x₀', hx₀, hx₀', τ, hτ, hval⟩ := hV
  have e₀ : x₀ = x := Subtype.ext (by rw [hx₀, hx])
  have e₀' : x₀' = x' := Subtype.ext (by rw [hx₀', hx'])
  rw [e₀, e₀'] at hval
  have hx0 : x ≠ 0 := ne_zero_of_coe_eq_jqModC M H x hx
  have hx'0 : x' ≠ 0 := ne_zero_of_coe_eq_qExpand p M H x' hx'
  have hτ0 : (τ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h; apply one_ne_zero (α := ResidueField ↥A)
    rw [← hτ, show τ = 0 from Subtype.ext h, map_zero]
  have hordq : V.ord (x' / x ^ p) = 0 := hval.ord_eq_zero hτ0
  have hord : V.ord x' = (p : ℤ) * V.ord x := by
    have : x' = x' / x ^ p * x ^ p := by rw [div_mul_cancel₀ _ (pow_ne_zero _ hx0)]
    rw [this, Place.ord_mul _ (div_ne_zero hx'0 (pow_ne_zero _ hx0)) (pow_ne_zero _ hx0), hordq, zero_add, ord_pow_nat]
  refine ⟨?_, hord⟩

  intro y hy a
  have ey : y = x' := Subtype.ext (by rw [hy, hx'])
  rw [ey]
  have hcx := hcusp x hx
  have h0 : V.ord x ≤ 0 := by simpa using hcx ⟨0, zero_mem A⟩
  rcases lt_or_eq_of_le h0 with hlt | heq
  ·
    have hlt' : V.ord x' < 0 := by
      rw [hord]; exact mul_neg_of_pos_of_neg (by exact_mod_cast (Fact.out : p.Prime).pos) hlt
    rw [ord_sub_algebraMap_of_ord_neg V hlt']
    exact hlt'.le
  ·
    obtain ⟨β, hβ, -⟩ := Place.exists_hasValue_of_surjective V (surjective_algebraMap_residueField M H V) (mem_of_ord_eq_zero V hx0 heq)
    have hβA : β ∉ A := by
      intro hβA
      have h := hcx ⟨β, hβA⟩
      rcases (hasValue_iff_ord V x β).mp hβ with h0' | h0'
      · exact ne_algebraMap_of_coe_eq_jqModC M H x hx β (sub_eq_zero.mp h0')
      · exact absurd h (not_le.mpr h0')
    have hγ : V.HasValue x' ((τ : AlgebraicClosure ℚ) * β ^ p) := by
      have := hval.mul (hasValue_pow hβ p)
      rwa [div_mul_cancel₀ _ (pow_ne_zero _ hx0)] at this
    have hγA : (τ : AlgebraicClosure ℚ) * β ^ p ≠ (a : AlgebraicClosure ℚ) := by
      intro h
      apply hβA

      have hv : A.valuation ((τ : AlgebraicClosure ℚ) * β ^ p) ≤ 1 := by rw [h]; exact (A.valuation_le_one_iff _).mpr a.2
      have hvτ : A.valuation (τ : AlgebraicClosure ℚ) = 1 := by
        rw [← A.valuation_eq_one_iff]
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hτ]; exact one_ne_zero
      rw [map_mul, hvτ, one_mul, map_pow] at hv
      have hvβ : A.valuation β ≤ 1 := by
        by_contra hgt
        push Not at hgt
        have := one_lt_pow₀ hgt (Fact.out : p.Prime).ne_zero
        exact absurd hv (not_le.mpr this)
      exact (A.valuation_le_one_iff β).mp hvβ
    rw [ord_sub_algebraMap_eq_zero_of_hasValue_ne hγ hγA]

theorem isCuspidal_of_isCuspidal' (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj) (hpM2 : ¬ p ^ 2 ∣ M)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : Pt 𝔛), y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
        𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hV : JHPlaceSpecialization.IsCuspidal' (p := p) (M := M) (H := H) (A := A) V) : JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hθx : ((θ x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) :=
    coe_theta_of_coe_eq_jqModC p M H hpM A hj θ α hα_coe hβ_coe x hx
  have hθθx : θ (θ x) = x := by
    have h := theta_theta_sub 𝔛 hpM2 θ hwgen x hx 0
    rwa [map_zero, sub_zero] at h

  have hW : JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) (θ.symm • V) := by
    intro y hy a
    have ey : y = x := Subtype.ext (by rw [hy, hx])
    rw [ord_algEquiv_smul, AlgEquiv.symm_symm, map_sub, AlgEquiv.commutes, ey]
    exact hV (θ x) hθx a
  rcases ModularCurve.JHPlaceSpecialization.isInftySide_or_isZeroSide_of_isCuspidal p M H hpM A hA _ hW with hinf | hzero
  ·
    apply ModularCurve.JHPlaceSpecialization.isCuspidal_of_isZeroSide p M H A V
    obtain ⟨-, x₀, x₀', hx₀, hx₀', τ, hτ, hval⟩ := hinf
    have e₀ : x₀ = x := Subtype.ext (by rw [hx₀, hx])
    have e₀' : x₀' = θ x := Subtype.ext (by rw [hx₀', hθx])
    rw [e₀, e₀', hasValue_algEquiv_smul_iff, AlgEquiv.symm_symm, map_div₀, map_pow, hθθx] at hval
    exact ⟨hV, x, θ x, hx, hθx, τ, hτ, hval⟩
  ·
    intro y hy a
    have ey : y = x := Subtype.ext (by rw [hy, hx])
    have h := hzero.1 (θ x) hθx a
    rw [ord_algEquiv_smul, AlgEquiv.symm_symm, map_sub, AlgEquiv.commutes, hθθx] at h
    rw [ey]; exact h

theorem ord_of_isZeroSide (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hV : JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V) (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) (x' : ↥(xHFunctionFieldBar M H)) (hx' : ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ))) :
    V.ord x = (p : ℤ) * V.ord x' := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨-, x₀, x₀', hx₀, hx₀', τ, hτ, hval⟩ := hV
  have e₀ : x₀ = x := Subtype.ext (by rw [hx₀, hx])
  have e₀' : x₀' = x' := Subtype.ext (by rw [hx₀', hx'])
  rw [e₀, e₀'] at hval
  have hx0 : x ≠ 0 := ne_zero_of_coe_eq_jqModC M H x hx
  have hx'0 : x' ≠ 0 := ne_zero_of_coe_eq_qExpand p M H x' hx'
  have hτ0 : (τ : AlgebraicClosure ℚ) ≠ 0 := by
    intro h; apply one_ne_zero (α := ResidueField ↥A)
    rw [← hτ, show τ = 0 from Subtype.ext h, map_zero]
  have hordq : V.ord (x / x' ^ p) = 0 := hval.ord_eq_zero hτ0
  have : x = x / x' ^ p * x' ^ p := by rw [div_mul_cancel₀ _ (pow_ne_zero _ hx'0)]
  rw [this, Place.ord_mul _ (div_ne_zero hx0 (pow_ne_zero _ hx'0)) (pow_ne_zero _ hx'0), hordq, zero_add, ord_pow_nat]

theorem not_dvd_div (p M : ℕ) [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) : ¬ p ∣ M / p := fun h => hpM2 <| by
  rw [pow_two, ← Nat.div_mul_cancel hpM]
  exact Nat.mul_dvd_mul_right h p

theorem delta_frob (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (pb : (ZMod (M / p))ˣ)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w) = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ w) := by
  rw [hδ, hδ]
  exact (ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) (not_dvd_div p M hpM hpM2)
    (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) w).symm

theorem fixed_frob_iff (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (pb : (ZMod (M / p))ˣ)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (y : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p y) ↔ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ y := by
  unfold JHPlaceSpecialization.Fixed
  rw [delta_frob p M H hpM hpM2 A pb δ hδ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p y)]
  constructor
  · intro h
    exact (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)).injective h
  · intro h
    rw [h]

theorem fixed_delta_iff (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (pb : (ZMod (M / p))ˣ)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (y : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (δ y) ↔ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ y := by
  unfold JHPlaceSpecialization.Fixed
  rw [← delta_frob p M H hpM hpM2 A pb δ hδ y, ← delta_frob p M H hpM hpM2 A pb δ hδ]
  constructor
  · intro h
    have hinj : Function.Injective δ := by
      intro a b hab
      rw [hδ, hδ] at hab
      exact smul_left_cancel _ hab
    exact hinj h
  · intro h
    rw [h]

theorem fixed_reduceFst_iff_fixed_reduceSnd (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (pb : (ZMod (M / p))ˣ)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (Psp : JHPlaceSpecialization p M H hpM A)
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V) ↔ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V) := by
  rcases hTD V with hT | hT
  · rw [hT, fixed_frob_iff p M H hpM hpM2 A pb δ hδ]
  · rw [← hT, fixed_delta_iff p M H hpM hpM2 A pb δ hδ, fixed_frob_iff p M H hpM hpM2 A pb δ hδ]

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

noncomputable def valAt {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F) (w : Place K F) : K := by
  classical
  exact if h : ∃ β, w.HasValue x β then h.choose else 0

theorem valAt_eq {K F : Type*} [Field K] [Field F] [Algebra K F] {x : F} {w : Place K F} {β : K} (h : w.HasValue x β) :
    valAt x w = β := by
  classical
  have hex : ∃ β, w.HasValue x β := ⟨β, h⟩
  unfold valAt
  rw [dif_pos hex]
  exact hex.choose_spec.unique h

theorem exists_residue_avoiding (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (S₀ : Finset (ResidueField ↥A)) :
    ∃ b0 : ResidueField ↥A, b0 ∉ S₀ ∧
      ∀ (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (β : ResidueField ↥A),
        JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ w → w.HasValue xb β → β ≠ b0 ∧ β ^ p ≠ b0 := by
  have hfin := ModularCurve.JHPlaceSpecialization.finite_setOf_fixed_of_eq_gammaLift p M H hpM hpM2 A hA pb hpb δ hδ
  have hBADfin : ((valAt xb '' {v | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}) ∪
      ((fun w => valAt xb w ^ p) '' {v | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}) ∪
      (S₀ : Set (ResidueField ↥A))).Finite :=
    ((hfin.image _).union (hfin.image _)).union S₀.finite_toSet
  obtain ⟨b0, hb0⟩ := hBADfin.exists_notMem
  refine ⟨b0, fun h => hb0 (Or.inr h), fun w β hw hβ => ?_⟩
  have hval : valAt xb w = β := valAt_eq hβ
  constructor
  · rintro rfl
    exact hb0 (Or.inl (Or.inl ⟨w, hw, hval⟩))
  · rintro rfl
    exact hb0 (Or.inl (Or.inr ⟨w, hw, by simp only [hval]⟩))

end Kit

section Shape

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_shape (v : Place K F) {a u u' : F} (ha : a ≠ 0) (hu : u ≠ 0) (hu' : u' ≠ 0) (N m q : ℕ) :
    v.ord (a ^ N * u ^ m / u' ^ q) = (N : ℤ) * v.ord a + (m : ℤ) * v.ord u - (q : ℤ) * v.ord u' := by
  rw [div_eq_mul_inv, Place.ord_mul _ (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hu)) (inv_ne_zero (pow_ne_zero _ hu')),
    Place.ord_mul _ (pow_ne_zero _ ha) (pow_ne_zero _ hu), Place.ord_inv, ord_pow_nat, ord_pow_nat, ord_pow_nat]
  ring

theorem ord_const_add_nonneg (v : Place K F) (c : K) {g : F} (hg0 : g ≠ 0) (hg : 0 ≤ v.ord g) :
    0 ≤ v.ord (algebraMap K F c + g) :=
  ord_add_algebraMap_nonneg v ((Place.mem_iff_ord_nonneg v hg0).mpr hg) c

theorem ord_const_add_of_neg (v : Place K F) (c : K) {g : F} (hg : v.ord g < 0) : v.ord (algebraMap K F c + g) = v.ord g := by
  have hg0 : g ≠ 0 := fun h => by rw [h, Place.ord_zero] at hg; exact lt_irrefl _ hg
  by_cases hc : c = 0
  · rw [hc, map_zero, zero_add]
  · rw [add_comm]
    exact Place.ord_add_eq_of_lt v hg0 (by rw [map_ne_zero_iff _ (algebraMap K F).injective]; exact hc) (by rw [Place.ord_algebraMap]; exact hg)

end Shape

end TwistSol

end

open TwistSol

set_option maxHeartbeats 12800000 in
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

    (G : ↥(xHFunctionFieldBar M H)) (m : ℕ) (c : (AlgebraicClosure ℚ)) (S₀ : Finset ((ResidueField ↥A))) (n : (ResidueField ↥A) → ℕ) (e : (ResidueField ↥A))
    (hG₁ : G ∈ Rpd.R₁.integers)
    (hc : c ≠ 0 ∧ A.valuation c < 1)
    (hGres : e ≠ 0 ∧ (∀ a ∈ S₀, a ∈ @ssJSet p ((ResidueField ↥A)) _ (Classical.decEq _)) ∧ (∑ a ∈ S₀, n a = m) ∧
      ∀ xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ((xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries ((ResidueField ↥A))) = jqModC ((ResidueField ↥A)) →
        Rpd.R₁.residue ⟨G, hG₁⟩ =
          algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) e * ∏ a ∈ S₀, (xb - algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) a) ^ n a)
    (hθG : θ G = algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) c * G⁻¹)
    (hGY : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), ¬ JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V → V.ord G = 0)
    (hGinf : ∀ x : ↥(xHFunctionFieldBar M H), ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries ((AlgebraicClosure ℚ))) = jqModC ((AlgebraicClosure ℚ)) →
      ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C → C.ord G = (m : ℤ) * C.ord x)
    (hGzero : ∀ x' : ↥(xHFunctionFieldBar M H), ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries ((AlgebraicClosure ℚ))) = qExpand ((AlgebraicClosure ℚ)) p (jqModC ((AlgebraicClosure ℚ))) →
      ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C → C.ord G = -((m : ℤ) * C.ord x')) :
    ∃ N : ℕ, 0 < N ∧
      ∀ ϖ : (AlgebraicClosure ℚ), A.valuation c < A.valuation ϖ → A.valuation ϖ < 1 →
        ∃ h : ↥(xHFunctionFieldBar M H), h ≠ 0 ∧
          (∃ h₁ : h ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨h, h₁⟩ ≠ 0) ∧
          (∃ h₂ : (algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (ϖ ^ N))⁻¹ * h ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨_, h₂⟩ ≠ 0) ∧
          (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
            V.ord h ≠ 0 → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V → ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V →
              ∃ s ∈ SS, Psp.reduceFst α hα V = s.1) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  obtain ⟨hc0, hcv⟩ := hc
  obtain ⟨he0, hS₀ss, hnsum, hGres⟩ := hGres

  have hjM : jq ∈ xHFunctionField M H := by
    show jqModC ℚ ∈ qExpFunctionFieldC ℚ _
    exact qExpFunctionFieldC_mono ℚ le_top hj
  have hyA : coeffMap A.subtype (jqModC ↥A) ∈ xHFunctionFieldBar M H := by
    rw [show coeffMap A.subtype (jqModC ↥A) = jqModC ((AlgebraicClosure ℚ)) from map_jqModC _, ← map_jqModC (algebraMap ℚ ((AlgebraicClosure ℚ)))]
    exact coeffEmb_mem_laurentBaseChange ((AlgebraicClosure ℚ)) hjM
  set x : ↥(xHFunctionFieldBar M H) := ⟨coeffMap A.subtype (jqModC ↥A), hyA⟩ with hxdef
  have hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC ((AlgebraicClosure ℚ)) := map_jqModC _
  obtain ⟨hxmem, hxres⟩ := Rpd.residue₁_coeffMap (jqModC ↥A) hyA
  set xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := Rpd.R₁.residue ⟨x, hxmem⟩ with hxbdef
  have hxb : ((xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries ((ResidueField ↥A))) = jqModC ((ResidueField ↥A)) := by rw [hxbdef, hxres]; exact map_jqModC _
  have Rx : HasRes Rpd.R₁ x xb := ⟨hxmem, rfl⟩
  set x' : ↥(xHFunctionFieldBar M H) := θ x with hx'def
  have hx' : ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand ((AlgebraicClosure ℚ)) p (jqModC ((AlgebraicClosure ℚ))) :=
    coe_theta_of_coe_eq_jqModC p M H hpM A hj θ α hα_coe hβ_coe x hx
  have hx0 : x ≠ 0 := ne_zero_of_coe_eq_jqModC M H x hx
  have hx'0 : x' ≠ 0 := ne_zero_of_coe_eq_qExpand p M H x' hx'

  have hyA' : coeffMap A.subtype (qExpand ↥A p (jqModC ↥A)) ∈ xHFunctionFieldBar M H := by
    rw [coeffMap_qExpandK, show coeffMap A.subtype (jqModC ↥A) = jqModC ((AlgebraicClosure ℚ)) from map_jqModC _, ← hx']; exact x'.2
  have Rx' : HasRes Rpd.R₁ x' (xb ^ p) := by
    obtain ⟨hm', hres'⟩ := Rpd.residue₁_coeffMap (qExpand ↥A p (jqModC ↥A)) hyA'
    have hex : (⟨coeffMap A.subtype (qExpand ↥A p (jqModC ↥A)), hyA'⟩ : ↥(xHFunctionFieldBar M H)) = x' :=
      Subtype.ext (by
        show coeffMap A.subtype (qExpand ↥A p (jqModC ↥A)) = ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))
        rw [hx', coeffMap_qExpandK, show coeffMap A.subtype (jqModC ↥A) = jqModC ((AlgebraicClosure ℚ)) from map_jqModC _])
    have hval : Rpd.R₁.residue ⟨_, hm'⟩ = xb ^ p := by
      apply Subtype.ext
      rw [hres', SubmonoidClass.coe_pow, hxb, coeffMap_qExpandK, show coeffMap (IsLocalRing.residue ↥A) (jqModC ↥A) = jqModC ((ResidueField ↥A)) from map_jqModC _,
        jqModC_pow_eq_qExpand]
    rw [← hex]
    exact ⟨hm', hval⟩

  have hCκ : ∀ a : (ResidueField ↥A), ((algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) a : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries ((ResidueField ↥A))) = HahnSeries.C a := by
    intro a
    rw [SubalgebraClass.coe_algebraMap]
    show HahnSeries.ofPowerSeries ℤ ((ResidueField ↥A)) (algebraMap ((ResidueField ↥A)) (PowerSeries ((ResidueField ↥A))) a) = _
    rw [PowerSeries.algebraMap_eq, HahnSeries.ofPowerSeries_C]
  have hxbsub : ∀ a : (ResidueField ↥A), xb - algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) a ≠ 0 := by
    intro a h
    have := congrArg (fun z : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) => (z : LaurentSeries ((ResidueField ↥A))).coeff (-1)) (sub_eq_zero.mp h)
    simp only [hxb, TwistSol.coeff_jqModC_neg_one, hCκ, HahnSeries.C_apply] at this
    rw [HahnSeries.coeff_single_of_ne (by norm_num)] at this
    exact one_ne_zero this
  have hxbpsub : ∀ a : (ResidueField ↥A), xb ^ p - algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) a ≠ 0 := by
    intro a h
    have := congrArg (fun z : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) => (z : LaurentSeries ((ResidueField ↥A))).coeff ((p : ℤ) * (-1))) (sub_eq_zero.mp h)
    simp only [SubmonoidClass.coe_pow, hxb, jqModC_pow_eq_qExpand, qExpand_coeff_mul, TwistSol.coeff_jqModC_neg_one, hCκ, HahnSeries.C_apply] at this
    rw [HahnSeries.coeff_single_of_ne (by omega)] at this
    exact one_ne_zero this

  obtain ⟨b0, hb0S, hb0⟩ := exists_residue_avoiding p M H hpM hpM2 A hA pb hpb δ hδ xb S₀
  obtain ⟨bA, hbA⟩ := IsLocalRing.residue_surjective (R := ↥A) b0
  set b : (AlgebraicClosure ℚ) := (bA : (AlgebraicClosure ℚ)) with hbdef
  have hbmem : b ∈ A := bA.2
  have Rb : HasRes Rpd.R₁ (algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) b) (algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) b0) := by
    have h := hasRes_algebraMap Rpd.R₁ hbmem
    rwa [show (⟨b, hbmem⟩ : ↥A) = bA from Subtype.ext rfl, hbA] at h

  refine ⟨p ^ 2 - 1, Nat.sub_pos_of_lt (Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt), fun ϖ hcϖ hϖ1 => ?_⟩
  set N : ℕ := p ^ 2 - 1 with hNdef
  have hN : (N : ℤ) = (p : ℤ) * p - 1 := by
    rw [hNdef, Nat.cast_sub (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)]; push_cast; ring

  have hϖ0 : ϖ ≠ 0 := by rintro rfl; rw [map_zero] at hcϖ; exact not_lt_zero hcϖ
  have hϖA : ϖ ∈ A := (A.valuation_le_one_iff ϖ).mp hϖ1.le
  have hcϖv : A.valuation (c / ϖ) < 1 := by
    rw [map_div₀, div_lt_one₀ ((Valuation.pos_iff _).mpr hϖ0)]; exact hcϖ
  have hcne : algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) c ≠ 0 := by rw [map_ne_zero_iff _ (algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H)).injective]; exact hc0

  set U : ↥(xHFunctionFieldBar M H) := x - algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) b with hUdef
  set U' : ↥(xHFunctionFieldBar M H) := x' - algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) b with hU'def
  set h₀ : ↥(xHFunctionFieldBar M H) := algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) ϖ + G with hh₀def
  set k₀ : ↥(xHFunctionFieldBar M H) := algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) ϖ + algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) c * G⁻¹ with hk₀def
  set Hh : ↥(xHFunctionFieldBar M H) := h₀ ^ N * U ^ m / U' ^ (p * m) with hHhdef
  set Kr : ↥(xHFunctionFieldBar M H) := k₀ ^ N * U' ^ m / U ^ (p * m) with hKrdef
  set Kk : ↥(xHFunctionFieldBar M H) := algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (ϖ ^ N)⁻¹ * Kr with hKkdef
  have hU0 : U ≠ 0 := sub_ne_zero.mpr (ne_algebraMap_of_coe_eq_jqModC M H x hx b)
  have hU'0 : U' ≠ 0 := sub_ne_zero.mpr (ne_algebraMap_of_coe_eq_qExpand p M H x' hx' b)

  have RG : HasRes Rpd.R₁ G (algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) e * ∏ a ∈ S₀, (xb - algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) a) ^ n a) := ⟨hG₁, hGres xb hxb⟩
  set gb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) e * ∏ a ∈ S₀, (xb - algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) a) ^ n a with hgbdef
  have hgb0 : gb ≠ 0 := mul_ne_zero (by rw [map_ne_zero_iff _ (algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))).injective]; exact he0)
    (Finset.prod_ne_zero_iff.mpr fun a _ => pow_ne_zero _ (hxbsub a))
  have hG0 : G ≠ 0 := RG.ne_zero hgb0
  have RU : HasRes Rpd.R₁ U (xb - algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) b0) := Rx.sub Rb
  have RU' : HasRes Rpd.R₁ U' (xb ^ p - algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) b0) := Rx'.sub Rb
  have Rh₀ : HasRes Rpd.R₁ h₀ gb := by
    have := (hasRes_algebraMap_zero Rpd.R₁ hϖ1).add RG
    rwa [zero_add] at this
  have hh₀0 : h₀ ≠ 0 := Rh₀.ne_zero hgb0

  have hk₀' : (algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) ϖ)⁻¹ * k₀ = 1 + algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (c / ϖ) * G⁻¹ := by
    have hϖne : algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) ϖ ≠ 0 := by rw [map_ne_zero_iff _ (algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H)).injective]; exact hϖ0
    rw [hk₀def, map_div₀, mul_add, inv_mul_cancel₀ hϖne, div_eq_mul_inv]; ring
  have Rk₀' : HasRes Rpd.R₁ ((algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) ϖ)⁻¹ * k₀) 1 := by
    rw [hk₀']
    have := (hasRes_one Rpd.R₁).add ((hasRes_algebraMap_zero Rpd.R₁ hcϖv).mul (RG.inv hgb0))
    rwa [zero_mul, add_zero] at this
  have hk₀0 : k₀ ≠ 0 := by
    intro h
    have := Rk₀'.ne_zero one_ne_zero
    rw [h, mul_zero] at this
    exact this rfl
  set r1 : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := xb - algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) b0 with hr1def
  set r2 : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := xb ^ p - algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) b0 with hr2def
  have hr10 : r1 ≠ 0 := hxbsub b0
  have hr20 : r2 ≠ 0 := hxbpsub b0
  have RHh : HasRes Rpd.R₁ Hh (gb ^ N * r1 ^ m / r2 ^ (p * m)) := ((Rh₀.pow N).mul (RU.pow m)).div (RU'.pow _) (pow_ne_zero _ hr20)
  have hKk_eq : Kk = ((algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) ϖ)⁻¹ * k₀) ^ N * U' ^ m / U ^ (p * m) := by
    rw [hKkdef, hKrdef, map_inv₀, map_pow, mul_pow, inv_pow, mul_div_assoc, mul_div_assoc, mul_assoc]
  have RKk : HasRes Rpd.R₁ Kk ((1 : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ^ N * r2 ^ m / r1 ^ (p * m)) := by
    rw [hKk_eq]; exact ((Rk₀'.pow N).mul (RU'.pow m)).div (RU.pow _) (pow_ne_zero _ hr10)
  set Ψ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := (gb ^ N * r1 ^ m / r2 ^ (p * m)) * ((1 : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ^ N * r2 ^ m / r1 ^ (p * m)) with hΨdef
  have hΨ0 : Ψ ≠ 0 := mul_ne_zero (div_ne_zero (mul_ne_zero (pow_ne_zero _ hgb0) (pow_ne_zero _ hr10)) (pow_ne_zero _ hr20))
    (div_ne_zero (mul_ne_zero (pow_ne_zero _ one_ne_zero) (pow_ne_zero _ hr20)) (pow_ne_zero _ hr10))
  have RF : HasRes Rpd.R₁ (Hh * Kk) Ψ := RHh.mul RKk

  have hθU : θ U = U' := by rw [hUdef, map_sub, AlgEquiv.commutes]
  have hθU' : θ U' = U := by
    rw [hU'def, hx'def, ← AlgEquiv.commutes θ b, ← map_sub]; exact theta_theta_sub 𝔛 hpM2 θ hwgen x hx b
  have hθh₀ : θ h₀ = k₀ := by rw [hh₀def, map_add, AlgEquiv.commutes, hθG]
  have hθk₀ : θ k₀ = h₀ := by
    rw [hk₀def, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, map_inv₀, hθG, mul_inv, inv_inv, ← mul_assoc,
      mul_inv_cancel₀ hcne, one_mul]
  have hθHh : θ Hh = Kr := by rw [hHhdef, map_div₀, map_mul, map_pow, map_pow, map_pow, hθh₀, hθU, hθU']
  have hθKr : θ Kr = Hh := by rw [hKrdef, map_div₀, map_mul, map_pow, map_pow, map_pow, hθk₀, hθU, hθU']
  have hθF : θ (Hh * Kk) = Hh * Kk := by
    rw [map_mul, hKkdef, map_mul, AlgEquiv.commutes, hθHh, hθKr]; ring

  have hF₁ : Hh * Kk ∈ Rpd.R₁.integers := RF.mem
  have hFr₁ : Rpd.R₁.residue ⟨Hh * Kk, hF₁⟩ = Ψ := RF.residue_eq hF₁
  have hF₂ : Hh * Kk ∈ Rpd.R₂.integers := (Rpd.mem_integers₂_iff _).mpr (by rw [hθF]; exact hF₁)
  have hFr₂ : Rpd.R₂.residue ⟨Hh * Kk, hF₂⟩ = Ψ := by
    rw [Rpd.residue₂_eq]
    have : (⟨θ (Hh * Kk), (Rpd.mem_integers₂_iff _).mp hF₂⟩ : Rpd.R₁.integers) = ⟨Hh * Kk, hF₁⟩ := Subtype.ext hθF
    rw [this, hFr₁]
  have hHh0 : Hh ≠ 0 := div_ne_zero (mul_ne_zero (pow_ne_zero _ hh₀0) (pow_ne_zero _ hU0)) (pow_ne_zero _ hU'0)
  have hKr0 : Kr ≠ 0 := div_ne_zero (mul_ne_zero (pow_ne_zero _ hk₀0) (pow_ne_zero _ hU'0)) (pow_ne_zero _ hU0)
  have hϖNne : algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (ϖ ^ N)⁻¹ ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H)).injective]; exact inv_ne_zero (pow_ne_zero _ hϖ0)
  have hKk0 : Kk ≠ 0 := mul_ne_zero hϖNne hKr0

  have hordHh : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord Hh = (N : ℤ) * V.ord h₀ + (m : ℤ) * V.ord U - ((p * m : ℕ) : ℤ) * V.ord U' :=
    fun V => ord_shape V hh₀0 hU0 hU'0 N m (p * m)
  have hordKk : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord Kk = (N : ℤ) * V.ord k₀ + (m : ℤ) * V.ord U' - ((p * m : ℕ) : ℤ) * V.ord U := by
    intro V
    rw [hKkdef, Place.ord_mul _ hϖNne hKr0, Place.ord_algebraMap, zero_add]
    exact ord_shape V hk₀0 hU'0 hU0 N m (p * m)
  have hordcG : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord (algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) c * G⁻¹) = - V.ord G := by
    intro V
    rw [Place.ord_mul _ hcne (inv_ne_zero hG0), Place.ord_algebraMap, zero_add, Place.ord_inv]
  have hcG0 : algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) c * G⁻¹ ≠ 0 := mul_ne_zero hcne (inv_ne_zero hG0)

  have KA := ModularCurve.JHPlaceSpecialization.isCuspidal_iff_not_isAffinePlace_reduceFst_and_hasValue_reduceFst_of_ord_pos
    p M H hpM hpM2 A hA Psp α hα hα_coe x hx xb hxb
  have hcusp'_to_cusp : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsCuspidal' (p := p) (M := M) (H := H) (A := A) V → JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V :=
    fun V hV => isCuspidal_of_isCuspidal' p M H hpM A hA hj 𝔛 hpM2 θ α hwgen hα_coe hβ_coe x hx V hV
  have hpm : ((p * m : ℕ) : ℤ) = (p : ℤ) * m := by push_cast; ring

  have hpole : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V ∨ (JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα V) ∧ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V))) →
      0 ≤ V.ord Hh ∧ 0 ≤ V.ord Kk := by
    intro V hV
    rw [hordHh V, hordKk V, hpm]
    rcases hV with hcusp | ⟨haff, hfix⟩
    · rcases ModularCurve.JHPlaceSpecialization.isInftySide_or_isZeroSide_of_isCuspidal p M H hpM A hA V hcusp with hinf | hzero
      ·
        obtain ⟨hcusp', hxx'⟩ := isCuspidal'_and_ord_of_isInftySide p M H hpM A V hinf x hx x' hx'
        obtain ⟨hU, hxle⟩ := ord_sub_eq_of_cuspidal M H A V x (hcusp x hx) (fun b' => ne_algebraMap_of_coe_eq_jqModC M H x hx b') b hbmem
        obtain ⟨hU', -⟩ := ord_sub_eq_of_cuspidal M H A V x' (hcusp' x' hx') (fun b' => ne_algebraMap_of_coe_eq_qExpand p M H x' hx' b') b hbmem
        have hGord : V.ord G = (m : ℤ) * V.ord x := hGinf x hx V hinf
        have eU : V.ord U = V.ord x := hU
        have eU' : V.ord U' = (p : ℤ) * V.ord x := by rw [show V.ord U' = V.ord x' from hU', hxx']
        rw [eU, eU']
        have ht : (m : ℤ) * V.ord x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) hxle
        constructor
        · rcases lt_or_eq_of_le ht with hlt | heq
          · have hh₀ : V.ord h₀ = (m : ℤ) * V.ord x := by rw [hh₀def, ord_const_add_of_neg V ϖ (by rw [hGord]; exact hlt), hGord]
            rw [hh₀, hN]
            have : ((p : ℤ) * p - 1) * ((m : ℤ) * V.ord x) + (m : ℤ) * V.ord x - (p : ℤ) * m * ((p : ℤ) * V.ord x) = 0 := by ring
            exact this.ge
          · have hh₀ : 0 ≤ V.ord h₀ := ord_const_add_nonneg V ϖ hG0 (by rw [hGord, heq])
            have e1 : (N : ℤ) * V.ord h₀ + (m : ℤ) * V.ord x - (p : ℤ) * m * ((p : ℤ) * V.ord x) =
                (N : ℤ) * V.ord h₀ + (1 - (p : ℤ) * p) * ((m : ℤ) * V.ord x) := by ring
            rw [e1, heq, mul_zero, add_zero]
            exact mul_nonneg (Nat.cast_nonneg N) hh₀
        · have hGinv : 0 ≤ V.ord (algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) c * G⁻¹) := by rw [hordcG, hGord]; exact neg_nonneg.mpr ht
          have hk₀ : 0 ≤ V.ord k₀ := ord_const_add_nonneg V ϖ hcG0 hGinv
          have e1 : (N : ℤ) * V.ord k₀ + (m : ℤ) * ((p : ℤ) * V.ord x) - (p : ℤ) * m * V.ord x = (N : ℤ) * V.ord k₀ := by ring
          rw [e1]
          exact mul_nonneg (Nat.cast_nonneg N) hk₀
      ·
        have hcusp' : JHPlaceSpecialization.IsCuspidal' (p := p) (M := M) (H := H) (A := A) V := hzero.1
        have hxx' : V.ord x = (p : ℤ) * V.ord x' := ord_of_isZeroSide p M H hpM A V hzero x hx x' hx'
        obtain ⟨hU, -⟩ := ord_sub_eq_of_cuspidal M H A V x (hcusp x hx) (fun b' => ne_algebraMap_of_coe_eq_jqModC M H x hx b') b hbmem
        obtain ⟨hU', hx'le⟩ := ord_sub_eq_of_cuspidal M H A V x' (hcusp' x' hx') (fun b' => ne_algebraMap_of_coe_eq_qExpand p M H x' hx' b') b hbmem
        have hGord : V.ord G = -((m : ℤ) * V.ord x') := hGzero x' hx' V hzero
        have eU : V.ord U = (p : ℤ) * V.ord x' := by rw [show V.ord U = V.ord x from hU, hxx']
        have eU' : V.ord U' = V.ord x' := hU'
        rw [eU, eU']
        have ht : (m : ℤ) * V.ord x' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) hx'le
        constructor
        · have hh₀ : 0 ≤ V.ord h₀ := ord_const_add_nonneg V ϖ hG0 (by rw [hGord]; exact neg_nonneg.mpr ht)
          have e1 : (N : ℤ) * V.ord h₀ + (m : ℤ) * ((p : ℤ) * V.ord x') - (p : ℤ) * m * V.ord x' = (N : ℤ) * V.ord h₀ := by ring
          rw [e1]
          exact mul_nonneg (Nat.cast_nonneg N) hh₀
        · have hordinv : V.ord (algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) c * G⁻¹) = (m : ℤ) * V.ord x' := by rw [hordcG, hGord]; ring
          rcases lt_or_eq_of_le ht with hlt | heq
          · have hk₀ : V.ord k₀ = (m : ℤ) * V.ord x' := by rw [hk₀def, ord_const_add_of_neg V ϖ (by rw [hordinv]; exact hlt), hordinv]
            rw [hk₀, hN]
            have : ((p : ℤ) * p - 1) * ((m : ℤ) * V.ord x') + (m : ℤ) * V.ord x' - (p : ℤ) * m * ((p : ℤ) * V.ord x') = 0 := by ring
            exact this.ge
          · have hk₀ : 0 ≤ V.ord k₀ := ord_const_add_nonneg V ϖ hcG0 (by rw [hordinv, heq])
            have e1 : (N : ℤ) * V.ord k₀ + (m : ℤ) * V.ord x' - (p : ℤ) * m * ((p : ℤ) * V.ord x') =
                (N : ℤ) * V.ord k₀ + (1 - (p : ℤ) * p) * ((m : ℤ) * V.ord x') := by ring
            rw [e1, heq, mul_zero, add_zero]
            exact mul_nonneg (Nat.cast_nonneg N) hk₀
    ·
      have hncusp : ¬ JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V := fun h => (KA V).1.mp h haff
      have hGord : V.ord G = 0 := hGY V hncusp
      have hh₀ : 0 ≤ V.ord h₀ := ord_const_add_nonneg V ϖ hG0 hGord.ge
      have hk₀ : 0 ≤ V.ord k₀ := ord_const_add_nonneg V ϖ hcG0 (by rw [hordcG, hGord, neg_zero])

      have hxreg : 0 ≤ V.ord U := by
        have hnc : ∃ a : ↥A, ¬ V.ord (x - algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ))) ≤ 0 := by
          by_contra hall
          push Not at hall
          exact hncusp (fun y hy a => by
            have ey : y = x := Subtype.ext (by rw [hy, hx])
            rw [ey]; exact hall a)
        obtain ⟨a, ha⟩ := hnc
        push Not at ha
        have hxa : x - algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ)) ∈ V.toValuationSubring :=
          (Place.mem_iff_ord_nonneg V (sub_ne_zero.mpr (ne_algebraMap_of_coe_eq_jqModC M H x hx _))).mpr ha.le
        have hxmemV : x ∈ V.toValuationSubring := by
          have : x = (x - algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ))) + algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ)) := by ring
          rw [this]; exact add_mem hxa (V.algebraMap_mem' _)
        exact (Place.mem_iff_ord_nonneg V hU0).mp (sub_mem hxmemV (V.algebraMap_mem' b))
      have hx'reg : 0 ≤ V.ord U' := by
        have hncusp' : ¬ JHPlaceSpecialization.IsCuspidal' (p := p) (M := M) (H := H) (A := A) V := fun h => hncusp (hcusp'_to_cusp V h)
        have hnc : ∃ a : ↥A, ¬ V.ord (x' - algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ))) ≤ 0 := by
          by_contra hall
          push Not at hall
          exact hncusp' (fun y hy a => by
            have ey : y = x' := Subtype.ext (by rw [hy, hx'])
            rw [ey]; exact hall a)
        obtain ⟨a, ha⟩ := hnc
        push Not at ha
        have hxa : x' - algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ)) ∈ V.toValuationSubring :=
          (Place.mem_iff_ord_nonneg V (sub_ne_zero.mpr (ne_algebraMap_of_coe_eq_qExpand p M H x' hx' _))).mpr ha.le
        have hxmemV : x' ∈ V.toValuationSubring := by
          have : x' = (x' - algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ))) + algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ)) := by ring
          rw [this]; exact add_mem hxa (V.algebraMap_mem' _)
        exact (Place.mem_iff_ord_nonneg V hU'0).mp (sub_mem hxmemV (V.algebraMap_mem' b))

      have hUz : V.ord U = 0 := by
        refine le_antisymm ?_ hxreg
        by_contra hpos
        push Not at hpos
        have hval := (KA V).2.1 bA hpos
        rw [hbA] at hval
        exact (hb0 _ b0 hfix hval).1 rfl

      have hU'z : V.ord U' = 0 := by
        refine le_antisymm ?_ hx'reg
        by_contra hpos
        push Not at hpos
        have hpos' : 0 < (θ.symm • V).ord (x - algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (bA : (AlgebraicClosure ℚ))) := by
          rw [ord_algEquiv_smul, AlgEquiv.symm_symm]
          have : θ (x - algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (bA : (AlgebraicClosure ℚ))) = U' := hθU
          rw [this]; exact hpos
        have hval := (KA (θ.symm • V)).2.1 bA hpos'
        rw [hbA] at hval
        have hfix2 : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ V) :=
          (fixed_reduceFst_iff_fixed_reduceSnd p M H hpM hpM2 A θ α hα hβ pb δ hδ Psp hTD V).mp hfix
        rw [reduceSnd_eq_delta_reduceFst_smul p M H hpM A θ α hα hβ δ Psp V, fixed_delta_iff p M H hpM hpM2 A pb δ hδ] at hfix2
        exact (hb0 _ b0 hfix2 hval).1 rfl
      rw [hUz, hU'z]
      simp only [mul_zero, sub_zero, add_zero]
      exact ⟨mul_nonneg (Nat.cast_nonneg N) hh₀, mul_nonneg (Nat.cast_nonneg N) hk₀⟩

  have hsurjκ := (ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar p M H hpM hpM2
    ((ResidueField ↥A))).2.2
  have hxb0 : xb ≠ 0 := by have := hxbsub 0; rwa [map_zero, sub_zero] at this
  have hordΨ : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), w.ord Ψ = (N : ℤ) * w.ord gb + (m : ℤ) * w.ord r1 - ((p * m : ℕ) : ℤ) * w.ord r2 +
      ((m : ℤ) * w.ord r2 - ((p * m : ℕ) : ℤ) * w.ord r1) := by
    intro w
    rw [hΨdef, Place.ord_mul _ (div_ne_zero (mul_ne_zero (pow_ne_zero _ hgb0) (pow_ne_zero _ hr10)) (pow_ne_zero _ hr20))
      (div_ne_zero (mul_ne_zero (pow_ne_zero _ one_ne_zero) (pow_ne_zero _ hr20)) (pow_ne_zero _ hr10)),
      ord_shape w hgb0 hr10 hr20, ord_shape w one_ne_zero hr20 hr10, Place.ord_one, mul_zero, zero_add]
  have hordgb : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), w.ord gb = ∑ a ∈ S₀, (n a : ℤ) * w.ord (xb - algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) a) := by
    intro w
    rw [hgbdef, Place.ord_mul _ (by rw [map_ne_zero_iff _ (algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))).injective]; exact he0)
      (Finset.prod_ne_zero_iff.mpr fun a _ => pow_ne_zero _ (hxbsub a)), Place.ord_algebraMap, zero_add,
      ord_prod w S₀ _ (fun a _ => pow_ne_zero _ (hxbsub a))]
    exact Finset.sum_congr rfl fun a _ => ord_pow_nat w _ _
  have hres : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (¬ JHPlaceSpecialization.IsAffinePlace p M H hpM A w ∨ (JHPlaceSpecialization.IsAffinePlace p M H hpM A w ∧ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ w ∧ w ∉ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)) →
      w.ord (Rpd.R₁.residue ⟨Hh * Kk, hF₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) = 0 ∧ w.ord (Rpd.R₂.residue ⟨Hh * Kk, hF₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) = 0 := by
    intro w hw
    rw [hFr₁, hFr₂, and_self, hordΨ w, hordgb w, hpm]
    rcases hw with hna | ⟨haff, hfix, hnss⟩
    ·
      have hxbmem : (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∉ w.toValuationSubring := by
        intro hmem
        obtain ⟨β, hβ, -⟩ := Place.exists_hasValue_of_surjective w (hsurjκ w) hmem
        exact hna ⟨xb, β, hxb, hβ⟩
      have hE : w.ord xb < 0 := by
        by_contra hge
        push Not at hge
        exact hxbmem ((Place.mem_iff_ord_nonneg w hxb0).mpr hge)
      have h1 : ∀ a : (ResidueField ↥A), w.ord (xb - algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) a) = w.ord xb := fun a => ord_sub_algebraMap_of_ord_neg w hE a
      have h2 : w.ord r2 = (p : ℤ) * w.ord xb := by
        rw [hr2def, ord_sub_algebraMap_of_ord_neg w (by rw [ord_pow_nat]; exact mul_neg_of_pos_of_neg (by exact_mod_cast (Fact.out : p.Prime).pos) hE) b0, ord_pow_nat]
      rw [hr1def, h1 b0, h2]
      simp_rw [h1]
      rw [← Finset.sum_mul, show (∑ a ∈ S₀, (n a : ℤ)) = (m : ℤ) from by rw [← hnsum]; push_cast; rfl, hN]
      ring
    ·
      obtain ⟨x₁, β, hx₁, hβ⟩ := haff
      have ex : x₁ = xb := Subtype.ext (by rw [hx₁, hxb])
      rw [ex] at hβ
      obtain ⟨hβb, hβpb⟩ := hb0 w β hfix hβ
      have hβS : β ∉ S₀ := by
        intro hmem
        exact hnss ⟨xb, β, hxb, hβ, by convert hS₀ss β hmem⟩
      have h1 : w.ord r1 = 0 := ord_sub_algebraMap_eq_zero_of_hasValue_ne hβ hβb
      have h2 : w.ord r2 = 0 := ord_sub_algebraMap_eq_zero_of_hasValue_ne (hasValue_pow hβ p) hβpb
      have h3 : ∀ a ∈ S₀, (n a : ℤ) * w.ord (xb - algebraMap ((ResidueField ↥A)) ((JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) a) = 0 := fun a ha => by
        rw [ord_sub_algebraMap_eq_zero_of_hasValue_ne hβ (fun h => hβS (h ▸ ha)), mul_zero]
      rw [h1, h2, Finset.sum_eq_zero h3]
      ring

  have hsupp := ModularCurve.XHDRModelAtP.exists_mem_reduceFst_eq_of_ord_ne_zero_of_mul_commonUnit_of_ord_nonneg_of_ord_residue_eq_zero_of_prolongationDatum_offDiag_of_wgen
    p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat' hO hRL hNV hθgal hβ_coe
    Hh Kk hHh0 hKk0 hF₁ (by rw [hFr₁]; exact hΨ0) hF₂ (by rw [hFr₂]; exact hΨ0) (fun V hV => (hpole V hV).1) (fun V hV => (hpole V hV).2) hres

  refine ⟨Hh, hHh0, ⟨RHh.mem, ?_⟩, ?_, hsupp⟩
  · rw [RHh.residue_eq]; exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hgb0) (pow_ne_zero _ hr10)) (pow_ne_zero _ hr20)
  ·
    have hθ' : θ ((algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (ϖ ^ N))⁻¹ * Hh) = Kk := by rw [map_mul, map_inv₀, AlgEquiv.commutes, hθHh, ← map_inv₀]
    have hmem₂ : (algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (ϖ ^ N))⁻¹ * Hh ∈ Rpd.R₂.integers := (Rpd.mem_integers₂_iff _).mpr (by rw [hθ']; exact RKk.mem)
    refine ⟨hmem₂, ?_⟩
    rw [Rpd.residue₂_eq]
    have : (⟨θ ((algebraMap ((AlgebraicClosure ℚ)) ↥(xHFunctionFieldBar M H) (ϖ ^ N))⁻¹ * Hh), (Rpd.mem_integers₂_iff _).mp hmem₂⟩ : Rpd.R₁.integers) = ⟨Kk, RKk.mem⟩ :=
      Subtype.ext hθ'
    rw [this, RKk.residue_eq]
    exact div_ne_zero (mul_ne_zero (pow_ne_zero _ one_ne_zero) (pow_ne_zero _ hr20)) (pow_ne_zero _ hr10)

end S_ModularCurve_XHDRModelAtP_exists_residueCarrier_pow_of_verticalUnit_of_prolongationDatum_offDiag_of_wgen
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_residueCarrier_pow_of_verticalUnit_of_prolongationDatum_offDiag_of_wgen (solution)
