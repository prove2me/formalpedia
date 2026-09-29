-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.oneSidedFst_laws_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/10479614-0147-5d34-a9cd-22e21184755d

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_ModularCurve_QAdicPlaceMod
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_sum_ramificationIndexAlong_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_sub_nonpos
import Theorems.Thm_ModularCurve_XHDRModelAtP_not_isAffinePlace_reduceFst_of_isInftySide_prolongationDatum
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_mapDomain_sp_zeros_sub_algebraMap_eq_and_mapDomain_sp_poles_eq_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ord_sp_neg_of_forall_ord_sub_algebraMap_le
import Theorems.Thm_ModularCurve_XHDRModelAtP_cuspOrientationInf_and_cuspOrientationZero_of_jHPlaceSpecialization_of_offDiag
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_ord_ne_zero_of_coe_eq_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_fixed_of_mem_ssPlacesQExp
import Theorems.Thm_ModularCurve_ord_eq_zero_of_not_mem_ssPlacesQExp_of_hasValue_of_coe_eq_coeffMap_modularUnitSeries
import Theorems.Thm_ModularCurve_XHDRModelAtP_not_isAffinePlace_frob_reduceSnd_of_isZeroSide_prolongationDatum
import Theorems.Thm_ModularCurve_exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_finite_setOf_fixed_of_eq_gammaLift
import Theorems.Thm_ModularCurve_XHDRModelAtP_reduceFst_eq_frob_reduceSnd_of_isZeroSide_prolongationDatum
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_ord_residue_eq_mul_ord_of_coe_eq_modularUnitSeries_of_not_isAffinePlace
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ord_eq_mul_ord_of_coe_eq_coeffEmb_modularUnitSeries_of_isInftySide
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_oneSidedFst_laws_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ValuationSubring.instIsAlgClosedResidueField ModularCurve.TwoChart.isOpenImmersion_fInf ModularCurve.TwoChart.isOpenImmersion_ιFin ModularCurve.TwoChart.isOpenImmersion_ιInf ModularCurve.TwoChart.isOpenImmersion_fFin AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun"
p2m_attr_erase "simp" "KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.TwoChart.coe_jChartFin ModularCurve.TwoChart.ιFin_modelTo ModularCurve.TwoChart.ιInf_modelTo ModularCurve.TwoChart.ιInf_modelTo_assoc ModularCurve.TwoChart.coe_jInvChartInf ModularCurve.TwoChart.ιFin_modelTo_assoc AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve~PlaceSpecialization ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP"

open scoped MatrixGroups

open Classical in

section

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]

private theorem specJ_ramificationIndexAlong_pos {F F' : Type*} [Field F] [Field F']
    [Algebra (AlgebraicClosure ℚ) F] [Algebra (AlgebraicClosure ℚ) F']
    (φ : F →ₐ[(AlgebraicClosure ℚ)] F') (hφ : φ.toRingHom.IsIntegral) (w : Place (AlgebraicClosure ℚ) F') :
    0 < w.ramificationIndexAlong φ := by
  unfold Place.ramificationIndexAlong
  letI := algebraAlong φ
  haveI := isIntegral_along φ hφ
  exact Place.ramificationIndex_pos (F := F) w

open Classical in

private theorem specJ (hpM2 : ¬ p ^ 2 ∣ M) (hA : A.LiesOverPrime p)
    (Psp : JHPlaceSpecialization p M H hpM A)
    (x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hx : ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (xb : JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A))
    (hxb : ((xb : JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
      jqModC (IsLocalRing.ResidueField ↥A))
    (Dj : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hDj : ∀ b, Dj b = b.ord x)
    (v : Place (IsLocalRing.ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)))
    (hv : v.ord xb ≤ 0) :
    Finsupp.mapDomain Psp.sp (Dj.filter (fun b => Dj b < 0)) v = v.ord xb := by
  set Pl : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    Finsupp.mapRange (fun n : ℤ => max (-n) 0) (by simp) Dj with hPl_def
  have hPl : ∀ b, Pl b = max (-b.ord x) 0 := fun b => by
    rw [hPl_def, Finsupp.mapRange_apply, hDj]
  have hfilt : Dj.filter (fun b => Dj b < 0) = -Pl := by
    ext b
    rw [Finsupp.filter_apply, Finsupp.neg_apply, hPl_def, Finsupp.mapRange_apply]
    by_cases h : Dj b < 0
    · rw [if_pos h, max_eq_left (by omega), neg_neg]
    · rw [if_neg h, max_eq_right (by omega), neg_zero]
  have eng := (ModularCurve.JHPlaceSpecialization.mapDomain_sp_zeros_sub_algebraMap_eq_and_mapDomain_sp_poles_eq_of_coe_eq_jqModC p M H hpM hpM2 A hA Psp x xb hx hxb).2 Pl hPl v
  rw [hfilt, ← Finsupp.mapDomain.addMonoidHom_apply, map_neg, Finsupp.neg_apply, Finsupp.mapDomain.addMonoidHom_apply, eng,
    max_eq_left (by omega), neg_neg]

open Classical in

private theorem specJ_reduceFst (hpM2 : ¬ p ^ 2 ∣ M) (hA : A.LiesOverPrime p)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[(AlgebraicClosure ℚ)] ↥(xHFunctionFieldBar M H)) (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A)
    (x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hx : ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (xb : JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A))
    (hxb : ((xb : JHNeronObjectAtP.Fbar p M H hpM (IsLocalRing.ResidueField ↥A)) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
      jqModC (IsLocalRing.ResidueField ↥A))
    (Dj : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hDj : ∀ b, Dj b = b.ord x)
    (C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hC : JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C) :
    Finsupp.mapDomain Psp.sp (Dj.filter (fun b => Dj b < 0)) (Psp.reduceFst α hα C) = (Psp.reduceFst α hα C).ord xb := by
  apply specJ hpM2 hA Psp x hx xb hxb Dj hDj

  have hw : ∀ a : ↥A, (C.restrictAlong α hα).ord
      (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ≤ 0 := by
    intro a
    have hC' := hC.1 (α x) (by rw [hα_coe, hx]) a
    rw [show α x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ))
        = α (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) by
          rw [map_sub, AlgHom.commutes],
      Place.ord_restrictAlong α hα] at hC'
    have he := specJ_ramificationIndexAlong_pos α hα C
    by_contra hpos
    rw [not_le] at hpos
    exact absurd hC' (not_le.mpr (mul_pos (by exact_mod_cast he) hpos))
  exact (ModularCurve.JHPlaceSpecialization.ord_sp_neg_of_forall_ord_sub_algebraMap_le p M H hpM hpM2 A hA Psp x xb hx hxb (C.restrictAlong α hα) hw).le

end

section InfDiv

private theorem infdiv_ordUnitInfH
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (u : ↥(xHFunctionFieldBar M H))
    (hu : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p))
    (xM : ↥(xHFunctionFieldBar M H))
    (hxM : ((xM : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hW : JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) W) :
    W.ord u = ((p : ℤ) - 1) * W.ord xM := by
  exact ModularCurve.JHPlaceSpecialization.ord_eq_mul_ord_of_coe_eq_coeffEmb_modularUnitSeries_of_isInftySide p M H hpM A u hu xM hxM W hW

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}

private theorem infdiv_mapDomain_restrictAlong_apply
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (hα : α.IsIntegral)
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (b : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
    Finsupp.mapDomain (fun W => W.restrictAlong α hα) E b = ∑ W ∈ Place.fiberAlong α hα b, E W := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  simp only [Finsupp.single_apply]
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro W hW
    rw [Finset.mem_filter] at hW
    rw [Place.mem_fiberAlong]
    exact hW.2
  · intro W hWf hW
    rw [Finset.mem_filter, not_and] at hW
    by_contra hne
    exact hW (Finsupp.mem_support_iff.mpr hne) ((Place.mem_fiberAlong).mp hWf)

private theorem infdiv_ord_sub_algebraMap_of_ord_neg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf0 : f ≠ 0) (hf : v.ord f < 0) (c : K) : v.ord (f - algebraMap K F c) = v.ord f := by
  by_cases hc : c = 0
  · rw [hc, map_zero, sub_zero]
  · have hnc : -c ≠ 0 := neg_ne_zero.mpr hc
    have hc' : algebraMap K F (-c) ≠ 0 := (_root_.map_ne_zero (algebraMap K F)).mpr hnc
    have hordc : v.ord (algebraMap K F (-c)) = 0 := (v.hasValue_algebraMap (-c)).ord_eq_zero hnc
    have hvf := v.adicValuation_ne_zero hf0
    have hvg := v.adicValuation_ne_zero hc'
    have hlt : v.adicValuation (algebraMap K F (-c)) < v.adicValuation f := by
      rw [← WithZero.log_lt_log hvg hvf]
      have h' : v.ord f < v.ord (algebraMap K F (-c)) := by rw [hordc]; exact hf
      simp only [Place.ord] at h'
      linarith
    rw [sub_eq_add_neg, ← map_neg]
    simp only [Place.ord, v.adicValuation.map_add_eq_of_lt_left hlt]

open Classical in

theorem infdiv_mapDomain_restrictAlong_filter_isInftySide_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (u : ↥(xHFunctionFieldBar M H))
    (hu : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p))
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hD : ∀ W, D W = W.ord u)
    (x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hx : ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (Dx : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hDx : ∀ b, Dx b = b.ord x)
    (b : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
    Finsupp.mapDomain (fun W => W.restrictAlong α hα)
        (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) b
      = ((p : ℤ) - 1) * (Dx.filter (fun b' => Dx b' < 0)) b := by
  classical
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar M H

  have hαx : ((α x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by rw [hα_coe, hx]
  have hx0 : x ≠ 0 := by
    intro h0
    apply jqModC_ne_zero_def (AlgebraicClosure ℚ)
    rw [← hx, h0]
    rfl

  have hordαx : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), W.ord (α x) = (W.ramificationIndexAlong α : ℤ) * (W.restrictAlong α hα).ord x :=
    fun W => Place.ord_restrictAlong α hα W x
  rw [infdiv_mapDomain_restrictAlong_apply α hα, Finsupp.filter_apply]
  have hterm : ∀ W ∈ Place.fiberAlong α hα b,
      (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) W
        = if JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) W then
            ((p : ℤ) - 1) * ((W.ramificationIndexAlong α : ℤ) * Dx b)
          else 0 := by
    intro W hW
    rw [Finsupp.filter_apply]
    split_ifs with hWi
    · rw [hD, infdiv_ordUnitInfH p M H hpM A u hu (α x) hαx W hWi, hordαx W, (Place.mem_fiberAlong).mp hW, hDx]
    · rfl
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, ← Finset.mul_sum]
  split_ifs with hneg
  ·
    have hb : ∀ x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
        ∀ a : ↥A, b.ord (x' - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) ≤ 0 := by
      intro x' hx' a
      have hxx : x' = x := Subtype.ext (hx'.trans hx.symm)
      rw [hxx]
      have hneg' : b.ord x < 0 := by rw [← hDx]; exact hneg
      rw [infdiv_ord_sub_algebraMap_of_ord_neg b hx0 hneg']
      exact hneg'.le
    rw [← Finset.sum_mul,
      ModularCurve.JHPlaceSpecialization.sum_ramificationIndexAlong_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_sub_nonpos
        p M H hpM hpM2 hHp A hA α hα hα_coe b hb, one_mul]
  · rw [mul_zero]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro W hW
    rw [Finset.mem_filter] at hW
    have hWb := (Place.mem_fiberAlong).mp hW.1
    have hcusp : W.ord (α x) ≤ 0 := by
      have h := hW.2.1 (α x) hαx 0
      simpa using h
    rw [hordαx W, hWb, ← hDx] at hcusp
    exact le_antisymm hcusp (mul_nonneg (Int.natCast_nonneg _) (not_lt.mp hneg))

end InfDiv

section C6Aux

private theorem c6_mapDomain_apply_eq_zero_of_forall {α β : Type*} (f : α → β) (g : α →₀ ℤ) (v : β)
    (h : ∀ a ∈ g.support, f a ≠ v) : Finsupp.mapDomain f g v = 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  exact Finset.sum_eq_zero (fun a ha => by simp [(h a ha).symm])

private theorem c6_mapDomain_filter_apply_of_pred {α β : Type*} (f : α → β) (g : α →₀ ℤ) (r : β → Prop)
    [DecidablePred r] (v : β) (hv : r v) :
    Finsupp.mapDomain f (g.filter (fun a => r (f a))) v = Finsupp.mapDomain f g v := by
  classical
  rw [Finsupp.mapDomain, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_apply, Finsupp.sum,
    Finsupp.sum, Finsupp.support_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases hfa : f a = v
  · simp [hfa, hv]
  · simp [Ne.symm hfa]

private theorem c6_surjK {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
  {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

private theorem c6_ord_carrier_neg (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hv : ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v)
    (x : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (hx : ((x : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A)) :
    v.ord x < 0 := by
  by_contra hnot
  rw [not_lt] at hnot
  have hx0 : x ≠ 0 := by
    intro h0
    apply jqModC_ne_zero_def (ResidueField ↥A)
    rw [← hx, h0]
    rfl
  have hmem : x ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hx0 hnot
  haveI : (JHNeronObjectAtP.ΓN p M H hpM).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH (M / p) (infSubgroup p M H hpM))
  have hT : ModularGroup.T ∈ JHNeronObjectAtP.ΓN p M H hpM := ModularCurve.translation_mem_GammaH (M / p) (infSubgroup p M H hpM)
  haveI : IsCurveOver (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :=
    ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) hT
  obtain ⟨b, hb, -⟩ := v.exists_hasValue_of_surjective (c6_surjK _) hmem
  exact hv ⟨x, b, hx, hb⟩

end C6Aux

section C6Frame

variable
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
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
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

    (u : ↥(xHFunctionFieldBar M H))
    (hu : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p))
    (h₁ : u ∈ Rpd.R₁.integers)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hD : ∀ W, D W = W.ord u)

include p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ α hα hβ Psp Rpd hwgen hθ hα_coe hTD hmodel hcompat hcompat' u hu h₁ D hD

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Classical in

private theorem c6_identity
    (x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hx : ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (hxb : ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (Dj : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hDj : ∀ b, Dj b = b.ord x)
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hv : ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v) :
    Finsupp.mapDomain (Psp.reduceFst α hα) (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) v = v.ord (Rpd.R₁.residue ⟨u, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  revert v

  intro v hv
  have hcomp : Finsupp.mapDomain (Psp.reduceFst α hα) (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)))
      = Finsupp.mapDomain (Psp.sp ∘ fun W => W.restrictAlong α hα) (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) := rfl
  have hpush : Finsupp.mapDomain (fun W => W.restrictAlong α hα) (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)))
      = ((p : ℤ) - 1) • Dj.filter (fun b' => Dj b' < 0) := by
    ext b
    rw [Finsupp.smul_apply, smul_eq_mul]
    exact infdiv_mapDomain_restrictAlong_filter_isInftySide_eq p M H hpM hpM2 hHp A hA α hα hα_coe u hu D hD x hx Dj hDj b
  rw [hcomp, Finsupp.mapDomain_comp, hpush, Finsupp.mapDomain_smul, Finsupp.smul_apply, smul_eq_mul,
    specJ hpM2 hA Psp x hx xb hxb Dj hDj v (c6_ord_carrier_neg v hv xb hxb).le,
    ModularCurve.JHPlaceSpecialization.ProlongationDatum.ord_residue_eq_mul_ord_of_coe_eq_modularUnitSeries_of_not_isAffinePlace
      p M H hpM A hA θ Psp Rpd u hu h₁ v hv xb hxb]

private theorem c6_cusp_nonaffine
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hW : JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) W) : ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα W) := by
  revert W

  intro W hW
  rcases ModularCurve.JHPlaceSpecialization.isInftySide_or_isZeroSide_of_isCuspidal p M H hpM A hA W hW with hinf | hzero
  · exact ModularCurve.XHDRModelAtP.not_isAffinePlace_reduceFst_of_isInftySide_prolongationDatum
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcompat W hinf
  · rw [ModularCurve.XHDRModelAtP.reduceFst_eq_frob_reduceSnd_of_isZeroSide_prolongationDatum
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcompat hcompat' W hzero]
    exact ModularCurve.XHDRModelAtP.not_isAffinePlace_frob_reduceSnd_of_isZeroSide_prolongationDatum
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcompat W hzero

private theorem c6_strict_iff
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hW : JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) W) (hnf : ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα W)) :
    (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ↔ JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) W) := by
  revert W

  intro W hW hnf

  have hssfin : (ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p).Finite :=
    (ModularCurve.JHPlaceSpecialization.finite_setOf_fixed_of_eq_gammaLift p M H hpM hpM2 A hA pb hpb δ hδ).subset
      (fun y hy => ModularCurve.JHPlaceSpecialization.fixed_of_mem_ssPlacesQExp p M H hpM hpM2 A pb hpb δ hδ y hy)
  have hnpfin : (ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p).Finite := by
    refine (hssfin.image (fun y => (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p y, y))).subset ?_
    rintro ⟨s1, s2⟩ ⟨h2, h1⟩
    exact ⟨s2, h2, Prod.ext h1.symm rfl⟩
  obtain ⟨hOinf, hOzero⟩ :=
    ModularCurve.XHDRModelAtP.cuspOrientationInf_and_cuspOrientationZero_of_jHPlaceSpecialization_of_offDiag
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ hnpfin.toFinset (fun s => hnpfin.mem_toFinset)
      θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat'
  constructor
  · intro hs
    rcases ModularCurve.JHPlaceSpecialization.isInftySide_or_isZeroSide_of_isCuspidal p M H hpM A hA W hW with hinf | hzero
    · exact hinf
    · exfalso
      apply hnf
      show qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα W))) = Psp.reduceFst α hα W
      rw [hs.1]
      exact (hOzero W hzero).symm
  · intro hinf
    exact ⟨hOinf W hinf, hnf⟩

private theorem c6_cusp_of_ne
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hW : D W ≠ 0) : JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) W :=
  ModularCurve.JHPlaceSpecialization.isCuspidal_of_ord_ne_zero_of_coe_eq_coeffEmb_modularUnitSeries p M H hpM A u hu W
    (by rw [← hD W]; exact hW)

open Classical in

private theorem c6_filter_eq :
    Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D =
      (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))).filter (fun W => ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα W)) := by
  have strict_iff := c6_strict_iff p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ α hα hβ Psp Rpd hwgen hθ hα_coe hTD hmodel hcompat hcompat' u hu h₁ D hD
  have cusp_of_ne := c6_cusp_of_ne p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ α hα hβ Psp Rpd hwgen hθ hα_coe hTD hmodel hcompat hcompat' u hu h₁ D hD

  ext W
  simp only [JHPlaceSpecialization.fstDiv, Finsupp.filter_apply]
  by_cases hz : D W = 0
  · simp [hz]
  · by_cases hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα W)
    · have hs : ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W := fun h => h.2 hfix
      rw [if_neg hs, if_neg (not_not.mpr hfix)]
    · have hiff := strict_iff W (cusp_of_ne W hz) hfix
      by_cases hs : Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W
      · rw [if_pos hs, if_pos hfix, if_pos (hiff.mp hs)]
      · rw [if_neg hs, if_pos hfix, if_neg (fun hi => hs (hiff.mpr hi))]

private theorem c6_res_unit
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hss : v ∉ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)
    (xj : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (hxj : ((xj : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A)) (a : ResidueField ↥A) (hva : v.HasValue xj a) :
    v.ord (Rpd.R₁.residue ⟨u, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) = 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨⟨xZ, hxZ, -, -⟩, -, -, -⟩ :=
    ModularCurve.exists_int_coeffMap_eq_modularUnitSeries_and_mem_qExpFunctionFieldC_gammaH_of_dvd p M H hpM
  have hZ : ∀ {R : Type} [CommRing R] (f g : ℤ →+* R), f = g := fun f g => Subsingleton.elim f g
  have hy : coeffMap A.subtype (coeffMap (Int.castRingHom ↥A) xZ) = ((u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [coeffMap_coeffMap, hu, ← hxZ]
    show _ = coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (coeffMap (Int.castRingHom ℚ) xZ)
    rw [coeffMap_coeffMap, hZ (A.subtype.comp (Int.castRingHom ↥A)) ((algebraMap ℚ (AlgebraicClosure ℚ)).comp (Int.castRingHom ℚ))]
  obtain ⟨h₁', hres⟩ := Rpd.residue₁_coeffMap (coeffMap (Int.castRingHom ↥A) xZ) (by rw [hy]; exact u.2)
  have hg : ((Rpd.R₁.residue ⟨u, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = coeffMap (Int.castRingHom (ResidueField ↥A)) xZ := by
    have hsub : (⟨u, h₁⟩ : ↥Rpd.R₁.integers) = ⟨⟨coeffMap A.subtype (coeffMap (Int.castRingHom ↥A) xZ), by rw [hy]; exact u.2⟩, h₁'⟩ :=
      Subtype.ext (Subtype.ext hy.symm)
    rw [hsub, hres, coeffMap_coeffMap, hZ ((IsLocalRing.residue ↥A).comp (Int.castRingHom ↥A)) (Int.castRingHom (ResidueField ↥A))]
  exact ModularCurve.ord_eq_zero_of_not_mem_ssPlacesQExp_of_hasValue_of_coe_eq_coeffMap_modularUnitSeries
    p (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) xZ hxZ (Rpd.R₁.residue ⟨u, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) hg v hss xj hxj a hva

end C6Frame

open Classical in

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
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)

    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
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

    (u : ↥(xHFunctionFieldBar M H))
    (hu : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries p))
    (h₁ : u ∈ Rpd.R₁.integers)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hD : ∀ W, D W = W.ord u) :
    (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D) v = v.ord (Rpd.R₁.residue ⟨u, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  let x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := ⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _))⟩
  have hx : ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    show coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = _
    exact coeffMap_jqModC _
  let xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) := ⟨jqModC (ResidueField ↥A), intFormRatiosC_subset (ResidueField ↥A) _ (ModularCurve.jqModC_mem_intFormRatiosC (ResidueField ↥A) _)⟩
  have hxb : ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := rfl
  have hx0 : x ≠ 0 := by
    intro h0
    apply jqModC_ne_zero_def (AlgebraicClosure ℚ)
    rw [← hx, h0]
    rfl
  haveI hPDp : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)
  obtain ⟨Dj, hDj, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) x hx0
  have identity := c6_identity p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ α hα hβ Psp Rpd hwgen hθ hα_coe hTD hmodel hcompat hcompat' u hu h₁ D hD x hx xb hxb Dj hDj
  refine ⟨fun v hv => ?_, fun C hC => ?_⟩
  ·
    by_cases haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v
    ·
      obtain ⟨xj, a, hxj, hva⟩ := haff
      have hss : v ∉ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p := fun hw =>
        hv (ModularCurve.JHPlaceSpecialization.fixed_of_mem_ssPlacesQExp p M H hpM hpM2 A pb hpb δ hδ v hw)
      rw [c6_res_unit p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ α hα hβ Psp Rpd hwgen hθ hα_coe hTD hmodel hcompat hcompat' u hu h₁ D hD v hss xj hxj a hva]
      apply c6_mapDomain_apply_eq_zero_of_forall
      intro W hWs hWv
      rw [Finsupp.mem_support_iff] at hWs
      have hne : D W ≠ 0 := by
        intro h0
        apply hWs
        simp only [JHPlaceSpecialization.fstDiv, Finsupp.filter_apply, h0, ite_self]
      exact c6_cusp_nonaffine p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ α hα hβ Psp Rpd hwgen hθ hα_coe hTD hmodel hcompat hcompat' u hu h₁ D hD W (c6_cusp_of_ne p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ α hα hβ Psp Rpd hwgen hθ hα_coe hTD hmodel hcompat hcompat' u hu h₁ D hD W hne) (by rw [hWv]; exact ⟨xj, a, hxj, hva⟩)
    · calc Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D) v
          = Finsupp.mapDomain (Psp.reduceFst α hα)
              ((D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))).filter (fun W => ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα W))) v := by
            rw [c6_filter_eq p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ α hα hβ Psp Rpd hwgen hθ hα_coe hTD hmodel hcompat hcompat' u hu h₁ D hD]
        _ = Finsupp.mapDomain (Psp.reduceFst α hα) (D.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) v :=
            c6_mapDomain_filter_apply_of_pred (Psp.reduceFst α hα) _ (fun y => ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ y) v hv
        _ = v.ord (Rpd.R₁.residue ⟨u, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := identity v haff
  ·
    exact identity (Psp.reduceFst α hα C)
      (ModularCurve.XHDRModelAtP.not_isAffinePlace_reduceFst_of_isInftySide_prolongationDatum
        p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcompat C hC)

end S_ModularCurve_XHDRModelAtP_oneSidedFst_laws_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_oneSidedFst_laws_of_coe_eq_coeffEmb_modularUnitSeries_prolongationDatum_of_isModel (solution)
