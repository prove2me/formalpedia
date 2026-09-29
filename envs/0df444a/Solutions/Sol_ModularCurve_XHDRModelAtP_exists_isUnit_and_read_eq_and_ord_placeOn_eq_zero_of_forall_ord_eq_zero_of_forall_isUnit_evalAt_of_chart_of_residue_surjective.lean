-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_isUnit_and_read_eq_and_ord_placeOn_eq_zero_of_forall_ord_eq_zero_of_forall_isUnit_evalAt_of_chart_of_residue_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/79daf6d3-3d39-54f3-a052-2bbbd1d7bc6f

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_UVCrossingModel

import Theorems.Thm_ModularCurve_XHDRModelAtP_isNoetherianRing_stalk_and_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_chart
import Theorems.Thm_ModularCurve_XHDRModelAtP_injective_stalkRead_and_stalkRead_germ_eq_read_chart_and_forall_section_evalAt_stalkRead_eq_of_chart
import Theorems.Thm_ValuationSubring_exists_ringHom_forall_eq_mul_units_and_forall_exists_ringHom_adicCompletion_comp_eq_of_liesOverPrime
import Theorems.Thm_IsLocalRing_exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel
import Theorems.Thm_AlgebraicCurve_Place_mk_mem_maximalIdeal_iff
import Theorems.Thm_AlgebraicCurve_Place_evalAt_eq_zero_iff_one_le_ord
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_isRational_section_forall_mem_iff_stalkClosedPointTo_eq_zero_of_isPrime_of_not_mem
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_isUnit_section_read_eq_stalkRead_of_isUnit
import Theorems.Thm_ModularCurve_XHDRModelAtP_forall_exists_isDiscreteValuationRing_specializes_and_mul_stalkRead_eq_stalkRead
import Theorems.Thm_IsLocalRing_exists_units_forall_mul_const_pow_eq_mul_monomial_of_ringEquiv_adicCompletion_uvCrossingModel_of_forall_prime_mem_localization
import Theorems.Thm_IsLocalRing_exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_units
import Theorems.Thm_ModularCurve_XHDRModelAtP_ord_placeOn_germ_eq_zero_of_isUnit_section
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_comp_eq_specMap_and_mem_maximalIdeal_and_mul_eq_of_section_of_chart
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_section_base_closedPoint_eq_and_comp_eq_specMap_of_chart
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_isRational_comp_eq_pointEquivPlace_and_eq_of_comp_eq
import Theorems.Thm_MvPolynomial_CrossingQuotient_existsUnique_ringHom_comp_algebraMap_eq_and_apply_U_eq_and_apply_V_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_read_chart_mul_eq_and_isUnit_germ_and_smul_eq_and_evalAt_eq_of_chart
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow
import Theorems.Thm_ModularCurve_UVCrossingModel_const_mem_nonZeroDivisors
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_isUnit_and_read_eq_and_ord_placeOn_eq_zero_of_forall_ord_eq_zero_of_forall_isUnit_evalAt_of_chart_of_residue_surjective
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation"
p2m_attr_erase "instance" "ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero"
p2m_attr_erase "simp" "compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.ProjectiveLine.map_mk ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆"
p2m_attr_erase "simp" "TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicCurve ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP MvPolynomial

open scoped MatrixGroups

set_option maxHeartbeats 1600000 in
theorem ntcore3
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ)

    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ) (he : 1 ≤ e) (U : (XO (ΓM M H) hj ρO).Opens) (hxU : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n ∈ U)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) = U.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔ U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
    (hpt : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      (f.stalkMap y).hom.Flat ∧ Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧ IsIso (f.residueFieldMap y))
    (het : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n → ∃ V : (U : Scheme.{0}).Opens, y ∈ V ∧ Etale (V.ι ≫ f))
    (hor₁ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₂ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₃ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)

    (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']
    (σ : O →+* O') (ιA' : O' →+* ↥A) (hσ : ιA'.comp σ = ιA) (hιA'inj : Function.Injective ιA') (hιA'loc : IsLocalHom ιA')
    (jO' : O' →+* AlgebraicClosure ℚ) (hjO' : jO'.comp (σ.comp ρO) = algebraMap (R p) (AlgebraicClosure ℚ)) (hιA'j : A.subtype.comp ιA' = jO')
    (htoκ' : ((IsLocalRing.residue ↥A).comp ιA').comp (σ.comp ρO) = (IsLocalRing.residue ↥A).comp ρ)
    (ϖ' : O') (hϖ' : IsLocalRing.maximalIdeal O' = Ideal.span {ϖ'}) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
    letI VM : (𝔛.Meta).C.Opens := 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)
    letI Q := CrossingQuotient O (((p : ℕ) : O) ^ e)
    letI φ : Q →+* Γ(CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI gv : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.V (((p : ℕ) : O) ^ e))))
    letI gu : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.U (((p : ℕ) : O) ^ e))))
    ∀ hgen : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤)),
    letI read : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) →+* ↥(xHFunctionFieldBar M H) :=
      (𝔛.Meta).ffEquiv.symm.toRingHom.comp
        (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
          ((𝔛.eeta.app (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prJ.app (U.ι ''ᵁ ⊤)).hom))
    letI param : ↥(xHFunctionFieldBar M H) := read gv
    letI param' : ↥(xHFunctionFieldBar M H) := read gu
    letI bc' := bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ'
    letI xn' : ↥(XO (ΓM M H) hj (σ.comp ρO)) := (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc').base n
    letI prJ' : XQ ⟶ XO (ΓM M H) hj (σ.comp ρO) :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
    letI prσ : XO (ΓM M H) hj (σ.comp ρO) ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom σ)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
    letI B := (XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalk xn'
    letI σB : O' →+* ↥B := ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ ⊤ xn' trivial).hom.comp
      (((XO.toBase (ΓM M H) hj (σ.comp ρO)).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
    ∀ (hsp : prJ'.base (𝔛.eeta.base (genericPoint (𝔛.Meta).C)) ⤳ xn'),
    letI emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
        ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
          ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes hsp).hom))
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
    ∀ g : ↥(xHFunctionFieldBar M H), (∃ r s₀ : ↥B, s₀ ≠ 0 ∧ g * emb s₀ = emb r) →
      ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsNoetherianRing B) (_ : IsLocalRing B)
        (σB : O' →+* B) (_ : IsLocalHom σB)
        (emb : B →+* ↥(xHFunctionFieldBar M H)) (_ : Function.Injective emb)
        (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsDiscreteValuationRing W')
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W') W')
        (π' : W') (_ : Irreducible π') (E' : ℕ) (_ : 1 ≤ E')
        (ι' : AdicCompletion (IsLocalRing.maximalIdeal B) B ≃+* UVCrossingModel W' (π' ^ E'))
        (w₀ : (UVCrossingModel W' (π' ^ E'))ˣ)
        (_ : ι' (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) (σB ϖ')) = (w₀ : UVCrossingModel W' (π' ^ E')) * UVCrossingModel.const (π' ^ E') π')
        (bu bv : B) (wu : (UVCrossingModel W' (π' ^ E'))ˣ)
        (_ : ι' (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) bu) = UVCrossingModel.U (π' ^ E') * (wu : UVCrossingModel W' (π' ^ E')))
        (_ : ι' (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) bv) = UVCrossingModel.V (π' ^ E'))
        (_ : emb bv = param) (_ : emb bu = param')
        (_ : ∃ r s : B, s ≠ 0 ∧ g * emb s = emb r)

        (S : Type) (_ : CommRing S) (jA : ↥A →+* S)
        (_ : ∀ (α β : ↥A) (u : Sˣ), jA α = jA β * (u : S) → ∃ v : (↥A)ˣ, α = β * (v : ↥A)),

        (∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), W.IsRational →
          ∀ (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
            s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
            barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ →
            U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
          ∃ (χ : B →+* ↥A) (ψ : AdicCompletion (IsLocalRing.maximalIdeal B) B →+* S),
          IsLocalHom χ ∧ χ.comp σB = ιA' ∧ ψ.comp (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)) = jA.comp χ ∧
          (∀ b : B, emb b ∈ W.toValuationSubring ∧ W.evalAt (emb b) = ((χ b : ↥A) : AlgebraicClosure ℚ)) ∧
          (∀ (x : ↥(xHFunctionFieldBar M H)), x ∈ W.toValuationSubring → (∃ r s₀ : B, s₀ ≠ 0 ∧ x * emb s₀ = emb r) →
            ∃ r s₀ : B, χ s₀ ≠ 0 ∧ x * emb s₀ = emb r)) ∧

        (∀ P : Ideal B, P.IsPrime → P ≠ ⊥ → σB ϖ' ∉ P →
          ∃ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (_ : W.IsRational)
            (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0}))
            (_ : s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA))
            (_ : barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ)
            (_ : U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
            (χ : B →+* ↥A),
            (IsLocalHom χ ∧ χ.comp σB = ιA' ∧
              (∀ b : B, emb b ∈ W.toValuationSubring ∧ W.evalAt (emb b) = ((χ b : ↥A) : AlgebraicClosure ℚ)) ∧
              (∀ (x : ↥(xHFunctionFieldBar M H)), x ∈ W.toValuationSubring → (∃ r s₀ : B, s₀ ≠ 0 ∧ x * emb s₀ = emb r) →
                ∃ r s₀ : B, χ s₀ ≠ 0 ∧ x * emb s₀ = emb r)) ∧
            ∀ b : B, b ∈ P ↔ χ b = 0) ∧

      (∀ t : B, IsUnit t →
        ∃ (U' : (XO (ΓM M H) hj ρ).Opens)
          (hx : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).base n ∈ U')
          (hgenA : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ U'))
          (γ : Γ(XO (ΓM M H) hj ρ, U')),
          IsUnit γ ∧
          (𝔛.Meta).ffEquiv.symm
          (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ U')) (genericPoint (𝔛.Meta).C) hgenA).hom
            ((𝔛.eeta.app (prA ⁻¹ᵁ U')).hom ((prA.app U').hom γ))) = emb t)
:= by
  intro hgen hsp g hgfrac
  have h2 := ModularCurve.XHDRModelAtP.isNoetherianRing_stalk_and_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_chart p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄ O' σ ιA' hσ hιA'inj hιA'loc jO' hjO' hιA'j htoκ' ϖ' hϖ'
  obtain ⟨hnoeth, hdom, E', hE', W', i1, i2, i3, i4, σ', hmW', hresW', ι', hconst, hmem2, ⟨wu, hbu⟩, hbv⟩ := h2
  have h3 := ModularCurve.XHDRModelAtP.injective_stalkRead_and_stalkRead_germ_eq_read_chart_and_forall_section_evalAt_stalkRead_eq_of_chart p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄ O' σ ιA' hσ hιA'inj hιA'loc jO' hjO' hιA'j htoκ' hgen hsp
  obtain ⟨⟨hσBloc, hembinj, hconst3⟩, ⟨hmem3, hembv, hembu⟩, hsec⟩ := h3
  have hGS := ModularCurve.XHDRModelAtP.exists_isUnit_section_read_eq_stalkRead_of_isUnit p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄ O' σ ιA' hσ hιA'inj hιA'loc jO' hjO' hιA'j htoκ' hgen hsp
  have h6 := ModularCurve.XHDRModelAtP.exists_isRational_section_forall_mem_iff_stalkClosedPointTo_eq_zero_of_isPrime_of_not_mem p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n U hxU O' σ ιA' hσ hιA'inj hιA'loc jO' hjO' hιA'j htoκ' ϖ' hϖ'
  obtain ⟨S, i5, jA, hdesc, hψall⟩ :=
    ValuationSubring.exists_ringHom_forall_eq_mul_units_and_forall_exists_ringHom_adicCompletion_comp_eq_of_liesOverPrime p A hA
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
  let VM : (𝔛.Meta).C.Opens := 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)
  let Q := CrossingQuotient O (((p : ℕ) : O) ^ e)
  let φ : Q →+* Γ(CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
  let gv : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.V (((p : ℕ) : O) ^ e))))
  let gu : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.U (((p : ℕ) : O) ^ e))))
  let read : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) →+* ↥(xHFunctionFieldBar M H) :=
    (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
        ((𝔛.eeta.app (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prJ.app (U.ι ''ᵁ ⊤)).hom))
  let param : ↥(xHFunctionFieldBar M H) := read gv
  let param' : ↥(xHFunctionFieldBar M H) := read gu
  let bc' := bcMap (ΓM M H) hj (σ.comp ρO) ((IsLocalRing.residue ↥A).comp ιA') htoκ'
  let xn' : ↥(XO (ΓM M H) hj (σ.comp ρO)) := (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bc').base n
  let prJ' : XQ ⟶ XO (ΓM M H) hj (σ.comp ρO) :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO')) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO'])
  let prσ : XO (ΓM M H) hj (σ.comp ρO) ⟶ XO (ΓM M H) hj ρO :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom σ)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
  let B := (XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalk xn'
  let σB : O' →+* ↥B := ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ ⊤ xn' trivial).hom.comp
    (((XO.toBase (ΓM M H) hj (σ.comp ρO)).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of O')).inv.hom)
  let emb : ↥B →+* ↥(xHFunctionFieldBar M H) := (𝔛.Meta).ffEquiv.symm.toRingHom.comp
    ((𝔛.eeta.stalkMap (genericPoint (𝔛.Meta).C)).hom.comp
      ((prJ'.stalkMap (𝔛.eeta.base (genericPoint (𝔛.Meta).C))).hom.comp
        ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes hsp).hom))
  haveI : IsNoetherianRing ↥B := hnoeth
  haveI : IsDomain ↥B := hdom
  haveI : IsLocalHom σB := hσBloc
  have hirr : Irreducible (σ' ϖ') := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmW'
  have hϖB : ι' (algebraMap ↥B (AdicCompletion (IsLocalRing.maximalIdeal ↥B) ↥B) (σB ϖ')) =
      ((1 : (UVCrossingModel W' ((σ' ϖ') ^ E'))ˣ) : UVCrossingModel W' ((σ' ϖ') ^ E')) * UVCrossingModel.const ((σ' ϖ') ^ E') (σ' ϖ') := by
    rw [Units.val_one, one_mul]; exact hconst ϖ'
  have hϖ0 : ϖ' ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field O'
    rw [hϖ', h0, Ideal.span_singleton_eq_bot]

  have hlocal : ∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), W.IsRational →
      ∀ (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
        s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
        barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ →
        U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      ∀ (s' : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj (σ.comp ρO)),
        s' ≫ pullback.fst _ _ = s ≫ U.ι ≫ pullback.fst _ _ → s' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA') →
        ∀ (hx : s'.base (IsLocalRing.closedPoint ↥A) = xn'),
        letI χ : ↥B →+* ↥A :=
          (Scheme.stalkClosedPointTo s').hom.comp ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes (specializes_of_eq hx)).hom
        (IsLocalHom χ ∧ χ.comp σB = ιA' ∧
          (∀ b : ↥B, emb b ∈ W.toValuationSubring ∧ W.evalAt (emb b) = ((χ b : ↥A) : AlgebraicClosure ℚ))) →
        ∀ (x : ↥(xHFunctionFieldBar M H)), x ∈ W.toValuationSubring → (∃ r s₀ : ↥B, s₀ ≠ 0 ∧ x * emb s₀ = emb r) →
          ∃ r s₀ : ↥B, χ s₀ ≠ 0 ∧ x * emb s₀ = emb r := by
    intro W hrat s hs1 hs2 hs3 s' hs'1 hs'2 hx hχ x hxW hxfrac
    let χ : ↥B →+* ↥A := (Scheme.stalkClosedPointTo s').hom.comp ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.stalkSpecializes (specializes_of_eq hx)).hom
    obtain ⟨hχloc, hχcomp, hχev⟩ := hχ
    have hPm : RingHom.ker χ ≠ IsLocalRing.maximalIdeal ↥B := by
      intro hk
      have h1 : σB ϖ' ∈ IsLocalRing.maximalIdeal ↥B := map_nonunit σB ϖ' (by rw [hϖ']; exact Ideal.subset_span rfl)
      rw [← hk, RingHom.mem_ker] at h1
      have h2 : χ (σB ϖ') = ιA' ϖ' := RingHom.congr_fun hχcomp ϖ'
      rw [h1] at h2
      exact hϖ0 (hιA'inj (by rw [map_zero]; exact h2.symm))
    have hP : ∀ b : ↥B, b ∈ RingHom.ker χ ↔ emb b ∈ (W.toValuationSubring).nonunits := by
      intro b
      rw [RingHom.mem_ker, ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
      constructor
      · intro hb
        refine ⟨(hχev b).1, ?_⟩
        rw [AlgebraicCurve.Place.mk_mem_maximalIdeal_iff]
        by_cases h0 : emb b = 0
        · exact Or.inl h0
        · right
          have h1 := (AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord W hrat h0 (hχev b).1).mp (by rw [(hχev b).2, hb]; rfl)
          omega
      · rintro ⟨hm, hmax⟩
        rw [AlgebraicCurve.Place.mk_mem_maximalIdeal_iff] at hmax
        rcases hmax with h0 | hpos
        · have hb0 : b = 0 := hembinj (by rw [h0, map_zero])
          rw [hb0, map_zero]
        · have h0 : emb b ≠ 0 := fun h => by rw [h, AlgebraicCurve.Place.ord_zero] at hpos; exact lt_irrefl _ hpos
          have h1 := (AlgebraicCurve.Place.evalAt_eq_zero_iff_one_le_ord W hrat h0 (hχev b).1).mpr (by omega)
          rw [(hχev b).2] at h1
          exact_mod_cast h1
    obtain ⟨r, s₀, hs₀, hxr⟩ :=
      IsLocalRing.exists_notMem_and_mul_eq_of_mem_valuationSubring_of_ringEquiv_adicCompletion_uvCrossingModel
        (σ' ϖ') hirr E' hE' ι' emb hembinj W.toValuationSubring (fun b => (hχev b).1) (RingHom.ker χ) hP hPm x hxW hxfrac
    exact ⟨r, s₀, fun h => hs₀ (RingHom.mem_ker.mpr h), hxr⟩
  refine ⟨↥B, inferInstance, hdom, hnoeth, inferInstance, σB, hσBloc, emb, hembinj, W', i1, i2, i3, i4, σ' ϖ', hirr, E', hE', ι', 1, hϖB,
    ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ (prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) xn' hmem2).hom ((prσ.app (U.ι ''ᵁ ⊤)).hom gu),
    ((XO (ΓM M H) hj (σ.comp ρO)).presheaf.germ (prσ ⁻¹ᵁ (U.ι ''ᵁ ⊤)) xn' hmem2).hom ((prσ.app (U.ι ''ᵁ ⊤)).hom gv),
    wu, hbu, hbv, hembv, hembu, hgfrac, S, i5, jA, hdesc, ?_, ?_, fun t ht => hGS t ht⟩
  ·
    intro W hrat s hs1 hs2 hs3
    have hw : (s ≫ U.ι ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj =
        Spec.map (CommRingCat.ofHom ιA') ≫ Spec.map (CommRingCat.ofHom (σ.comp ρO)) := by
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% hs1, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hσ]
    let s' : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj (σ.comp ρO) := pullback.lift (s ≫ U.ι ≫ pullback.fst _ _) (Spec.map (CommRingCat.ofHom ιA')) hw
    have hs'1 : s' ≫ pullback.fst _ _ = s ≫ U.ι ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
    have hs'2 : s' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA') := pullback.lift_snd _ _ _
    obtain ⟨hx, hχ⟩ := hsec W hrat s hs1 hs2 hs3 s' hs'1 hs'2
    obtain ⟨hχloc, hχcomp, hχev⟩ := hχ
    obtain ⟨ψ, hψ⟩ := hψall ↥B _ hχloc
    exact ⟨_, ψ, hχloc, hχcomp, hψ, hχev, hlocal W hrat s hs1 hs2 hs3 s' hs'1 hs'2 hx ⟨hχloc, hχcomp, hχev⟩⟩
  ·
    intro P hP hP0 hϖP
    specialize h6 P hP hP0 hϖP
    obtain ⟨W, hrat, s, hs1, hs2, hs3, hker⟩ := h6
    have hw : (s ≫ U.ι ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj =
        Spec.map (CommRingCat.ofHom ιA') ≫ Spec.map (CommRingCat.ofHom (σ.comp ρO)) := by
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% hs1, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hσ]
    let s' : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj (σ.comp ρO) := pullback.lift (s ≫ U.ι ≫ pullback.fst _ _) (Spec.map (CommRingCat.ofHom ιA')) hw
    have hs'1 : s' ≫ pullback.fst _ _ = s ≫ U.ι ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
    have hs'2 : s' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA') := pullback.lift_snd _ _ _
    obtain ⟨hx, hχ⟩ := hsec W hrat s hs1 hs2 hs3 s' hs'1 hs'2
    obtain ⟨hχloc, hχcomp, hχev⟩ := hχ
    exact ⟨W, hrat, s, hs1, hs2, hs3, _, ⟨hχloc, hχcomp, hχev, hlocal W hrat s hs1 hs2 hs3 s' hs'1 hs'2 hx ⟨hχloc, hχcomp, hχev⟩⟩,
      hker s' hs'1 hs'2 hx⟩

set_option maxHeartbeats 3200000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : R p →+* O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (toκ : O →+* ResidueField ↥A) (htoκ : toκ.comp ρO = (IsLocalRing.residue ↥A).comp ρ) (htoκs : Function.Surjective toκ)

    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO) (hιAκ : (IsLocalRing.residue ↥A).comp ιA = toκ)

    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)))
    (e : ℕ) (he : 1 ≤ e) (U : (XO (ΓM M H) hj ρO).Opens) (hxU : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n ∈ U)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e))
    (hover : f ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O (((p : ℕ) : O) ^ e)))) = U.ι ≫ pullback.snd _ _)
    (hfib : ∀ y : ↥(U : Scheme.{0}),
      (CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal ∧ CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) ↔ U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n)
    (hpt : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      (f.stalkMap y).hom.Flat ∧ Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧ IsIso (f.residueFieldMap y))
    (het : ∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n → ∃ V : (U : Scheme.{0}).Opens, y ∈ V ∧ Etale (V.ι ≫ f))
    (hor₁ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₂ : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal → U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base)
    (hor₃ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.V (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal)
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (𝔛.comp A hA ρ hρ 1 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base → CrossingQuotient.U (((p : ℕ) : O) ^ e) ∈ (f.base y).asIdeal) :
    letI XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
    letI prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
    letI prA : XQ ⟶ XO (ΓM M H) hj ρ :=
      pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom A.subtype)) (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ])
    letI bcA := bcMap (ΓM M H) hj ρ (IsLocalRing.residue ↥A) rfl
    ∀ g : ↥(xHFunctionFieldBar M H),
      (∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), W.IsRational →
        ∀ (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
          s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
          barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ →
          U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
          W.ord g = 0 ∧ ∃ h : W.evalAt g ∈ A, IsUnit (⟨_, h⟩ : ↥A)) →
      ∃ (U' : (XO (ΓM M H) hj ρ).Opens) (hx : (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).base n ∈ U')
        (hgenA : genericPoint (𝔛.Meta).C ∈ 𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ U'))
        (γ : Γ(XO (ΓM M H) hj ρ, U')),
        IsUnit γ ∧
        (𝔛.Meta).ffEquiv.symm
          (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prA ⁻¹ᵁ U')) (genericPoint (𝔛.Meta).C) hgenA).hom
            ((𝔛.eeta.app (prA ⁻¹ᵁ U')).hom ((prA.app U').hom γ))) = g ∧
        (letI := (𝔛.Mfib A hA ρ hρ).isIntegral
         ∃ hg1 : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ U',
          (𝔛.Mfib A hA ρ hρ).ffEquiv.symm
              (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ U') (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg1)
                (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA).app U').hom γ)) ≠ 0 ∧
          (𝔛.placeOn1 A hA ρ hρ n).ord
            ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm
              (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA) ⁻¹ᵁ U') (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg1)
                (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1 ≫ bcA).app U').hom γ))) = 0) ∧
        (letI := (𝔛.Mfib A hA ρ hρ).isIntegral
         ∃ hg0 : genericPoint (𝔛.Mfib A hA ρ hρ).C ∈ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ U',
          (𝔛.Mfib A hA ρ hρ).ffEquiv.symm
              (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ U') (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg0)
                (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).app U').hom γ)) ≠ 0 ∧
          (𝔛.placeOn0 A hA ρ hρ n).ord
            ((𝔛.Mfib A hA ρ hρ).ffEquiv.symm
              (((𝔛.Mfib A hA ρ hρ).C.presheaf.germ ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA) ⁻¹ᵁ U') (genericPoint (𝔛.Mfib A hA ρ hρ).C) hg0)
                (((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcA).app U').hom γ))) = 0) := by
  intro g hyp
  obtain ⟨hgen, h1, -, -, h4⟩ :=
    ModularCurve.XHDRModelAtP.exists_read_chart_mul_eq_and_isUnit_germ_and_smul_eq_and_evalAt_eq_of_chart p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄
  have hA0 := ModularCurve.XHDRModelAtP.exists_comp_eq_specMap_and_mem_maximalIdeal_and_mul_eq_of_section_of_chart p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄
  have hA1 := ModularCurve.XHDRModelAtP.exists_section_base_closedPoint_eq_and_comp_eq_specMap_of_chart p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄
  have hA3 := ModularCurve.XHDRModelAtP.exists_isRational_comp_eq_pointEquivPlace_and_eq_of_comp_eq p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄
  let XQ : Scheme.{0} := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  let prJ : XQ ⟶ XO (ΓM M H) hj ρO :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
  let VM : (𝔛.Meta).C.Opens := 𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ U)
  let Q := CrossingQuotient O (((p : ℕ) : O) ^ e)
  let φ : Q →+* Γ(CrossingQuotient.crossingScheme (((p : ℕ) : O) ^ e), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
  let gv : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.V (((p : ℕ) : O) ^ e))))
  let gu : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) := (U.ι.appIso ⊤).inv (f.appTop (φ (CrossingQuotient.U (((p : ℕ) : O) ^ e))))
  let read : Γ(XO (ΓM M H) hj ρO, U.ι ''ᵁ ⊤) →+* ↥(xHFunctionFieldBar M H) :=
    (𝔛.Meta).ffEquiv.symm.toRingHom.comp
      (((𝔛.Meta).C.presheaf.germ (𝔛.eeta ⁻¹ᵁ (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))) (genericPoint (𝔛.Meta).C) hgen).hom.comp
        ((𝔛.eeta.app (prJ ⁻¹ᵁ (U.ι ''ᵁ ⊤))).hom.comp (prJ.app (U.ι ''ᵁ ⊤)).hom))
  let param : ↥(xHFunctionFieldBar M H) := read gv
  let param' : ↥(xHFunctionFieldBar M H) := read gu

  have hpL : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hobt1 := IsAlgClosed.exists_pow_nat_eq (((p : ℕ) : AlgebraicClosure ℚ) ^ e) (by norm_num : 0 < 3)
  obtain ⟨z, hz⟩ := hobt1
  have hz0 : z ≠ 0 := fun h => by rw [h, zero_pow (by norm_num)] at hz; exact pow_ne_zero e hpL hz.symm
  have hzA : z ∈ A := by
    have hint : IsIntegral ↥A z := by
      refine ⟨Polynomial.X ^ 3 - Polynomial.C ((((p : ℕ) : ↥A)) ^ e), Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
      simp [hz]
    have hobt2 := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := AlgebraicClosure ℚ)).mp hint
    obtain ⟨y, hy⟩ := hobt2
    rw [← hy]; exact y.2
  let zA : ↥A := ⟨z, hzA⟩
  have hzAdef : zA = ⟨z, hzA⟩ := rfl
  have hpA : ((p : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]
    simpa using (show ((p : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits from hA)
  have hzA3 : zA ^ 3 = ιA (((p : ℕ) : O) ^ e) := by
    apply Subtype.ext; rw [map_pow, map_natCast]; push_cast; exact hz
  have hzm : zA ∈ IsLocalRing.maximalIdeal ↥A := by
    apply Ideal.IsPrime.mem_of_pow_mem inferInstance 3
    rw [hzA3, map_pow, map_natCast]; exact Ideal.pow_mem_of_mem _ hpA _ he
  have hzAne : zA ≠ 0 := fun h => hz0 (congrArg Subtype.val h)
  have hznu : ¬ IsUnit zA := fun hu => (IsLocalRing.mem_maximalIdeal _).mp hzm hu

  have htube : ∀ (m c : ↥A), m ∈ IsLocalRing.maximalIdeal ↥A → c ∈ IsLocalRing.maximalIdeal ↥A → m * c = ιA (((p : ℕ) : O) ^ e) →
      ∃ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hrat : W.IsRational) (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
        s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) ∧
        barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ ∧
        U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n ∧
        W.evalAt param = (c : AlgebraicClosure ℚ) ∧ W.evalAt param' = (m : AlgebraicClosure ℚ) := by
    intro m c hm hc hmc
    have hobt3 := MvPolynomial.CrossingQuotient.existsUnique_ringHom_comp_algebraMap_eq_and_apply_U_eq_and_apply_V_eq ιA (((p : ℕ) : O) ^ e) m c hmc
    obtain ⟨χ, ⟨hχO, hχu, hχv⟩, -⟩ := hobt3
    have hobt4 := hA1 χ hχO (hχu ▸ hm) (hχv ▸ hc)
    obtain ⟨s, hs1, hs3, hsf⟩ := hobt4
    have hobt5 := hA3.1 s hs1
    obtain ⟨W, hrat, hs2⟩ := hobt5
    have hobt6 := h4 W hrat s hs1 hs2 χ hsf
    obtain ⟨-, -, hev, hev'⟩ := hobt6
    exact ⟨W, hrat, s, hs1, hs2, hs3, by rw [hev, hχv], by rw [hev', hχu]⟩
  have hobt7 := htube (zA ^ 2) zA (Ideal.pow_mem_of_mem _ hzm _ (by norm_num)) hzm (by rw [← pow_succ, hzA3])
  obtain ⟨W₁, hrat₁, s₁, hs1₁, hs2₁, hs3₁, hy₁, hx₁⟩ := hobt7
  have hobt8 := htube zA (zA ^ 2) hzm (Ideal.pow_mem_of_mem _ hzm _ (by norm_num)) (by rw [← pow_succ', hzA3])
  obtain ⟨W₂, hrat₂, s₂, hs1₂, hs2₂, hs3₂, hy₂, hx₂⟩ := hobt8

  have hg : g ≠ 0 := by
    intro h0
    have hobt9 := hyp W₁ hrat₁ s₁ hs1₁ hs2₁ hs3₁
    obtain ⟨-, hmem, hu⟩ := hobt9
    apply hu.ne_zero
    apply Subtype.ext
    show W₁.evalAt g = 0
    rw [h0, ← map_zero (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), AlgebraicCurve.Place.evalAt_algebraMap]

  obtain ⟨O', i1, i2, i3, σ, ιA', hσ, hιinj, hιloc, jO', hjO', hιA'j, htoκ', hsp, rr, ss, hss, hgfr⟩ :=
    ModularCurve.XHDRModelAtP.forall_exists_isDiscreteValuationRing_specializes_and_mul_stalkRead_eq_stalkRead p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n g
  have hobt10 := IsDiscreteValuationRing.exists_irreducible O'
  obtain ⟨ϖ', hϖ'irr⟩ := hobt10
  have hϖ' : IsLocalRing.maximalIdeal O' = Ideal.span {ϖ'} := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖ'irr
  have hcore := ntcore3 p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ O ρO hϖ toκ htoκ jO hjO ιA hιA hιAκ n e he U hxU f hover hfib hpt het hor₁ hor₂ hor₃ hor₄ O' σ ιA' hσ hιinj hιloc jO' hjO' hιA'j htoκ' ϖ' hϖ' hgen hsp g ⟨rr, ss, hss, hgfr⟩
  obtain ⟨B, _, _, _, _, σB, hσB, emb, hemb, W', _, _, _, _, π', hπ', E', hE',
    ι', w₀, hϖB, bu, bv, wu, hbu, hbv, hembv, hembu, hgfrac, S, _, jA, hdesc, hχ, hprime, hGSc⟩ := hcore
  letI : Algebra B ↥(xHFunctionFieldBar M H) := emb.toAlgebra
  obtain ⟨r₀, s₀, hs₀, hgs⟩ := hgfrac
  have hord : ∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), W.IsRational → ∀ (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
      s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
      barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ →
      U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n → W.ord g = 0 :=
    fun W hrat s hs1 hs2 hs3 => (hyp W hrat s hs1 hs2 hs3).1
  have hunit : ∀ P : Ideal B, P.IsPrime → P ≠ ⊥ → σB ϖ' ∉ P →
      (∃ r s : B, s ∉ P ∧ g * algebraMap B ↥(xHFunctionFieldBar M H) s = algebraMap B ↥(xHFunctionFieldBar M H) r) ∧
      (∃ r s : B, s ∉ P ∧ g⁻¹ * algebraMap B ↥(xHFunctionFieldBar M H) s = algebraMap B ↥(xHFunctionFieldBar M H) r) := by
    intro P hP hP0 hϖP
    have hobt11 := hprime P hP hP0 hϖP
    obtain ⟨W, hrat, s, hs1, hs2, hs3, χ, ⟨-, -, -, hfrac⟩, hker⟩ := hobt11
    have h0 : W.ord g = 0 := hord W hrat s hs1 hs2 hs3
    have hgW : g ∈ W.toValuationSubring := AlgebraicCurve.Place.mem_of_ord_nonneg W hg h0.symm.le
    have hgiW : g⁻¹ ∈ W.toValuationSubring :=
      AlgebraicCurve.Place.mem_of_ord_nonneg W (inv_ne_zero hg) (by rw [AlgebraicCurve.Place.ord_inv, h0, neg_zero])
    have hr₀ : emb r₀ ≠ 0 := by
      rw [← hgs]; exact mul_ne_zero hg (fun h => hs₀ (hemb (by rw [h, map_zero])))
    have hgifrac : ∃ r s : B, s ≠ 0 ∧ g⁻¹ * emb s = emb r := by
      refine ⟨s₀, r₀, fun h => hr₀ (by rw [h, map_zero]), ?_⟩
      rw [← hgs, ← mul_assoc, inv_mul_cancel₀ hg, one_mul]
    constructor
    · obtain ⟨r, s', hs', hx⟩ := hfrac g hgW ⟨r₀, s₀, hs₀, hgs⟩
      exact ⟨r, s', fun hmem => hs' ((hker s').mp hmem), hx⟩
    · obtain ⟨r, s', hs', hx⟩ := hfrac g⁻¹ hgiW hgifrac
      exact ⟨r, s', fun hmem => hs' ((hker s').mp hmem), hx⟩
  obtain ⟨w, a, b, nn, k, hab, hmono⟩ :=
    IsLocalRing.exists_units_forall_mul_const_pow_eq_mul_monomial_of_ringEquiv_adicCompletion_uvCrossingModel_of_forall_prime_mem_localization
      (B := B) (K := ↥(xHFunctionFieldBar M H)) hemb π' hπ' E' hE' ι' (σB ϖ') 1 le_rfl w₀ (by rw [pow_one]; exact hϖB) g hg ⟨r₀, s₀, hs₀, hgs⟩ hunit

  have hϖ0 : ϖ' ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_a_field O'
    rw [hϖ', h0, Ideal.span_singleton_eq_bot]
  have hPne : ιA' ϖ' ≠ 0 := fun h => hϖ0 (hιinj (by rw [map_zero]; exact h))
  have hPnu : ¬ IsUnit (ιA' ϖ') := by
    intro hu; haveI := hιloc
    exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ').mpr hϖ' |>.not_isUnit (isUnit_of_map_unit ιA' ϖ' hu)

  have hassoc : ∀ (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hrat : W.IsRational) (s : Spec (CommRingCat.of ↥A) ⟶ (U : Scheme.{0})),
      s ≫ U.ι ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) →
      barPt A ≫ s ≫ U.ι = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫ prJ →
      U.ι.base (s.base (IsLocalRing.closedPoint ↥A)) = (pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1) ≫ 𝔛.comp A hA ρ hρ 0 ≫ bcMap (ΓM M H) hj ρO toκ htoκ).base n →
      ∀ (x y : ↥A), W.evalAt param = (y : AlgebraicClosure ℚ) → W.evalAt param' = (x : AlgebraicClosure ℚ) →
      Associated (ιA' ϖ' ^ k) (x ^ a * y ^ b * ιA' ϖ' ^ nn) := by
    intro W hrat s hs1 hs2 hs3 x y hy hx
    have hobt12 := hχ W hrat s hs1 hs2 hs3
    obtain ⟨χ, ψ, hloc, hcomp, hψ, hev, hfrac⟩ := hobt12
    have hobt13 := hyp W hrat s hs1 hs2 hs3
    obtain ⟨h0, hGA, hGu⟩ := hobt13
    have hgW : g ∈ W.toValuationSubring := AlgebraicCurve.Place.mem_of_ord_nonneg W hg h0.symm.le
    have hobt14 := hfrac g hgW ⟨r₀, s₀, hs₀, hgs⟩
    obtain ⟨r, s', hs', hxr⟩ := hobt14
    have hm := hmono r s' hxr
    let ψ' : UVCrossingModel W' (π' ^ E') →+* S := ψ.comp ι'.symm.toRingHom
    have hψ'ι : ∀ t, ψ' (ι' t) = ψ t := fun t => by
      show ψ (ι'.symm (ι' t)) = _
      rw [RingEquiv.symm_apply_apply]
    have hψB : ∀ bb : B, ψ (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) bb) = jA (χ bb) := fun bb => RingHom.congr_fun hψ bb
    have hVv : ψ' (UVCrossingModel.V (π' ^ E')) = jA (χ bv) := by rw [← hbv, hψ'ι, hψB]
    have hUu : ψ' (UVCrossingModel.U (π' ^ E')) * ψ' wu = jA (χ bu) := by rw [← map_mul, ← hbu, hψ'ι, hψB]
    have hCc : ψ' w₀ * ψ' (UVCrossingModel.const (π' ^ E') π') = jA (ιA' ϖ') := by
      rw [← map_mul, ← hϖB, hψ'ι, hψB]
      exact congrArg jA (RingHom.congr_fun hcomp ϖ')
    have hmS := congrArg ψ' hm
    simp only [map_mul, map_pow, hψ'ι, hψB] at hmS
    let uw : Sˣ := Units.map ψ'.toMonoidHom w
    let uw₀ : Sˣ := Units.map ψ'.toMonoidHom w₀
    let uwu : Sˣ := Units.map ψ'.toMonoidHom wu
    have huw : (uw : S) = ψ' w := rfl
    have huw₀ : (uw₀ : S) = ψ' w₀ := rfl
    have huwu : (uwu : S) = ψ' wu := rfl
    let α : ↥A := χ r * ιA' ϖ' ^ k
    let β : ↥A := χ s' * χ bu ^ a * χ bv ^ b * ιA' ϖ' ^ nn
    have hkey : jA α * (uw₀ ^ nn * uwu ^ a : Sˣ) = jA β * (uw * uw₀ ^ k : Sˣ) := by
      simp only [α, β, map_mul, map_pow, Units.val_mul, Units.val_pow_eq_pow_val, huw, huw₀, huwu, ← hVv, ← hUu, ← hCc]
      linear_combination (ψ' w₀) ^ k * (ψ' w₀) ^ nn * (ψ' wu) ^ a * hmS
    have hkey' : jA α = jA β * ((uw * uw₀ ^ k) * (uw₀ ^ nn * uwu ^ a)⁻¹ : Sˣ) := by
      rw [Units.val_mul, ← mul_assoc, ← hkey, mul_assoc, Units.mul_inv, mul_one]
    have hobt15 := hdesc α β _ hkey'
    obtain ⟨v, hv⟩ := hobt15

    have hpeq : param = emb bv := hembv.symm
    have hpeq' : param' = emb bu := hembu.symm
    have hyA : χ bv = y := by
      apply Subtype.ext; rw [← hy, hpeq]; exact ((hev bv).2).symm
    have hxA : χ bu = x := by
      apply Subtype.ext; rw [← hx, hpeq']; exact ((hev bu).2).symm
    have hG : (⟨W.evalAt g, hGA⟩ : ↥A) * χ s' = χ r := by
      apply Subtype.ext
      show W.evalAt g * ((χ s' : ↥A) : AlgebraicClosure ℚ) = ((χ r : ↥A) : AlgebraicClosure ℚ)
      rw [← (hev s').2, ← (hev r).2, ← AlgebraicCurve.Place.evalAt_mul W hrat hgW (hev s').1, hxr]

    simp only [α, β] at hv
    rw [hyA, hxA] at hv
    refine ⟨hGu.unit * v⁻¹, ?_⟩
    have hs'0 : (χ s' : ↥A) ≠ 0 := hs'
    apply mul_left_cancel₀ hs'0
    rw [Units.val_mul, IsUnit.unit_spec]

    have hvinv : (v : ↥A) * ((v⁻¹ : (↥A)ˣ) : ↥A) = 1 := v.mul_inv
    linear_combination (ιA' ϖ' ^ k * ((v⁻¹ : (↥A)ˣ) : ↥A)) * hG + ((v⁻¹ : (↥A)ˣ) : ↥A) * hv
      + (χ s' * x ^ a * y ^ b * ιA' ϖ' ^ nn) * hvinv

  have hA₁ := hassoc W₁ hrat₁ s₁ hs1₁ hs2₁ hs3₁ (zA ^ 2) zA hy₁ hx₁
  have hA₂ := hassoc W₂ hrat₂ s₂ hs1₂ hs2₂ hs3₂ zA (zA ^ 2) hy₂ hx₂
  have hab0 : a = 0 ∧ b = 0 := by
    have h12 : Associated ((zA ^ 2) ^ a * zA ^ b * ιA' ϖ' ^ nn) (zA ^ a * (zA ^ 2) ^ b * ιA' ϖ' ^ nn) := hA₁.symm.trans hA₂
    have hcommon : (zA ^ 2) ^ a * zA ^ b * ιA' ϖ' ^ nn = (zA ^ (a + b) * ιA' ϖ' ^ nn) * zA ^ a := by ring
    have hcommon' : zA ^ a * (zA ^ 2) ^ b * ιA' ϖ' ^ nn = (zA ^ (a + b) * ιA' ϖ' ^ nn) * zA ^ b := by ring
    rw [hcommon, hcommon'] at h12
    have hne : zA ^ (a + b) * ιA' ϖ' ^ nn ≠ 0 := mul_ne_zero (pow_ne_zero _ hzAne) (pow_ne_zero _ hPne)
    have hab' : Associated (zA ^ a) (zA ^ b) := Associated.of_mul_left h12 (Associated.refl _) hne
    rcases hab with ha | hb
    · subst ha
      refine ⟨rfl, ?_⟩
      by_contra hb
      rw [pow_zero] at hab'
      exact hznu (isUnit_of_dvd_one (dvd_trans (dvd_pow_self zA hb) hab'.symm.dvd))
    · subst hb
      refine ⟨?_, rfl⟩
      by_contra ha
      rw [pow_zero] at hab'
      exact hznu (isUnit_of_dvd_one (dvd_trans (dvd_pow_self zA ha) hab'.dvd))
  obtain ⟨ha0, hb0⟩ := hab0
  have hkn : nn = k := by
    have h1' : Associated (ιA' ϖ' ^ k) (ιA' ϖ' ^ nn) := by simpa [ha0, hb0] using hA₁
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    ·
      have : Associated (ιA' ϖ' ^ nn * ιA' ϖ' ^ (k - nn)) (ιA' ϖ' ^ nn * 1) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one]; exact h1'
      have h2 := Associated.of_mul_left this (Associated.refl _) (pow_ne_zero _ hPne)
      exact hPnu (isUnit_of_dvd_one (dvd_trans (dvd_pow_self _ (Nat.sub_ne_zero_of_lt hlt)) h2.dvd))
    · have : Associated (ιA' ϖ' ^ k * 1) (ιA' ϖ' ^ k * ιA' ϖ' ^ (nn - k)) := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' hgt.le]; exact h1'
      have h2 := Associated.of_mul_left this (Associated.refl _) (pow_ne_zero _ hPne)
      exact hPnu (isUnit_of_dvd_one (dvd_trans (dvd_pow_self _ (Nat.sub_ne_zero_of_lt hgt)) h2.symm.dvd))

  haveI : IsDomain (UVCrossingModel W' (π' ^ E')) := (ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow π' hπ' E' hE').1
  haveI : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal B) B) := ι'.injective.isDomain ι'.toRingHom
  have hm0 := hmono r₀ s₀ hgs
  simp only [ha0, hb0, hkn, pow_zero, mul_one] at hm0

  have hrs : algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) r₀ = algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) s₀ * ((Units.map ι'.symm.toRingHom.toMonoidHom w : (AdicCompletion (IsLocalRing.maximalIdeal B) B)ˣ) : AdicCompletion (IsLocalRing.maximalIdeal B) B) := by
    apply ι'.injective
    have hcE : UVCrossingModel.const (π' ^ E') π' ^ E' ∈ nonZeroDivisors (UVCrossingModel W' (π' ^ E')) := by
      rw [← ModularCurve.UVCrossingModel.constHom_apply, ← map_pow]
      exact ModularCurve.UVCrossingModel.const_mem_nonZeroDivisors (pow_mem (mem_nonZeroDivisors_of_ne_zero hπ'.ne_zero) E')
    have hc1 : UVCrossingModel.const (π' ^ E') π' ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by omega)] at hcE
      exact nonZeroDivisors.ne_zero hcE rfl
    have hc0 : UVCrossingModel.const (π' ^ E') π' ^ k ≠ 0 := pow_ne_zero _ hc1
    apply mul_right_cancel₀ hc0
    rw [hm0, map_mul, mul_assoc]
    congr 1
    show _ = ι' (ι'.symm w) * _
    rw [RingEquiv.apply_symm_apply]
  have hobt16 := IsLocalRing.exists_units_eq_mul_of_algebraMap_adicCompletion_eq_mul_units r₀ s₀ hs₀ _ hrs
  obtain ⟨t, ht⟩ := hobt16
  have hgt : g = emb t := by
    have hs0' : emb s₀ ≠ 0 := fun h => hs₀ (hemb (by rw [h, map_zero]))
    apply mul_right_cancel₀ hs0'
    rw [hgs, ht, map_mul, mul_comm]
  have hobt17 := hGSc (t : B) (Units.isUnit t)
  obtain ⟨U', hxA, hgenA, γ, hγ, hread⟩ := hobt17
  have hUSO := ModularCurve.XHDRModelAtP.ord_placeOn_germ_eq_zero_of_isUnit_section p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ n U' hxA γ hγ
  exact ⟨U', hxA, hgenA, γ, hγ, by rw [hread, ← hgt], hUSO.1, hUSO.2⟩

end S_ModularCurve_XHDRModelAtP_exists_isUnit_and_read_eq_and_ord_placeOn_eq_zero_of_forall_ord_eq_zero_of_forall_isUnit_evalAt_of_chart_of_residue_surjective
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_isUnit_and_read_eq_and_ord_placeOn_eq_zero_of_forall_ord_eq_zero_of_forall_isUnit_evalAt_of_chart_of_residue_surjective (solution)
