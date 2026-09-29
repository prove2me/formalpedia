-- Prove2me | solution 1 for ModularCurve.FullLevel.ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/5d716ae8-77fc-591a-84f8-73cc4cc7c588

import Mathlib
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_comp
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Theorems.Thm_ModularCurve_laurentBaseChange_mono
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index
import Theorems.Thm_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_gamma0_sq_mul_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_xH_of_eq_two
import Theorems.Thm_ModularCurve_ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul_of_eq_two
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH_of_eq_two
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.coe_jqNGen CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply"
p2m_attr_erase "simp" "ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ"
p2m_attr_erase "simp" "ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

namespace HCPAux

open AlgebraicCurve ModularCurve AlgebraicCurve.TwoChartIntegralModel

set_option synthInstance.maxHeartbeats 1600000 in

theorem isIntegral_inclusion
    (L : Type) [Field L]
    (K : IntermediateField L (LaurentSeries L)) (K₁ : IntermediateField L (LaurentSeries L)) (hle : K₁ ≤ K)
    (j : ↥K) (hjK₁ : ((j : LaurentSeries L)) ∈ K₁)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K) :
    (IntermediateField.inclusion hle).toRingHom.IsIntegral := by
  classical
  haveI := hFD
  haveI : Algebra.IsIntegral ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsIntegral.of_finite _ _
  set E := IntermediateField.adjoin L ({j} : Set ↥K) with hE
  have hEK₁ : ∀ x : ↥E, (((x : ↥K) : LaurentSeries L)) ∈ K₁ := by
    have hle' : E ≤ IntermediateField.comap K.val K₁ := by
      rw [hE, IntermediateField.adjoin_le_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hjK₁
    intro x
    exact hle' x.2
  let ψ : ↥E →+* ↥K₁ :=
    { toFun := fun x => ⟨((x : ↥K) : LaurentSeries L), hEK₁ x⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have hψ : (IntermediateField.inclusion hle).toRingHom.comp ψ = algebraMap ↥E ↥K := by
    ext x
    rfl
  intro y
  have hy : IsIntegral ↥E y := Algebra.IsIntegral.isIntegral y
  refine ⟨(minpoly ↥E y).map ψ, (minpoly.monic hy).map ψ, ?_⟩
  rw [Polynomial.eval₂_map, hψ, ← Polynomial.aeval_def, minpoly.aeval]

theorem gamma0_le_of_dvd {M N : ℕ} (h : M ∣ N) : CongruenceSubgroup.Gamma0 N ≤ CongruenceSubgroup.Gamma0 M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hγ ⊢
  have := (ZMod.castHom h (ZMod M)).congr_arg hγ
  simpa using this

theorem exists_ringHom_chartAlgInf
    (R : Type) [CommRing R] (F F' : Type) [Field F] [Field F'] [Algebra R F] [Algebra R F']
    (φ : F →ₐ[R] F') (j : F) (j' : F') (hj : φ j = j') :
    ∃ ι : ↥(chartAlgInf R F j) →+* ↥(chartAlgInf R F' j'),
      (∀ x, ((ι x : ↥(chartAlgInf R F' j')) : F') = φ x) ∧ (∀ r : R, ι (algebraMap R _ r) = algebraMap R _ r) ∧
      ι.IsIntegral := by
  classical
  have hj' : φ j⁻¹ = j'⁻¹ := by rw [map_inv₀, hj]
  have hadj : ∀ x ∈ Algebra.adjoin R ({j⁻¹} : Set F), φ x ∈ Algebra.adjoin R ({j'⁻¹} : Set F') := by
    intro x hx
    have : (Algebra.adjoin R ({j⁻¹} : Set F)).map φ ≤ Algebra.adjoin R ({j'⁻¹} : Set F') := by
      rw [AlgHom.map_adjoin, Set.image_singleton, hj']
    exact this ⟨x, hx, rfl⟩
  let ψ : ↥(Algebra.adjoin R ({j⁻¹} : Set F)) →+* ↥(Algebra.adjoin R ({j'⁻¹} : Set F')) :=
    (φ.toRingHom.comp (Algebra.adjoin R ({j⁻¹} : Set F)).val.toRingHom).codRestrict
      (Algebra.adjoin R ({j'⁻¹} : Set F')).toSubring (fun x => hadj x x.2)
  have hint : ∀ x : F, IsIntegral ↥(Algebra.adjoin R ({j⁻¹} : Set F)) x →
      IsIntegral ↥(Algebra.adjoin R ({j'⁻¹} : Set F')) (φ x) := by
    intro x hx
    exact hx.map_of_comp_eq ψ φ.toRingHom (by ext y; rfl)
  let ι : ↥(chartAlgInf R F j) →+* ↥(chartAlgInf R F' j') :=
    { toFun := fun x => ⟨φ (x : F), (mem_chartAlg_iff R F').mpr (hint x ((mem_chartAlg_iff R F).mp x.2))⟩,
      map_one' := Subtype.ext (by simp),
      map_mul' := fun x y => Subtype.ext (by simp),
      map_zero' := Subtype.ext (by simp),
      map_add' := fun x y => Subtype.ext (by simp) }
  have hιalg : ∀ r : R, ι (algebraMap R _ r) = algebraMap R _ r := by
    intro r
    apply Subtype.ext
    show φ ((algebraMap R ↥(chartAlgInf R F j) r : ↥(chartAlgInf R F j)) : F) = ((algebraMap R ↥(chartAlgInf R F' j') r : ↥(chartAlgInf R F' j')) : F')
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, φ.commutes]
  refine ⟨ι, fun x => rfl, hιalg, ?_⟩

  intro b
  have hb : IsIntegral ↥(Algebra.adjoin R ({j'⁻¹} : Set F')) (b : F') := (mem_chartAlg_iff R F').mp b.2
  obtain ⟨p₁, hp₁m, hp₁b⟩ := hb

  set θ : ↥(chartAlgInf R F j) →+* F' := (chartAlgInf R F' j').val.toRingHom.comp ι with hθ
  have hθ' : θ = φ.toRingHom.comp (chartAlgInf R F j).val.toRingHom := by
    rw [hθ]; ext x; rfl

  have hadjle : Algebra.adjoin R ({j⁻¹} : Set F) ≤ chartAlgInf R F j := by
    intro x hx
    exact (mem_chartAlg_iff R F).mpr (isIntegral_algebraMap (A := F) (x := (⟨x, hx⟩ : ↥(Algebra.adjoin R ({j⁻¹} : Set F)))))

  have hlifts : p₁.map (Algebra.adjoin R ({j'⁻¹} : Set F')).val.toRingHom ∈ Polynomial.lifts θ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    have hc := (p₁.coeff n).2
    have : ((p₁.coeff n : ↥(Algebra.adjoin R ({j'⁻¹} : Set F'))) : F') ∈ (Algebra.adjoin R ({j⁻¹} : Set F)).map φ := by
      rw [AlgHom.map_adjoin, Set.image_singleton, hj']; exact hc
    obtain ⟨x, hx, hxc⟩ := this
    refine ⟨⟨x, hadjle hx⟩, ?_⟩
    rw [hθ']
    exact hxc
  obtain ⟨p, hpmap, -, hpmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts (hp₁m.map _)
  refine ⟨p, hpmonic, ?_⟩
  apply Subtype.ext
  have h1 : (((Polynomial.eval₂ ι b p) : ↥(chartAlgInf R F' j')) : F') = Polynomial.eval₂ θ (b : F') p := by
    rw [hθ]
    exact Polynomial.hom_eval₂ p ι (chartAlgInf R F' j').val.toRingHom b
  rw [h1, Polynomial.eval₂_eq_eval_map, hpmap, Polynomial.eval_map]
  show Polynomial.eval₂ (algebraMap ↥(Algebra.adjoin R ({j'⁻¹} : Set F')) F') (b : F') p₁ = ((0 : ↥(chartAlgInf R F' j')) : F')
  rw [hp₁b]; rfl

theorem map_mem_nonunits_of_mem_nonunits_comap
    {K L : Type} [Field K] [Field L] (W : ValuationSubring L) (f : K →+* L) (x : K)
    (hx : x ∈ (W.comap f).nonunits) : f x ∈ W.nonunits := by
  have hxW : x ∈ W.comap f := ValuationSubring.nonunits_subset hx
  have hfx : f x ∈ W := ValuationSubring.mem_comap.mp hxW
  rw [show x = ((⟨x, hxW⟩ : ↥(W.comap f)) : K) from rfl, ValuationSubring.coe_mem_nonunits_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
  rw [show f x = ((⟨f x, hfx⟩ : ↥W) : L) from rfl, ValuationSubring.coe_mem_nonunits_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hx
  obtain ⟨u, hu⟩ := hu
  have hval : (((u⁻¹ : (↥W)ˣ) : ↥W) : L) * f x = 1 := by
    have := congrArg (fun z : ↥W => (z : L)) (u.inv_mul)
    rw [hu] at this
    simpa using this
  have hx0 : f x ≠ 0 := fun h => by rw [h, mul_zero] at hval; exact zero_ne_one hval
  have hinv : (f x)⁻¹ = (((u⁻¹ : (↥W)ˣ) : ↥W) : L) := (eq_inv_of_mul_eq_one_left hval).symm
  have hinvW : (f x)⁻¹ ∈ W := hinv ▸ ((u⁻¹ : (↥W)ˣ) : ↥W).2
  have hxinvW : x⁻¹ ∈ W.comap f := by
    rw [ValuationSubring.mem_comap, map_inv₀]; exact hinvW
  have hxK0 : x ≠ 0 := fun h => hx0 (by rw [h, map_zero])
  exact isUnit_iff_exists_inv.mpr ⟨⟨x⁻¹, hxinvW⟩, Subtype.ext (mul_inv_cancel₀ hxK0)⟩

end HCPAux

open AlgebraicCurve ModularCurve AlgebraicCurve.TwoChartIntegralModel in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle₀ : K₀ ≤ K)
    (w : AlgebraicCurve.Place L ↥K)
    (hw : 0 < w.ord ((AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K) j :
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) : ↥K))
    (y : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [y.IsMaximal]
    (hyϖ : algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ ∈ y)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y)
    (hwy : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), 0 < w.ord (b : ↥K) → b ∈ y) :
    AlgebraicCurve.Place.ramificationIndexAlong (IntermediateField.inclusion hle₀) w = 1 := by
  classical

  set K₂ : IntermediateField L (LaurentSeries L) :=
    ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q ^ 2 * M'))) with hK₂
  have hle₂ : K₂ ≤ K := by
    rw [hK₂, hK]
    exact ModularCurve.laurentBaseChange_mono L (ModularCurve.qExpFunctionFieldC_mono ℚ (CohCarrier.GammaH_le_Gamma0 _))
  have hle₀₂ : K₀ ≤ K₂ := by
    rw [hK₀, hK₂]
    exact ModularCurve.laurentBaseChange_mono L
      (ModularCurve.qExpFunctionFieldC_mono ℚ (HCPAux.gamma0_le_of_dvd (Dvd.intro_left (q ^ 2) rfl)))
  letI algAK₂ : Algebra A ↥K₂ := ((algebraMap L ↥K₂).comp (algebraMap A L)).toAlgebra
  haveI istAK₂ : IsScalarTower A L ↥K₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  haveI : (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')).FiniteIndex := ⟨by
    rw [CohCarrier.index_gammaH_eq_index_gamma0_mul_index]
    exact mul_ne_zero Subgroup.FiniteIndex.index_ne_zero Subgroup.index_ne_zero_of_finite⟩

  have hT : ModularGroup.T ∈ CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :=
    ModularCurve.translation_mem_GammaH _ _
  have hT₂ : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (q ^ 2 * M') := by
    rw [← CohCarrier.GammaH_top]; exact ModularCurve.translation_mem_GammaH _ _
  have hjqK₂ : ModularCurve.coeffEmb L ModularCurve.jq ∈ K₂ := by
    rw [hK₂]
    refine ModularCurve.coeffEmb_mem_laurentBaseChange L ?_
    rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    exact ModularCurve.modularFunctionField_le_full _ (ModularCurve.jq_mem _)
  have hjqK₀ : ModularCurve.coeffEmb L ModularCurve.jq ∈ K₀ := by
    rw [hK₀]
    refine ModularCurve.coeffEmb_mem_laurentBaseChange L ?_
    rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    exact ModularCurve.modularFunctionField_le_full _ (ModularCurve.jq_mem _)
  have hjK₂ : ((j : ↥K) : LaurentSeries L) ∈ K₂ := hj ▸ hjqK₂
  have hjK₀ : ((j : ↥K) : LaurentSeries L) ∈ K₀ := hj ▸ hjqK₀
  let j₂ : ↥K₂ := ⟨(j : LaurentSeries L), hjK₂⟩
  have hj₂ : ((j₂ : ↥K₂) : LaurentSeries L) = ModularCurve.coeffEmb L ModularCurve.jq := hj
  have hj0 : ((j : ↥K) : LaurentSeries L) ≠ 0 := fun h =>
    (Fact.out : j ≠ 0) (Subtype.ext (by rw [h]; rfl))
  haveI : Fact (j₂ ≠ 0) := ⟨fun h => hj0 (congrArg (fun z : ↥K₂ => (z : LaurentSeries L)) h)⟩
  have hj₂K₀ : ((j₂ : ↥K₂) : LaurentSeries L) ∈ K₀ := hjK₀

  haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) hT L K hK j hj
  haveI hFD₂ : FiniteDimensional ↥(IntermediateField.adjoin L ({j₂} : Set ↥K₂)) ↥K₂ :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma0 (q ^ 2 * M')) hT₂ L K₂ hK₂ j₂ hj₂

  let ι₂ : ↥K₂ →ₐ[L] ↥K := IntermediateField.inclusion hle₂
  have hint₂ : ι₂.toRingHom.IsIntegral := HCPAux.isIntegral_inclusion L K K₂ hle₂ j hjK₂ hFD
  have hint₀₂ : (IntermediateField.inclusion hle₀₂).toRingHom.IsIntegral :=
    HCPAux.isIntegral_inclusion L K₂ K₀ hle₀₂ j₂ hj₂K₀ hFD₂
  have hint₀ : (IntermediateField.inclusion hle₀).toRingHom.IsIntegral := HCPAux.isIntegral_inclusion L K K₀ hle₀ j hjK₀ hFD
  have hcomp : ι₂.comp (IntermediateField.inclusion hle₀₂) = IntermediateField.inclusion hle₀ := by
    ext x; rfl
  have hint₀' : (ι₂.comp (IntermediateField.inclusion hle₀₂)).toRingHom.IsIntegral := by rw [hcomp]; exact hint₀

  let W₂ : ValuationSubring ↥K₂ := W₀.comap ι₂.toRingHom
  have hW₂ : ∀ f : ↥K₂, f ∈ W₂ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) := by
    intro f
    rw [ValuationSubring.mem_comap]
    exact hW₀ (ι₂ f)

  let w₂ : AlgebraicCurve.Place L ↥K₂ := w.restrictAlong ι₂ hint₂
  have he₂ : 1 ≤ AlgebraicCurve.Place.ramificationIndexAlong ι₂ w :=
    AlgebraicCurve.Place.one_le_ramificationIndexAlong ι₂ hint₂ w
  have hordpos : ∀ f : ↥K₂, 0 < w₂.ord f ↔ 0 < w.ord (ι₂ f) := by
    intro f
    rw [AlgebraicCurve.Place.ord_restrictAlong ι₂ hint₂ w f]
    have he : (0 : ℤ) < (AlgebraicCurve.Place.ramificationIndexAlong ι₂ w : ℤ) := by exact_mod_cast he₂
    constructor
    · intro h; exact mul_pos he h
    · intro h; exact (mul_pos_iff_of_pos_left he).mp h

  obtain ⟨ιB, hιB, hιBalg, hιBint⟩ := HCPAux.exists_ringHom_chartAlgInf A ↥K₂ ↥K (ι₂.restrictScalars A) (j₂ : ↥K₂) (j : ↥K)
    (Subtype.ext rfl)
  letI algB : Algebra ↥(chartAlgInf A (↥K₂) j₂) ↥(chartAlgInf A (↥K) j) := ιB.toAlgebra
  haveI : Algebra.IsIntegral ↥(chartAlgInf A (↥K₂) j₂) ↥(chartAlgInf A (↥K) j) := ⟨hιBint⟩
  let y₂ : Ideal ↥(chartAlgInf A (↥K₂) j₂) := y.comap ιB
  haveI hy₂max : y₂.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ↥(chartAlgInf A (↥K₂) j₂)) y
  have hcoeB : ∀ b : ↥(chartAlgInf A (↥K₂) j₂), ((ιB b : ↥(chartAlgInf A (↥K) j)) : ↥K) = ι₂ (b : ↥K₂) := fun b => hιB b

  have hyϖ₂ : algebraMap A ↥(chartAlgInf A (↥K₂) j₂) ϖ ∈ y₂ := by
    show ιB (algebraMap A _ ϖ) ∈ y
    rw [hιBalg]; exact hyϖ
  have hz₀₂ : ∀ b : ↥(chartAlgInf A (↥K₂) j₂), (b : ↥K₂) ∈ W₂.nonunits → b ∈ y₂ := by
    intro b hb
    show ιB b ∈ y
    apply hz₀
    rw [hcoeB]
    exact HCPAux.map_mem_nonunits_of_mem_nonunits_comap W₀ ι₂.toRingHom (b : ↥K₂) hb
  have hwy₂ : ∀ b : ↥(chartAlgInf A (↥K₂) j₂), 0 < w₂.ord (b : ↥K₂) → b ∈ y₂ := by
    intro b hb
    show ιB b ∈ y
    apply hwy
    rw [hcoeB]
    exact (hordpos _).mp hb
  have hw₂ : 0 < w₂.ord ((AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K₂) j₂ :
      ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₂) j₂)) : ↥K₂) := by
    rw [hordpos]
    have : ι₂ ((jInvChartInf A (↥K₂) j₂ : ↥(chartAlgInf A (↥K₂) j₂)) : ↥K₂) =
        ((jInvChartInf A (↥K) j : ↥(chartAlgInf A (↥K) j)) : ↥K) := by
      rw [coe_jInvChartInf, coe_jInvChartInf, map_inv₀]
      congr 1
    rw [this]; exact hw

  have hA := ModularCurve.FullLevel.ramificationIndexAlong_inclusion_gamma0_sq_mul_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_xH_of_eq_two
    q hq2 M' hqM' L K hK A hAq j hj ϖ hϖ W₀ hW₀ K₂ hK₂ hle₂ w hw y hyϖ hz₀ hwy
  have hB := ModularCurve.ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jInvChartInf_pos_of_forall_mem_nonunits_gauss_gamma0_sq_mul_of_eq_two
    q hq2 M' hqM' L K₂ hK₂ A hAq j₂ hj₂ ϖ hϖ W₂ hW₂ K₀ hK₀ hle₀₂ w₂ hw₂ y₂ hyϖ₂ hz₀₂ hwy₂

  have hc := AlgebraicCurve.Place.ramificationIndexAlong_comp (IntermediateField.inclusion hle₀₂) ι₂ hint₀₂ hint₂ hint₀' w
  have hA' : AlgebraicCurve.Place.ramificationIndexAlong ι₂ w = 1 := hA
  have hB' : AlgebraicCurve.Place.ramificationIndexAlong (IntermediateField.inclusion hle₀₂) w₂ = 1 := hB
  have h2 : AlgebraicCurve.Place.ramificationIndexAlong ι₂ w *
      AlgebraicCurve.Place.ramificationIndexAlong (IntermediateField.inclusion hle₀₂) w₂ = 1 := by
    rw [hA', hB']
  exact (congrArg (fun φ : ↥K₀ →ₐ[L] ↥K => AlgebraicCurve.Place.ramificationIndexAlong φ w) hcomp).symm.trans
    (hc.trans h2)

end S_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH_of_eq_two (solution)
