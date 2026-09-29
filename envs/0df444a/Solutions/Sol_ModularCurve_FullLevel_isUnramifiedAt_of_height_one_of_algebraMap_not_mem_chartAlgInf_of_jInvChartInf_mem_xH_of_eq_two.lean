-- Prove2me | solution 1 for ModularCurve.FullLevel.isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/add88611-0af6-5ffd-a81c-b17ca40b1743

import Theorems.Thm_Algebra_isUnramifiedAt_of_height_eq_one_of_not_mem_of_ramificationIndexAlong_eq_one_of_centre
import Theorems.Thm_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH_of_eq_two
import Theorems.Thm_ModularCurve_FullLevel_ramificationIndexAlong_inclusion_eq_one_of_ord_eq_zero_of_ord_sub_eq_zero_xH_levelH_of_eq_two
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isFractionRing_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finiteType_chartAlgFin_and_chartAlgInf
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_ModularCurve_X1
import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_two
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms"
p2m_attr_erase "instance" "ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Pic.baseChange_mk"
p2m_attr_erase "simp" "AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.LevelN.coe_jGen PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_empty TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.coe_jqNGen CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

open AlgebraicCurve.TwoChartIntegralModel

namespace O6Aux

open scoped MatrixGroups

scoped instance gammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : (CohCarrier.GammaH M H).FiniteIndex := by
  refine @Subgroup.finiteIndex_of_le _ _ (CongruenceSubgroup.Gamma1 M) _ inferInstance ?_
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have h0 : A ∈ CongruenceSubgroup.Gamma0 M := CongruenceSubgroup.Gamma1_in_Gamma0 M hA
  refine ⟨h0, ?_⟩
  have h1 := ((CongruenceSubgroup.Gamma1_mem M A).mp hA).2.1
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact h1
  rw [this]; exact H.one_mem

end O6Aux
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_two.O6Aux"

theorem germ_mem_maximalIdeal_iff_of_chart'
    {A S : Type} [CommRing A] [CommRing S] [Algebra A S] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of A)) (ι : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A S))) (q : ↥(Spec (CommRingCat.of S))) (a : A) :
    (X.presheaf.germ ⊤ (ι.base q) trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk (ι.base q)) ↔
      algebraMap A S a ∈ q.asIdeal := by
  have key : (ι.stalkMap q).hom ((X.presheaf.germ ⊤ (ι.base q) trivial).hom
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a))) =
      ((Spec (CommRingCat.of S)).presheaf.germ ⊤ q trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (algebraMap A S a)) := by
    erw [Scheme.Hom.germ_stalkMap_apply ι ⊤ q trivial]
    congr 1
    show ((f.appTop ≫ ι.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = _
    rw [← Scheme.Hom.comp_appTop, hι]
    show ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap A S))).appTop).hom a = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff (ι.stalkMap q).hom, key,
    ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
  letI : Algebra S ((Spec (CommRingCat.of S)).presheaf.stalk q) :=
    AlgebraicGeometry.StructureSheaf.stalkAlgebra (R := S) q
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of S)).presheaf.stalk q) q.asIdeal :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk S q
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff ((Spec (CommRingCat.of S)).presheaf.stalk q) q.asIdeal (algebraMap A S a)

set_option maxHeartbeats 32000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)

    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))

    [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf A (↥K) j))
    (hy : (AlgebraicCurve.TwoChartIntegralModel.ιInf A (↥K) j).base y = z)
    (hmax : y.asIdeal.IsMaximal)

    (hcusp : AlgebraicCurve.TwoChartIntegralModel.jInvChartInf A (↥K) j ∈ y.asIdeal)
    (hz₀ : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j), (b : ↥K) ∈ W₀.nonunits → b ∈ y.asIdeal)

    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle₀ : K₀ ≤ K)
    [Algebra A ↥K₀] [IsScalarTower A L ↥K₀]
    (j₀ : ↥K₀) (hj₀ : ((j₀ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j₀ ≠ 0)]
    (ι : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀) →+* ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j))
    (hι : ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀), ((ι b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) : ↥K) = IntermediateField.inclusion hle₀ (b : ↥K₀)) :
    letI : Algebra ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) := ι.toAlgebra
    ∀ (𝔔 : Ideal ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j)) [𝔔.IsPrime], 𝔔 ≤ y.asIdeal → 𝔔.height = 1 →
      algebraMap A ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K) j) ϖ ∉ 𝔔 → Algebra.IsUnramifiedAt ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf A (↥K₀) j₀) 𝔔 := by
  intro 𝔔 _inst h𝔔y hQ1 hϖQ
  classical

  letI algBB : Algebra ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) := ι.toAlgebra
  set φK : ↥K₀ →ₐ[L] ↥K := IntermediateField.inclusion hle₀ with hφKdef

  haveI : IsIntegrallyClosed ↥(chartAlgInf A (↥K) j) := isIntegrallyClosed_chartAlg A (↥K) _
  haveI : IsIntegrallyClosed ↥(chartAlgInf A (↥K₀) j₀) := isIntegrallyClosed_chartAlg A (↥K₀) _

  have hT : ModularGroup.T ∈ CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') :=
    ModularCurve.translation_mem_GammaH _ _
  have hT₀ : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 M' := by
    rw [← CohCarrier.GammaH_top]; exact ModularCurve.translation_mem_GammaH _ _
  haveI hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) hT L K hK j hj
  haveI hFD₀ : FiniteDimensional ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
      (CongruenceSubgroup.Gamma0 M') hT₀ L K₀ hK₀ j₀ hj₀
  haveI hAlg : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K := Algebra.IsAlgebraic.of_finite _ _
  haveI hAlg₀ : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ := Algebra.IsAlgebraic.of_finite _ _
  haveI hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hsep₀ : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j₀} : Set ↥K₀)) ↥K₀ :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have htj : Transcendental A j := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  have htj₀ : Transcendental A j₀ := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K₀ A j₀ hj₀
  have hadj : IntermediateField.adjoin L ({j⁻¹} : Set ↥K) = IntermediateField.adjoin L ({j} : Set ↥K) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self L j)
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have := inv_mem (IntermediateField.mem_adjoin_simple_self L j⁻¹)
      rwa [inv_inv] at this
  have hadj₀ : IntermediateField.adjoin L ({j₀⁻¹} : Set ↥K₀) = IntermediateField.adjoin L ({j₀} : Set ↥K₀) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self L j₀)
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have := inv_mem (IntermediateField.mem_adjoin_simple_self L j₀⁻¹)
      rwa [inv_inv] at this
  haveI hAlgInv : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j⁻¹} : Set ↥K)) ↥K := by rw [hadj]; exact hAlg
  haveI hAlgInv₀ : Algebra.IsAlgebraic ↥(IntermediateField.adjoin L ({j₀⁻¹} : Set ↥K₀)) ↥K₀ := by rw [hadj₀]; exact hAlg₀
  haveI : IsFractionRing ↥(chartAlgInf A (↥K) j) ↥K := isFractionRing_chartAlg A L (↥K) _
  haveI : IsFractionRing ↥(chartAlgInf A (↥K₀) j₀) ↥K₀ := isFractionRing_chartAlg A L (↥K₀) _
  haveI : IsNoetherianRing ↥(chartAlgInf A (↥K₀) j₀) := by
    haveI := (finiteType_chartAlgFin_and_chartAlgInf A L (↥K₀) j₀ htj₀ hFD₀ hsep₀).2
    exact Algebra.FiniteType.isNoetherianRing A _

  have hιj : ι (jInvChartInf A (↥K₀) j₀) = jInvChartInf A (↥K) j := by
    apply Subtype.ext
    rw [hι]
    apply Subtype.ext
    show ((jInvChartInf A (↥K₀) j₀ : ↥K₀) : LaurentSeries L) = ((jInvChartInf A (↥K) j : ↥K) : LaurentSeries L)
    rw [coe_jInvChartInf, coe_jInvChartInf]
    have h1 : (((j₀⁻¹ : ↥K₀)) : LaurentSeries L) = ((j₀ : ↥K₀) : LaurentSeries L)⁻¹ := by simp
    have h2 : (((j⁻¹ : ↥K)) : LaurentSeries L) = ((j : ↥K) : LaurentSeries L)⁻¹ := by simp
    rw [h1, h2, hj₀, hj]
  haveI : IsScalarTower A ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    symm
    apply Subtype.ext
    show ((ι (algebraMap A ↥(chartAlgInf A (↥K₀) j₀) a) : ↥(chartAlgInf A (↥K) j)) : ↥K) = (algebraMap A ↥(chartAlgInf A (↥K) j) a : ↥K)
    rw [hι]
    apply Subtype.ext
    show ((algebraMap A ↥K₀ a : ↥K₀) : LaurentSeries L) = ((algebraMap A ↥K a : ↥K) : LaurentSeries L)
    rw [IsScalarTower.algebraMap_apply A L ↥K₀, IsScalarTower.algebraMap_apply A L ↥K]
    rfl
  haveI : Module.Finite ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) := by
    letI algP : Algebra (Polynomial A) ↥(chartAlgInf A (↥K) j) := (polynomialToChartInf A (↥K) j).toRingHom.toAlgebra
    letI algP₀ : Algebra (Polynomial A) ↥(chartAlgInf A (↥K₀) j₀) := (polynomialToChartInf A (↥K₀) j₀).toRingHom.toAlgebra
    haveI hfinP : Module.Finite (Polynomial A) ↥(chartAlgInf A (↥K) j) :=
      (finite_polynomial_chartAlgFin_and_chartAlgInf A L (↥K) j htj hFD hsep).2
    have hcomp : ι.comp (polynomialToChartInf A (↥K₀) j₀).toRingHom = (polynomialToChartInf A (↥K) j).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        show ι (polynomialToChartInf A (↥K₀) j₀ (Polynomial.C a)) = polynomialToChartInf A (↥K) j (Polynomial.C a)
        rw [Polynomial.C_eq_algebraMap, AlgHom.commutes, AlgHom.commutes]
        exact (IsScalarTower.algebraMap_apply A ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) a).symm
      · show ι (polynomialToChartInf A (↥K₀) j₀ Polynomial.X) = polynomialToChartInf A (↥K) j Polynomial.X
        rw [polynomialToChartInf_X, polynomialToChartInf_X, hιj]
    haveI : IsScalarTower (Polynomial A) ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) := by
      apply IsScalarTower.of_algebraMap_eq
      intro p
      show polynomialToChartInf A (↥K) j p = ι (polynomialToChartInf A (↥K₀) j₀ p)
      exact (congrArg (fun g : Polynomial A →+* ↥(chartAlgInf A (↥K) j) => g p) hcomp).symm
    exact Module.Finite.of_restrictScalars_finite (Polynomial A) _ _
  have hιK : ∀ x : ↥(chartAlgInf A (↥K₀) j₀),
      algebraMap ↥(chartAlgInf A (↥K) j) ↥K (algebraMap ↥(chartAlgInf A (↥K₀) j₀) ↥(chartAlgInf A (↥K) j) x) =
        φK (algebraMap ↥(chartAlgInf A (↥K₀) j₀) ↥K₀ x) := fun x => hι x
  have hint : φK.toRingHom.IsIntegral := by

    set R : IntermediateField L ↥K := IntermediateField.map φK ⊤ with hRdef
    have hjR : j ∈ R := by
      rw [hRdef, IntermediateField.mem_map]
      refine ⟨j₀, IntermediateField.mem_top, ?_⟩
      apply Subtype.ext
      show ((j₀ : ↥K₀) : LaurentSeries L) = ((j : ↥K) : LaurentSeries L)
      rw [hj₀, hj]
    have hER : IntermediateField.adjoin L ({j} : Set ↥K) ≤ R := IntermediateField.adjoin_le_iff.mpr (by
      intro x hx; rw [Set.mem_singleton_iff.mp hx]; exact hjR)

    letI algER : Algebra ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥R := (IntermediateField.inclusion hER).toRingHom.toAlgebra
    haveI : IsScalarTower ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥R ↥K := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    haveI hAlgR : Algebra.IsAlgebraic ↥R ↥K := Algebra.IsAlgebraic.tower_top (K := ↥(IntermediateField.adjoin L ({j} : Set ↥K))) ↥R
    have hRint : (R.val.toRingHom : ↥R →+* ↥K).IsIntegral := fun x => (Algebra.IsIntegral.isIntegral (R := ↥R) x)

    let e : ↥K₀ ≃ₐ[L] ↥R := (IntermediateField.topEquiv).symm.trans (IntermediateField.equivMap ⊤ φK)
    have hcompφ : φK.toRingHom = (R.val.toRingHom : ↥R →+* ↥K).comp e.toAlgHom.toRingHom := by
      ext x; rfl
    rw [hcompφ]
    exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective _ e.surjective) hRint

  haveI : y.asIdeal.IsMaximal := hmax
  have hϖy : algebraMap A ↥(chartAlgInf A (↥K) j) ϖ ∈ y.asIdeal := by
    have h := hz
    rw [hϖz, ← hy] at h
    exact (germ_mem_maximalIdeal_iff_of_chart' (toBase A (↥K) j) (ιInf A (↥K) j) (ιInf_toBase A (↥K) j) y ϖ).mp h
  have hjInvy : jInvChartInf A (↥K) j ∈ y.asIdeal := hcusp

  have he : ∀ w : AlgebraicCurve.Place L ↥K, (∀ r : ↥(chartAlgInf A (↥K) j), 0 ≤ w.ord (algebraMap _ ↥K r)) →
      (∀ r : ↥(chartAlgInf A (↥K) j), r ≠ 0 → (0 < w.ord (algebraMap _ ↥K r) ↔ r ∈ 𝔔)) →
      AlgebraicCurve.Place.ramificationIndexAlong φK w = 1 := by
    intro w hw0 hw1
    have hjIne : jInvChartInf A (↥K) j ≠ 0 := by
      intro h
      have : ((jInvChartInf A (↥K) j : ↥(chartAlgInf A (↥K) j)) : ↥K) = 0 := by rw [h]; rfl
      rw [coe_jInvChartInf] at this
      exact (Fact.out : j ≠ 0) (inv_eq_zero.mp this)
    by_cases hcQ : jInvChartInf A (↥K) j ∈ 𝔔
    ·
      have hw : 0 < w.ord ((jInvChartInf A (↥K) j : ↥(chartAlgInf A (↥K) j)) : ↥K) := (hw1 _ hjIne).mpr hcQ
      have hwy : ∀ b : ↥(chartAlgInf A (↥K) j), 0 < w.ord (b : ↥K) → b ∈ y.asIdeal := by
        intro b hb
        have hb0 : b ≠ 0 := by rintro rfl; simp at hb
        exact h𝔔y ((hw1 b hb0).mp hb)
      rw [hφKdef]
      exact ModularCurve.FullLevel.ramificationIndexAlong_inclusion_eq_one_of_ord_jInvChartInf_pos_of_forall_ord_pos_mem_of_forall_mem_nonunits_gauss_xH_of_eq_two q hq2 M' hqM' L K hK A hAq j hj ϖ hϖ W₀ hW₀ K₀ hK₀ hle₀ w hw y.asIdeal hϖy hz₀ hwy
    ·
      have hordInv : w.ord ((jInvChartInf A (↥K) j : ↥(chartAlgInf A (↥K) j)) : ↥K) = 0 := by
        have h1 := hw0 (jInvChartInf A (↥K) j)
        have h2 := (hw1 _ hjIne).not.mpr hcQ
        change 0 ≤ w.ord ((jInvChartInf A (↥K) j : ↥(chartAlgInf A (↥K) j)) : ↥K) at h1
        change ¬ 0 < w.ord ((jInvChartInf A (↥K) j : ↥(chartAlgInf A (↥K) j)) : ↥K) at h2
        omega
      have hord0 : w.ord j = 0 := by
        rw [coe_jInvChartInf, AlgebraicCurve.Place.ord_inv] at hordInv
        omega

      set u : ↥(chartAlgInf A (↥K) j) := 1 - 1728 * jInvChartInf A (↥K) j with hu
      have huQ : u ∉ 𝔔 := by
        intro h
        apply hmax.ne_top
        rw [Ideal.eq_top_iff_one]
        have : (1 : ↥(chartAlgInf A (↥K) j)) = u + 1728 * jInvChartInf A (↥K) j := by rw [hu]; ring
        rw [this]
        exact y.asIdeal.add_mem (h𝔔y h) (y.asIdeal.mul_mem_left _ hjInvy)
      have hune : u ≠ 0 := fun h => huQ (h ▸ 𝔔.zero_mem)
      have hordu : w.ord (u : ↥K) = 0 := by
        have h1 := hw0 u
        have h2 := (hw1 _ hune).not.mpr huQ
        change 0 ≤ w.ord (u : ↥K) at h1
        change ¬ 0 < w.ord (u : ↥K) at h2
        omega
      have hj0K : (j : ↥K) ≠ 0 := Fact.out
      have hcoeu : (u : ↥K) = 1 - 1728 * (j : ↥K)⁻¹ := by
        show (chartAlgInf A (↥K) j).val u = _
        rw [hu, map_sub, map_one, map_mul, map_ofNat]
        show 1 - 1728 * ((jInvChartInf A (↥K) j : ↥(chartAlgInf A (↥K) j)) : ↥K) = _
        rw [coe_jInvChartInf]
      have hord1728 : w.ord (j - 1728) = 0 := by
        have hfac : (j : ↥K) - 1728 = j * (u : ↥K) := by
          rw [hcoeu, mul_sub, mul_one, ← mul_assoc, mul_comm (j : ↥K) 1728, mul_assoc, mul_inv_cancel₀ hj0K, mul_one]
        have hu0 : (u : ↥K) ≠ 0 := by
          intro h; apply hune; exact Subtype.ext h
        rw [hfac, w.ord_mul hj0K hu0, hord0, hordu]; rfl
      rw [hφKdef]
      exact ModularCurve.FullLevel.ramificationIndexAlong_inclusion_eq_one_of_ord_eq_zero_of_ord_sub_eq_zero_xH_levelH_of_eq_two
        q hq2 M' hqM' L K hK K₀ hK₀ hle₀ j hj w hord0 hord1728
  exact Algebra.isUnramifiedAt_of_height_eq_one_of_not_mem_of_ramificationIndexAlong_eq_one_of_centre
    L A ↥K ↥K₀ φK ↥(chartAlgInf A (↥K) j) ↥(chartAlgInf A (↥K₀) j₀) hιK hint 𝔔 hQ1 he ϖ hϖ hϖQ

end S_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_isUnramifiedAt_of_height_one_of_algebraMap_not_mem_chartAlgInf_of_jInvChartInf_mem_xH_of_eq_two (solution)
