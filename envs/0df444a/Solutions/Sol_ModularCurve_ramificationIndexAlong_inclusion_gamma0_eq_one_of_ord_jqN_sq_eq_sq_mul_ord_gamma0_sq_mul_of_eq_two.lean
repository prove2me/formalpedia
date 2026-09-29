-- Prove2me | solution 1 for ModularCurve.ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jqN_sq_eq_sq_mul_ord_gamma0_sq_mul_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1c45ace5-c36a-5351-809e-924e43f1d21f

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndexAlong_eq_one_of_ord_eval_derivative_eq_zero
import Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_lt_of_le_and_natDegree_coeff_sub_one_eq
import Theorems.Thm_ModularCurve_exists_polynomial_eval2_inclusion_eq_of_laurentBaseChange_gamma0_sq_mul_of_eq_two
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jqN_sq_eq_sq_mul_ord_gamma0_sq_mul_of_eq_two
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg"
p2m_attr_erase "instance" "ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_jqNGen CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"
p2m_attr_erase "simp" "CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def"

set_option autoImplicit false

open ModularCurve Polynomial

namespace PWKit

open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F)

theorem min_ord_le_ord_add {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  have h := v.adicValuation.map_add f g
  have hf' := v.adicValuation_ne_zero hf
  have hg' := v.adicValuation_ne_zero hg
  have hfg' := v.adicValuation_ne_zero hfg
  simp only [AlgebraicCurve.Place.ord]
  rcases le_max_iff.mp h with h1 | h1
  · have := (WithZero.log_le_log hfg' hf').mpr h1
    omega
  · have := (WithZero.log_le_log hfg' hg').mpr h1
    omega

theorem ord_algebraMap {a : K} (ha : a ≠ 0) : v.ord (algebraMap K F a) = 0 := by
  have hmem : algebraMap K F a ∈ v.toValuationSubring := v.algebraMap_mem' a
  have hmem' : algebraMap K F a⁻¹ ∈ v.toValuationSubring := v.algebraMap_mem' a⁻¹
  have hu : IsUnit (⟨algebraMap K F a, hmem⟩ : v.toValuationSubring) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K F a⁻¹, hmem'⟩, ?_⟩
    ext
    show algebraMap K F a * algebraMap K F a⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ ha, map_one]
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rw [hu] at this
  exact this

theorem ord_natCast (n : ℕ) : v.ord (n : F) = 0 := by
  by_cases hn : (n : K) = 0
  · have : (n : F) = 0 := by rw [← map_natCast (algebraMap K F) n, hn, map_zero]
    rw [this, v.ord_zero]
  · rw [← map_natCast (algebraMap K F) n]
    exact ord_algebraMap v hn

theorem ord_intCast (n : ℤ) : v.ord (n : F) = 0 := by
  by_cases hn : (n : K) = 0
  · have : (n : F) = 0 := by rw [← map_intCast (algebraMap K F) n, hn, map_zero]
    rw [this, v.ord_zero]
  · rw [← map_intCast (algebraMap K F) n]
    exact ord_algebraMap v hn

theorem ord_pow (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

theorem ord_neg (f : F) : v.ord (-f) = v.ord f := by
  simp only [AlgebraicCurve.Place.ord, Valuation.map_neg]

theorem ord_sub_comm (f g : F) : v.ord (f - g) = v.ord (g - f) := by
  rw [← neg_sub, ord_neg]

theorem nonneg_add {f g : F} (hf : 0 ≤ v.ord f) (hg : 0 ≤ v.ord g) : 0 ≤ v.ord (f + g) := by
  by_cases hf0 : f = 0
  · simpa [hf0] using hg
  by_cases hg0 : g = 0
  · simpa [hg0] using hf
  by_cases hfg : f + g = 0
  · rw [hfg, v.ord_zero]
  have := min_ord_le_ord_add v hf0 hg0 hfg
  omega

theorem small_add {f g : F} (hf : f = 0 ∨ 0 < v.ord f) (hg : g = 0 ∨ 0 < v.ord g) :
    f + g = 0 ∨ 0 < v.ord (f + g) := by
  rcases hf with rfl | hf
  · simpa using hg
  rcases hg with rfl | hg
  · simpa using Or.inr hf
  by_cases hf0 : f = 0
  · rw [hf0, v.ord_zero] at hf; exact absurd hf (lt_irrefl _)
  by_cases hg0 : g = 0
  · rw [hg0, v.ord_zero] at hg; exact absurd hg (lt_irrefl _)
  by_cases hfg : f + g = 0
  · exact Or.inl hfg
  have := min_ord_le_ord_add v hf0 hg0 hfg
  right; omega

theorem nonneg_mul {f g : F} (hf : 0 ≤ v.ord f) (hg : 0 ≤ v.ord g) : 0 ≤ v.ord (f * g) := by
  by_cases hf0 : f = 0
  · simp [hf0]
  by_cases hg0 : g = 0
  · simp [hg0]
  rw [v.ord_mul hf0 hg0]; omega

theorem small_mul_nonneg {f g : F} (hf : f = 0 ∨ 0 < v.ord f) (hg : 0 ≤ v.ord g) :
    f * g = 0 ∨ 0 < v.ord (f * g) := by
  by_cases hf0 : f = 0
  · simp [hf0]
  by_cases hg0 : g = 0
  · simp [hg0]
  rcases hf with h | h
  · exact absurd h hf0
  right; rw [v.ord_mul hf0 hg0]; omega

theorem nonneg_mul_small {f g : F} (hf : 0 ≤ v.ord f) (hg : g = 0 ∨ 0 < v.ord g) :
    f * g = 0 ∨ 0 < v.ord (f * g) := by
  rw [mul_comm]; exact small_mul_nonneg v hg hf

theorem nonneg_of_small {f : F} (hf : f = 0 ∨ 0 < v.ord f) : 0 ≤ v.ord f := by
  rcases hf with rfl | hf
  · simp
  · exact hf.le

theorem nonneg_pow {f : F} (hf : 0 ≤ v.ord f) (n : ℕ) : 0 ≤ v.ord (f ^ n) := by
  rw [ord_pow]; positivity

theorem nonneg_sum {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, 0 ≤ v.ord (f i)) :
    0 ≤ v.ord (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact nonneg_add v (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem small_sum {ι : Type*} (s : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ s, f i = 0 ∨ 0 < v.ord (f i)) :
    (∑ i ∈ s, f i) = 0 ∨ 0 < v.ord (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact small_add v (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem nonneg_aeval {t : F} (ht : 0 ≤ v.ord t) (P : Polynomial ℤ) :
    0 ≤ v.ord (Polynomial.aeval t P) := by
  rw [Polynomial.aeval_eq_sum_range]
  refine nonneg_sum v _ _ (fun i _ => ?_)
  rw [zsmul_eq_mul]
  exact nonneg_mul v (by rw [ord_intCast]) (nonneg_pow v ht i)

theorem aeval_eq_coeff_zero_add (t : F) (P : Polynomial ℤ) :
    Polynomial.aeval t P = ((P.coeff 0 : ℤ) : F) + t * Polynomial.aeval t P.divX := by
  conv_lhs => rw [← Polynomial.X_mul_divX_add P]
  rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, add_comm]
  simp

theorem unit_add_small {x s : F} (hx : x ≠ 0) (hx0 : v.ord x = 0) (hs : s = 0 ∨ 0 < v.ord s) :
    x + s ≠ 0 ∧ v.ord (x + s) = 0 := by
  rcases hs with rfl | hs
  · simpa using And.intro hx hx0
  have hs0 : s ≠ 0 := by rintro rfl; rw [v.ord_zero] at hs; exact lt_irrefl _ hs
  have hxs : x + s ≠ 0 := by
    intro h
    have : s = -x := by linear_combination h
    rw [this, ord_neg] at hs; omega
  refine ⟨hxs, ?_⟩
  have h1 := min_ord_le_ord_add v hx hs0 hxs
  have h2 := min_ord_le_ord_add v hxs (neg_ne_zero.mpr hs0) (by simpa using hx)
  rw [ord_neg] at h2
  have h3 : x + s + -s = x := by ring
  rw [h3] at h2
  omega

theorem small_of_unit_mul {u s : F} (hu : u ≠ 0) (hu0 : v.ord u = 0)
    (h : u * s = 0 ∨ 0 < v.ord (u * s)) : s = 0 ∨ 0 < v.ord s := by
  by_cases hs : s = 0
  · exact Or.inl hs
  rcases h with h | h
  · exact absurd ((mul_eq_zero.mp h).resolve_left hu) hs
  right; rw [v.ord_mul hu hs] at h; omega

theorem derivative_unit_of_reduction
    (t g : F) (ht : t = 0 ∨ 0 < v.ord t) (hg0 : g ≠ 0) (hg : v.ord g = 0)
    (m : ℕ) (P : ℕ → Polynomial ℤ) (hPtop : P (m + 2) = 1) (hP1 : (P (m + 1)).coeff 0 = -1)
    (hP0 : ∀ k, k < m + 1 → (P k).coeff 0 = 0)
    (hroot : ∑ k ∈ Finset.range (m + 3), Polynomial.aeval t (P k) * g ^ k = 0) :
    (∑ k ∈ Finset.range (m + 3), (Polynomial.aeval t (P k) * k) * g ^ (k - 1)) ≠ 0 ∧
    v.ord (∑ k ∈ Finset.range (m + 3), (Polynomial.aeval t (P k) * k) * g ^ (k - 1)) = 0 := by

  set s : ℕ → F := fun k => t * Polynomial.aeval t (P k).divX with hs
  have hsmall : ∀ k, s k = 0 ∨ 0 < v.ord (s k) := fun k =>
    small_mul_nonneg v ht (nonneg_aeval v (nonneg_of_small v ht) _)
  have hc : ∀ k, Polynomial.aeval t (P k) = (((P k).coeff 0 : ℤ) : F) + s k := fun k =>
    aeval_eq_coeff_zero_add t (P k)
  have hctop : Polynomial.aeval t (P (m + 2)) = 1 := by rw [hPtop, map_one]
  have hc1 : Polynomial.aeval t (P (m + 1)) = -1 + s (m + 1) := by rw [hc, hP1]; simp
  have hc0 : ∀ k ∈ Finset.range (m + 1), Polynomial.aeval t (P k) = s k := by
    intro k hk
    rw [hc, hP0 k (Finset.mem_range.mp hk)]; simp
  have hgn : ∀ n : ℕ, 0 ≤ v.ord (g ^ n) := fun n => nonneg_pow v hg.ge n

  have hroot' : g ^ (m + 1) * (g - 1) =
      -(∑ k ∈ Finset.range (m + 1), s k * g ^ k + s (m + 1) * g ^ (m + 1)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hctop, hc1, Finset.sum_congr rfl
      (fun k hk => by rw [hc0 k hk])] at hroot
    linear_combination hroot
  have hgm1 : g - 1 = 0 ∨ 0 < v.ord (g - 1) := by
    refine small_of_unit_mul v (pow_ne_zero (m + 1) hg0) (by rw [ord_pow, hg, mul_zero]) ?_
    rw [hroot']
    rcases small_add v (small_sum v _ _ (fun k _ => small_mul_nonneg v (hsmall k) (hgn k)))
      (small_mul_nonneg v (hsmall (m + 1)) (hgn (m + 1))) with h | h
    · left; rw [h, neg_zero]
    · right; rwa [ord_neg]

  have hD : (∑ k ∈ Finset.range (m + 3), (Polynomial.aeval t (P k) * k) * g ^ (k - 1)) =
      g ^ m + (∑ k ∈ Finset.range (m + 1), (s k * k) * g ^ (k - 1) + (s (m + 1) * (m + 1 : ℕ)) * g ^ m
        + g ^ m * (m + 2 : ℕ) * (g - 1)) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, hctop, hc1, Finset.sum_congr rfl
      (fun k hk => by rw [hc0 k hk])]
    simp only [Nat.add_succ_sub_one, add_zero]
    push_cast
    ring
  rw [hD]
  refine unit_add_small v (pow_ne_zero m hg0) (by rw [ord_pow, hg, mul_zero]) ?_
  refine small_add v (small_add v (small_sum v _ _ (fun k _ => ?_)) ?_) ?_
  · exact small_mul_nonneg v (small_mul_nonneg v (hsmall k) (by rw [ord_natCast])) (hgn _)
  · exact small_mul_nonneg v (small_mul_nonneg v (hsmall _) (by rw [ord_natCast])) (hgn _)
  · exact nonneg_mul_small v (nonneg_mul v (hgn m) (by rw [ord_natCast])) hgm1

end PWKit

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]

    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q ^ 2 * M'))))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)

    (J₂ : ↥K) (hJ₂ : ((J₂ : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.jqN (q ^ 2)))

    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle₀ : K₀ ≤ K)

    (w : AlgebraicCurve.Place L ↥K) (hw : w.ord j < 0)
    (hP : w.ord J₂ = (q : ℤ) ^ 2 * w.ord j) :
    AlgebraicCurve.Place.ramificationIndexAlong (IntermediateField.inclusion hle₀) w = 1 := by
  classical
  set φ : ↥K₀ →ₐ[L] ↥K := IntermediateField.inclusion hle₀ with hφdef
  haveI hNz : NeZero (q ^ 2) := ⟨pow_ne_zero 2 (Fact.out : q.Prime).ne_zero⟩
  have hqsq : 2 ≤ q ^ 2 := by rw [hq2]; norm_num

  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData (q ^ 2)

  obtain ⟨hlt, hdeg1, hlc1⟩ :=
    ModularCurve.ModularPolynomialData.natDegree_coeff_lt_of_le_and_natDegree_coeff_sub_one_eq (q ^ 2) hqsq data

  have hψ2 : 2 ≤ dedekindPsi (q ^ 2) := by
    have h1 : (q ^ 2) / 1 ≤ dedekindPsi (q ^ 2) := by
      rw [dedekindPsi]
      refine Finset.single_le_sum (f := fun d => q ^ 2 / d) (fun _ _ => Nat.zero_le _) ?_
      exact Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne _), squarefree_one⟩
    rw [Nat.div_one] at h1
    omega
  obtain ⟨m, hm⟩ : ∃ m : ℕ, dedekindPsi (q ^ 2) = m + 2 := ⟨dedekindPsi (q ^ 2) - 2, by omega⟩
  rw [hm] at hlt hdeg1 hlc1
  rw [show m + 2 - 1 = m + 1 by omega] at hdeg1 hlc1
  have hΦtop : data.Φ.coeff (m + 2) = 1 := by
    rw [← hm, ← data.natDegree_eq]; exact data.monic.coeff_natDegree
  have hΦdeg : ∀ k, (data.Φ.coeff k).natDegree ≤ q ^ 2 * (m + 2 - k) := by
    intro k
    rcases lt_or_ge k (m + 1) with hk | hk
    · exact (hlt k (by omega)).le
    rcases (show k = m + 1 ∨ k = m + 2 ∨ m + 2 < k by omega) with rfl | rfl | hk'
    · rw [hdeg1]; exact Nat.le_mul_of_pos_right _ (by omega)
    · rw [hΦtop, Polynomial.natDegree_one]; exact Nat.zero_le _
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [data.natDegree_eq, hm]; exact hk'),
        Polynomial.natDegree_zero]; exact Nat.zero_le _

  set P : ℕ → Polynomial ℤ := fun k => Polynomial.reflect (q ^ 2 * (m + 2 - k)) (data.Φ.coeff k) with hPdef
  have hPtop : P (m + 2) = 1 := by
    simp only [hPdef]
    rw [Nat.sub_self, mul_zero, hΦtop, ← Polynomial.C_1, Polynomial.reflect_C, pow_zero, mul_one]
  have hP1 : (P (m + 1)).coeff 0 = -1 := by
    simp only [hPdef]
    rw [Polynomial.coeff_reflect, Polynomial.revAt_zero, show m + 2 - (m + 1) = 1 by omega, mul_one]
    have h := hlc1
    rwa [Polynomial.leadingCoeff, hdeg1] at h
  have hP0 : ∀ k, k < m + 1 → (P k).coeff 0 = 0 := by
    intro k hk
    simp only [hPdef]
    rw [Polynomial.coeff_reflect, Polynomial.revAt_zero]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hlt k (by omega))

  have hj0 : (j : ↥K) ≠ 0 := by
    intro h0; rw [h0, AlgebraicCurve.Place.ord_zero] at hw; exact lt_irrefl _ hw
  have hJ0 : (J₂ : ↥K) ≠ 0 := by
    intro h
    have h1 : (ModularCurve.coeffEmb L (ModularCurve.jqN (q ^ 2))).coeff (((q ^ 2 : ℕ) : ℤ) * (-1)) = 0 := by
      rw [← hJ₂, h]; simp
    rw [ModularCurve.coeffEmb_coeff, ModularCurve.jqN, ModularCurve.qExpand_coeff_mul,
      ModularCurve.coeff_jq_neg_one, map_one] at h1
    exact one_ne_zero h1

  have hjmem : (j : LaurentSeries L) ∈ K₀ := by
    rw [hj, hK₀]
    refine ModularCurve.coeffEmb_mem_laurentBaseChange L ?_
    rw [ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    exact ModularCurve.modularFunctionField_le_full M' (ModularCurve.jq_mem M')
  set j₀ : ↥K₀ := ⟨(j : LaurentSeries L), hjmem⟩ with hj₀def
  have hj₀ : φ j₀ = j := Subtype.ext rfl

  set t₀ : ↥K₀ := j₀⁻¹ with ht₀
  set t : ↥K := j⁻¹ with ht
  have hφt : φ t₀ = t := by rw [ht₀, map_inv₀, hj₀]
  have ht0 : t ≠ 0 := by rw [ht]; exact inv_ne_zero hj0
  have htj : t * j = 1 := by rw [ht]; exact inv_mul_cancel₀ hj0
  set g : ↥K := J₂ * t ^ (q ^ 2) with hg
  have hg0 : g ≠ 0 := mul_ne_zero hJ0 (pow_ne_zero _ ht0)
  have hordt : w.ord t = - w.ord j := by rw [ht, w.ord_inv]
  have htsmall : t = 0 ∨ 0 < w.ord t := Or.inr (by rw [hordt]; omega)
  have hordg : w.ord g = 0 := by
    rw [hg, w.ord_mul hJ0 (pow_ne_zero _ ht0), PWKit.ord_pow, hordt, hP]; push_cast; ring

  set ev : Polynomial ℤ →+* ↥K := Polynomial.eval₂RingHom (Int.castRingHom ↥K) j with hev
  have hroot : Polynomial.eval₂ ev J₂ data.Φ = 0 := by
    apply Subtype.val_injective
    have h1 := Polynomial.hom_eval₂ data.Φ ev (algebraMap ↥K (LaurentSeries L)) J₂
    have hcomp : (algebraMap ↥K (LaurentSeries L)).comp ev =
        Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) ((j : LaurentSeries L)) := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      rw [hev]; simp
    have hcomp2 : (ModularCurve.coeffEmb L).comp ModularCurve.evalAtJ =
        Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries L)) ((j : LaurentSeries L)) := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      rw [RingHom.comp_apply, ModularCurve.evalAtJ_X, ← hj]; simp
    have h2 := Polynomial.hom_eval₂ data.Φ ModularCurve.evalAtJ (ModularCurve.coeffEmb L) (ModularCurve.jqN (q ^ 2))
    rw [data.eval_eq_zero, map_zero, hcomp2, ← hJ₂] at h2
    show (algebraMap ↥K (LaurentSeries L)) (Polynomial.eval₂ ev J₂ data.Φ) = ((0 : ↥K) : LaurentSeries L)
    rw [h1, hcomp]
    exact h2.symm.trans (by simp)
  have hroot2 : ∑ k ∈ Finset.range (m + 3), Polynomial.aeval j (data.Φ.coeff k) * J₂ ^ k = 0 := by
    rw [Polynomial.eval₂_eq_sum_range, data.natDegree_eq, hm] at hroot
    rw [← hroot]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Polynomial.aeval_def, algebraMap_int_eq, hev, Polynomial.coe_eval₂RingHom]

  have hrefl : ∀ k, Polynomial.aeval t (P k) * j ^ (q ^ 2 * (m + 2 - k)) = Polynomial.aeval j (data.Φ.coeff k) := by
    intro k
    haveI : Invertible (j : ↥K) := invertibleOfNonzero hj0
    have h := Polynomial.eval₂_reflect_mul_pow (algebraMap ℤ ↥K) j (q ^ 2 * (m + 2 - k)) (data.Φ.coeff k) (hΦdeg k)
    rw [invOf_eq_inv] at h
    rw [Polynomial.aeval_def, Polynomial.aeval_def, ht]
    exact h

  have hJint : φ.toRingHom.IsIntegralElem J₂ := by
    refine ⟨data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥K₀) j₀), data.monic.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : φ.toRingHom.comp (Polynomial.eval₂RingHom (Int.castRingHom ↥K₀) j₀) = ev := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      rw [hev, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, Polynomial.eval₂_X, ← hj₀]
      rfl
    rw [hc]; exact hroot
  have hφ : φ.toRingHom.IsIntegral := by
    letI : Algebra ↥K₀ ↥K := φ.toRingHom.toAlgebra
    have hJ : IsIntegral ↥K₀ J₂ := hJint
    intro x
    obtain ⟨p, hp⟩ := ModularCurve.exists_polynomial_eval2_inclusion_eq_of_laurentBaseChange_gamma0_sq_mul_of_eq_two
      q hq2 M' hqM' L K hK j hj J₂ hJ₂ K₀ hK₀ hle₀ x
    rw [← hp, Polynomial.eval₂_eq_sum_range]
    show IsIntegral ↥K₀ _
    refine Finset.sum_induction _ (fun y => IsIntegral ↥K₀ y) (fun a b ha hb => ha.add hb)
      isIntegral_zero (fun i _ => ?_)
    exact IsIntegral.mul isIntegral_algebraMap (hJ.pow i)

  have hJg : φ (j₀ ^ (q ^ 2)) * g = J₂ := by
    rw [map_pow, hj₀, hg, ht, mul_left_comm, ← mul_pow, mul_inv_cancel₀ hj0, one_pow, mul_one]
  have hgen : ∀ x : ↥K, ∃ p : Polynomial ↥K₀, Polynomial.eval₂ φ.toRingHom g p = x := by
    intro x
    obtain ⟨p, hp⟩ := ModularCurve.exists_polynomial_eval2_inclusion_eq_of_laurentBaseChange_gamma0_sq_mul_of_eq_two
      q hq2 M' hqM' L K hK j hj J₂ hJ₂ K₀ hK₀ hle₀ x
    refine ⟨p.comp (Polynomial.C (j₀ ^ (q ^ 2)) * Polynomial.X), ?_⟩
    rw [← hp, Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_eq_eval_map, Polynomial.map_comp,
      Polynomial.eval_comp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, ← hJg]
    rfl

  set c₀ : ℕ → ↥K₀ := fun k => Polynomial.aeval t₀ (P k) with hc₀
  have hφc : ∀ k, φ (c₀ k) = Polynomial.aeval t (P k) := by
    intro k
    simp only [hc₀]
    rw [Polynomial.aeval_def, Polynomial.aeval_def, ← hφt]
    show φ.toRingHom (eval₂ (algebraMap ℤ ↥K₀) t₀ (P k)) = _
    rw [Polynomial.hom_eval₂, RingHom.ext_int (φ.toRingHom.comp (algebraMap ℤ ↥K₀)) (algebraMap ℤ ↥K)]
    rfl
  set Ψ : Polynomial ↥K₀ := ∑ k ∈ Finset.range (m + 3), Polynomial.C (c₀ k) * Polynomial.X ^ k with hΨ
  have hΨcoeff : ∀ i, Ψ.coeff i = if i ∈ Finset.range (m + 3) then c₀ i else 0 := by
    intro i
    rw [hΨ, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
  have hΨtop : Ψ.coeff (m + 2) = 1 := by
    rw [hΨcoeff, if_pos (Finset.mem_range.mpr (by omega))]
    simp only [hc₀]; rw [hPtop, map_one]
  have hΨdeg : Ψ.natDegree ≤ m + 2 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [hΨcoeff, if_neg (fun h => by have := Finset.mem_range.mp h; omega)]
  have hΨmonic : Ψ.Monic := Polynomial.monic_of_natDegree_le_of_coeff_eq_one (m + 2) hΨdeg hΨtop
  have hevalΨ : Polynomial.eval₂ φ.toRingHom g Ψ =
      ∑ k ∈ Finset.range (m + 3), Polynomial.aeval t (P k) * g ^ k := by
    rw [hΨ, Polynomial.eval₂_finsetSum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, ← hφc]
    rfl
  have hevalΨ' : Polynomial.eval₂ φ.toRingHom g (Polynomial.derivative Ψ) =
      ∑ k ∈ Finset.range (m + 3), (Polynomial.aeval t (P k) * k) * g ^ (k - 1) := by
    rw [hΨ, Polynomial.derivative_sum, Polynomial.eval₂_finsetSum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Polynomial.derivative_C_mul_X_pow, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow,
      map_mul, map_natCast, ← hφc]
    rfl

  have ht₀pos : 0 < (w.restrictAlong φ hφ).ord t₀ := by
    have h := AlgebraicCurve.Place.ord_restrictAlong φ hφ w t₀
    rw [hφt, hordt] at h
    have h2 : 0 < (AlgebraicCurve.Place.ramificationIndexAlong φ w : ℤ) * (w.restrictAlong φ hφ).ord t₀ := by
      rw [← h]; omega
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos h2 with ⟨-, h3⟩ | ⟨h3, -⟩
    · exact h3
    · exact absurd h3 (not_lt.mpr (Nat.cast_nonneg _))
  have hgO : ∀ i : ℕ, 0 ≤ (w.restrictAlong φ hφ).ord (Ψ.coeff i) := by
    intro i
    rw [hΨcoeff]
    split_ifs
    · simp only [hc₀]; exact PWKit.nonneg_aeval _ ht₀pos.le _
    · simp

  have hck : ∀ k ∈ Finset.range (m + 3), Polynomial.aeval t (P k) * g ^ k =
      t ^ (q ^ 2 * (m + 2)) * (Polynomial.aeval j (data.Φ.coeff k) * J₂ ^ k) := by
    intro k hk
    have hk' : k ≤ m + 2 := by have := Finset.mem_range.mp hk; omega
    rw [← hrefl k, hg]
    have e1 : t ^ (q ^ 2 * (m + 2)) = t ^ (q ^ 2 * k) * t ^ (q ^ 2 * (m + 2 - k)) := by
      rw [← pow_add, ← mul_add]; congr 2; omega
    have e2 : t ^ (q ^ 2 * (m + 2 - k)) * j ^ (q ^ 2 * (m + 2 - k)) = 1 := by
      rw [← mul_pow, htj, one_pow]
    calc Polynomial.aeval t (P k) * (J₂ * t ^ (q ^ 2)) ^ k
        = Polynomial.aeval t (P k) * J₂ ^ k * t ^ (q ^ 2 * k) *
            (t ^ (q ^ 2 * (m + 2 - k)) * j ^ (q ^ 2 * (m + 2 - k))) := by
          rw [e2, mul_one, mul_pow, ← pow_mul]; ring
      _ = t ^ (q ^ 2 * (m + 2)) * (Polynomial.aeval t (P k) * j ^ (q ^ 2 * (m + 2 - k)) * J₂ ^ k) := by
          rw [e1]; ring
  have hgz' : ∑ k ∈ Finset.range (m + 3), Polynomial.aeval t (P k) * g ^ k = 0 := by
    rw [Finset.sum_congr rfl hck, ← Finset.mul_sum, hroot2, mul_zero]
  have hgz : Polynomial.eval₂ φ.toRingHom g Ψ = 0 := by rw [hevalΨ]; exact hgz'

  obtain ⟨hne', hsimple'⟩ :=
    PWKit.derivative_unit_of_reduction w t g htsmall hg0 hordg m P hPtop hP1 hP0 hgz'
  have hne : Polynomial.eval₂ φ.toRingHom g (Polynomial.derivative Ψ) ≠ 0 := by
    rw [hevalΨ']; exact hne'
  have hsimple : w.ord (Polynomial.eval₂ φ.toRingHom g (Polynomial.derivative Ψ)) = 0 := by
    rw [hevalΨ']; exact hsimple'

  have := AlgebraicCurve.Place.ramificationIndexAlong_eq_one_of_ord_eval_derivative_eq_zero
    φ hφ w g hgen Ψ hΨmonic hgO hgz hne hsimple
  simpa [hφdef] using this

end S_ModularCurve_ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jqN_sq_eq_sq_mul_ord_gamma0_sq_mul_of_eq_two
end P2MW
export P2MW.S_ModularCurve_ramificationIndexAlong_inclusion_gamma0_eq_one_of_ord_jqN_sq_eq_sq_mul_ord_gamma0_sq_mul_of_eq_two (solution)
