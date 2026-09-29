-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_pair_qExpFunctionFieldC_intertwines_heckeAlphaModLH_heckeBetaModLH_and_reduction_slash_fricke
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/f6dae9ce-22fa-5426-9ac0-b54970fbd014

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_exists_valuationSubring_liesOverPrime_forall_mlocal_iff_mem_range
import Theorems.Thm_ModularCurve_exists_algEquiv_pair_xHFunctionFieldBar_slash_fricke_intertwines_heckeAlphaHBar_heckeBetaHBar
import Theorems.Thm_ModularCurve_forall_apply_mem_gaussValuationSubring_iff_of_apply_jqModC_eq_qExpand_of_liesOverPrime
import Theorems.Thm_ModularCurve_exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_of_liesOverPrime_xHTop
import Theorems.Thm_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP
import Theorems.Thm_ModularCurve_coe_apply_eq_qExpand_jqModC_of_forall_coeffMap_mul_qExpansion_slash_fricke_eq
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC_of_liesOverPrime
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_heckeBetaModLHDefined
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_CohCarrier_gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_intertwines_heckeAlphaModLH_heckeBetaModLH_and_reduction_slash_fricke
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP"
p2m_attr_erase "simp" "ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"

set_option autoImplicit false

noncomputable section

namespace FrickePairAsm

open IsLocalRing

abbrev Zbar : Type := ↥(integralClosure ℤ ℂ)

def ιC : AlgebraicClosure ℚ →+* ℂ := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  exact ((IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ) : AlgebraicClosure ℚ →+* ℂ)

theorem ιC_injective : Function.Injective ιC := (ιC).injective

section Ker

variable {K : Type*} [Field K]

theorem natCast_mem_ker (p : ℕ) [CharP K p] (φ : Zbar →+* K) : ((p : ℕ) : Zbar) ∈ RingHom.ker φ := by
  rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]

theorem ker_isMaximal (p : ℕ) [Fact p.Prime] [CharP K p] (φ : Zbar →+* K) : (RingHom.ker φ).IsMaximal := by
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  haveI : Algebra.IsIntegral ℤ Zbar := inferInstance
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ) (RingHom.ker φ) ?_
  have hcomap : (RingHom.ker φ).comap (algebraMap ℤ Zbar) = Ideal.span {((p : ℕ) : ℤ)} := by
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_span_singleton]
    have : φ (algebraMap ℤ Zbar a) = (a : K) := by
      rw [← eq_intCast (φ.comp (algebraMap ℤ Zbar)) a]; rfl
    rw [this, CharP.intCast_eq_zero_iff K p]
  rw [hcomap]
  exact PrincipalIdealRing.isMaximal_of_irreducible
    (Int.prime_iff_natAbs_prime.mpr (by simpa using (Fact.out : p.Prime))).irreducible

end Ker

section Place

variable (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [CharP K p] (φ : Zbar →+* K)

theorem exists_place : ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p ∧
    ∀ z : ℂ, (∃ x y : Zbar, y ∉ RingHom.ker φ ∧ (x : ℂ) = y * z) ↔ ∃ a : AlgebraicClosure ℚ, a ∈ A ∧ ιC a = z :=
  exists_valuationSubring_liesOverPrime_forall_mlocal_iff_mem_range p ιC (RingHom.ker φ) (ker_isMaximal p φ)
    (natCast_mem_ker p φ)

variable (A : ValuationSubring (AlgebraicClosure ℚ))
  (hloc : ∀ z : ℂ, (∃ x y : Zbar, y ∉ RingHom.ker φ ∧ (x : ℂ) = y * z) ↔ ∃ a : AlgebraicClosure ℚ, a ∈ A ∧ ιC a = z)

include hloc

theorem exists_eq_of_zbar (z : Zbar) : ∃ a : ↥A, ιC (a : AlgebraicClosure ℚ) = (z : ℂ) := by
  obtain ⟨a, ha, e⟩ := (hloc (z : ℂ)).mp ⟨z, 1, by
    rw [RingHom.mem_ker, map_one]; exact one_ne_zero, by rw [OneMemClass.coe_one, one_mul]⟩
  exact ⟨⟨a, ha⟩, e⟩

def toA : Zbar →+* ↥A where
  toFun z := (exists_eq_of_zbar φ A hloc z).choose
  map_one' := by
    apply Subtype.ext; apply ιC_injective
    rw [(exists_eq_of_zbar φ A hloc 1).choose_spec, OneMemClass.coe_one, OneMemClass.coe_one, map_one]
  map_mul' a b := by
    apply Subtype.ext; apply ιC_injective
    rw [(exists_eq_of_zbar φ A hloc (a * b)).choose_spec, Subring.coe_mul, MulMemClass.coe_mul, map_mul,
      (exists_eq_of_zbar φ A hloc a).choose_spec, (exists_eq_of_zbar φ A hloc b).choose_spec]
  map_zero' := by
    apply Subtype.ext; apply ιC_injective
    rw [(exists_eq_of_zbar φ A hloc 0).choose_spec, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, map_zero]
  map_add' a b := by
    apply Subtype.ext; apply ιC_injective
    rw [(exists_eq_of_zbar φ A hloc (a + b)).choose_spec, Subring.coe_add, AddMemClass.coe_add, map_add,
      (exists_eq_of_zbar φ A hloc a).choose_spec, (exists_eq_of_zbar φ A hloc b).choose_spec]

theorem ιC_toA (z : Zbar) : ιC ((toA φ A hloc z : ↥A) : AlgebraicClosure ℚ) = (z : ℂ) :=
  (exists_eq_of_zbar φ A hloc z).choose_spec

theorem exists_pres (a : ↥A) : ∃ x y : Zbar, y ∉ RingHom.ker φ ∧ (x : ℂ) = y * ιC (a : AlgebraicClosure ℚ) :=
  (hloc _).mpr ⟨a, a.2, rfl⟩

theorem pres_indep {a : ↥A} {x y x' y' : Zbar} (hy : y ∉ RingHom.ker φ) (hy' : y' ∉ RingHom.ker φ)
    (h : (x : ℂ) = y * ιC (a : AlgebraicClosure ℚ)) (h' : (x' : ℂ) = y' * ιC (a : AlgebraicClosure ℚ)) :
    φ x * (φ y)⁻¹ = φ x' * (φ y')⁻¹ := by
  rw [RingHom.mem_ker] at hy hy'
  have hxy : x * y' = x' * y := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, h, h']; ring
  have := congrArg φ hxy
  rw [map_mul, map_mul] at this
  field_simp
  linear_combination this

def ψ : ↥A →+* K where
  toFun a := φ (exists_pres φ A hloc a).choose * (φ (exists_pres φ A hloc a).choose_spec.choose)⁻¹
  map_one' := by
    obtain ⟨hy, h⟩ := (exists_pres φ A hloc 1).choose_spec.choose_spec
    rw [pres_indep φ A hloc hy (y' := 1) (x' := 1) (by rw [RingHom.mem_ker, map_one]; exact one_ne_zero) h
      (by rw [OneMemClass.coe_one, OneMemClass.coe_one, map_one, mul_one]), map_one, inv_one, mul_one]
  map_mul' a b := by
    obtain ⟨hy, h⟩ := (exists_pres φ A hloc (a * b)).choose_spec.choose_spec
    obtain ⟨hya, ha⟩ := (exists_pres φ A hloc a).choose_spec.choose_spec
    obtain ⟨hyb, hb⟩ := (exists_pres φ A hloc b).choose_spec.choose_spec
    set xa := (exists_pres φ A hloc a).choose
    set ya := (exists_pres φ A hloc a).choose_spec.choose
    set xb := (exists_pres φ A hloc b).choose
    set yb := (exists_pres φ A hloc b).choose_spec.choose
    have hyy : ya * yb ∉ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_mul] at *; exact mul_ne_zero hya hyb
    rw [pres_indep φ A hloc hy hyy h (x' := xa * xb) (by
      rw [MulMemClass.coe_mul, MulMemClass.coe_mul, ha, hb, MulMemClass.coe_mul, map_mul]; ring)]
    rw [map_mul, map_mul, mul_inv]; ring
  map_zero' := by
    obtain ⟨hy, h⟩ := (exists_pres φ A hloc 0).choose_spec.choose_spec
    rw [pres_indep φ A hloc hy (y' := 1) (x' := 0) (by rw [RingHom.mem_ker, map_one]; exact one_ne_zero) h
      (by rw [ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, map_zero, mul_zero]), map_zero, zero_mul]
  map_add' a b := by
    obtain ⟨hy, h⟩ := (exists_pres φ A hloc (a + b)).choose_spec.choose_spec
    obtain ⟨hya, ha⟩ := (exists_pres φ A hloc a).choose_spec.choose_spec
    obtain ⟨hyb, hb⟩ := (exists_pres φ A hloc b).choose_spec.choose_spec
    set xa := (exists_pres φ A hloc a).choose
    set ya := (exists_pres φ A hloc a).choose_spec.choose
    set xb := (exists_pres φ A hloc b).choose
    set yb := (exists_pres φ A hloc b).choose_spec.choose
    have hyy : ya * yb ∉ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_mul] at *; exact mul_ne_zero hya hyb
    rw [pres_indep φ A hloc hy hyy h (x' := xa * yb + xb * ya) (by
      rw [AddMemClass.coe_add, MulMemClass.coe_mul, MulMemClass.coe_mul, ha, hb, MulMemClass.coe_mul,
        AddMemClass.coe_add, map_add]; ring)]
    rw [RingHom.mem_ker] at hya hyb
    rw [map_add, map_mul, map_mul, map_mul]
    field_simp
    ring

theorem ψ_eq {a : ↥A} {x y : Zbar} (hy : y ∉ RingHom.ker φ) (h : (x : ℂ) = y * ιC (a : AlgebraicClosure ℚ)) :
    ψ φ A hloc a = φ x * (φ y)⁻¹ := by
  obtain ⟨hy0, h0⟩ := (exists_pres φ A hloc a).choose_spec.choose_spec
  exact pres_indep φ A hloc hy0 hy h0 h

theorem ψ_toA (z : Zbar) : ψ φ A hloc (toA φ A hloc z) = φ z := by
  rw [ψ_eq φ A hloc (x := z) (y := 1) (by rw [RingHom.mem_ker, map_one]; exact one_ne_zero)
    (by rw [ιC_toA, OneMemClass.coe_one, one_mul]), map_one, inv_one, mul_one]

theorem isUnit_of_ψ_ne_zero {a : ↥A} (ha : ψ φ A hloc a ≠ 0) : IsUnit a := by
  obtain ⟨x, y, hy, h⟩ := exists_pres φ A hloc a
  rw [ψ_eq φ A hloc hy h] at ha
  have hx : x ∉ RingHom.ker φ := by
    intro hx; rw [RingHom.mem_ker] at hx; rw [hx, zero_mul] at ha; exact ha rfl
  have ha0 : (a : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    rw [h0, map_zero, mul_zero] at h
    apply hx; rw [RingHom.mem_ker]
    have : x = 0 := Subtype.ext (by rw [h, ZeroMemClass.coe_zero])
    rw [this, map_zero]

  obtain ⟨b, hb, hbι⟩ := (hloc (ιC (a : AlgebraicClosure ℚ))⁻¹).mp ⟨y, x, hx, by
    rw [h, mul_assoc, mul_inv_cancel₀ ((map_ne_zero ιC).mpr ha0), mul_one]⟩
  rw [← map_inv₀] at hbι
  have hb' : b = (a : AlgebraicClosure ℚ)⁻¹ := ιC_injective hbι
  rw [hb'] at hb
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hb⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

scoped instance : IsLocalHom (ψ φ A hloc) :=
  ⟨fun a ha => isUnit_of_ψ_ne_zero φ A hloc ha.ne_zero⟩

def θ : ResidueField ↥A →+* K := ResidueField.lift (ψ φ A hloc)

theorem θ_residue (a : ↥A) : θ φ A hloc (residue ↥A a) = ψ φ A hloc a := rfl

def φκ : Zbar →+* ResidueField ↥A := (residue ↥A).comp (toA φ A hloc)

theorem θ_comp_φκ : (θ φ A hloc).comp (φκ φ A hloc) = φ := by
  ext z
  show θ φ A hloc (residue ↥A (toA φ A hloc z)) = φ z
  rw [θ_residue, ψ_toA]

end Place

section Transport

variable {F Fb : Type*} [Field F] [Field Fb]

theorem exists_transport (W : ValuationSubring F) (red : ↥W →+* Fb) (hsurj : Function.Surjective red)
    (hker : RingHom.ker red = IsLocalRing.maximalIdeal ↥W) (w : F ≃+* F) (hstab : ∀ f, w f ∈ W ↔ f ∈ W) :
    ∃ Wr : Fb ≃+* Fb, ∀ g : ↥W, Wr (red g) = red ⟨w g, (hstab g).mpr g.2⟩ := by
  have hstab' : ∀ f, w.symm f ∈ W ↔ f ∈ W := fun f => by
    have h := hstab (w.symm f)
    rw [RingEquiv.apply_symm_apply] at h
    exact h.symm
  let ws : ↥W ≃+* ↥W :=
    { toFun := fun g => ⟨w g, (hstab g).mpr g.2⟩
      invFun := fun g => ⟨w.symm g, (hstab' g).mpr g.2⟩
      left_inv := fun g => Subtype.ext (w.symm_apply_apply (g : _))
      right_inv := fun g => Subtype.ext (w.apply_symm_apply (g : _))
      map_mul' := fun a b => Subtype.ext (map_mul w _ _)
      map_add' := fun a b => Subtype.ext (map_add w _ _) }
  have hunit : ∀ (e : ↥W ≃+* ↥W) (x : ↥W), x ∈ IsLocalRing.maximalIdeal ↥W → e x ∈ IsLocalRing.maximalIdeal ↥W := by
    intro e x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hu
    apply hx
    have := hu.map e.symm
    rwa [RingEquiv.symm_apply_apply] at this
  have hI : RingHom.ker red = Ideal.map (ws : ↥W →+* ↥W) (RingHom.ker red) := by
    apply le_antisymm
    · intro x hx
      have hx' : ws.symm x ∈ RingHom.ker red := by
        rw [hker] at hx ⊢
        exact hunit ws.symm x hx
      have := Ideal.mem_map_of_mem (ws : ↥W →+* ↥W) hx'
      rwa [RingHom.coe_coe, RingEquiv.apply_symm_apply] at this
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, RingHom.coe_coe]
      rw [hker] at hx ⊢
      exact hunit ws x hx
  let e := RingHom.quotientKerEquivOfSurjective hsurj
  let qws := Ideal.quotientEquiv (RingHom.ker red) (RingHom.ker red) ws hI
  refine ⟨e.symm.trans (qws.trans e), fun g => ?_⟩
  show e (qws (e.symm (red g))) = red (ws g)
  have h1 : e.symm (red g) = Ideal.Quotient.mk (RingHom.ker red) g :=
    RingHom.quotientKerEquivOfSurjective_symm_apply hsurj g
  rw [h1]
  show e (Ideal.quotientEquiv _ _ ws hI (Ideal.Quotient.mk (RingHom.ker red) g)) = _
  rw [Ideal.quotientEquiv_mk]
  exact RingHom.quotientKerEquivOfSurjective_apply_mk hsurj (ws g)

end Transport

section Laurent

open HahnSeries

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : PowerSeries R) :
    ModularCurve.coeffMap f (ofPowerSeries ℤ R u) = ofPowerSeries ℤ S (u.map f) := by
  ext k
  rw [ModularCurve.coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hk, ModularCurve.ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem map_map_int {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : PowerSeries ℤ) :
    (u.map (Int.castRingHom R)).map f = u.map (Int.castRingHom S) := by
  rw [show PowerSeries.map f (PowerSeries.map (Int.castRingHom R) u) = PowerSeries.map (f.comp (Int.castRingHom R)) u from
      (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom R) f)) u).symm,
    RingHom.ext_int (f.comp (Int.castRingHom R)) (Int.castRingHom S)]

theorem map_map' {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) (u : PowerSeries R) :
    (u.map f).map g = u.map (g.comp f) :=
  (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp f g)) u).symm

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (ModularCurve.coeffMap f) := by
  intro x y h
  ext k
  apply hf
  have := congrArg (fun z => HahnSeries.coeff z k) h
  simpa [ModularCurve.coeffMap_coeff] using this

theorem coeffMap_intSeriesC {R S : Type*} [Field R] [Field S] (f : R →+* S) (u : PowerSeries ℤ) :
    ModularCurve.coeffMap f (ModularCurve.intSeriesC R u) = ModularCurve.intSeriesC S u := by
  rw [ModularCurve.intSeriesC, coeffMap_ofPowerSeries, map_map_int, ModularCurve.intSeriesC]

theorem intSeriesC_ne_zero_of {R S : Type*} [Field R] [Field S] (f : R →+* S) {u : PowerSeries ℤ}
    (h : ModularCurve.intSeriesC S u ≠ 0) : ModularCurve.intSeriesC R u ≠ 0 := by
  intro h0; apply h; rw [← coeffMap_intSeriesC f, h0, map_zero]

theorem intSeriesC_ne_zero_of_ne_zero {R S : Type*} [Field R] [Field S] [CharZero R] {u : PowerSeries ℤ}
    (h : ModularCurve.intSeriesC S u ≠ 0) : ModularCurve.intSeriesC R u ≠ 0 := by
  have hu : u ≠ 0 := by rintro rfl; exact h (by rw [ModularCurve.intSeriesC, map_zero, map_zero])
  rw [ModularCurve.intSeriesC]
  intro h0
  apply hu
  have h1 : u.map (Int.castRingHom R) = 0 := HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
  have hinj : Function.Injective (Int.castRingHom R) := Int.cast_injective
  exact PowerSeries.map_injective (Int.castRingHom R) hinj (by rw [h1, map_zero])

theorem ofPowerSeries_ne_zero_iff {R : Type*} [CommRing R] {u : PowerSeries R} : ofPowerSeries ℤ R u ≠ 0 ↔ u ≠ 0 := by
  rw [not_iff_not]
  constructor
  · intro h; exact HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm)
  · intro h; rw [h, map_zero]

end Laurent

section SpecLaw

p2m_open "ModularCurve~coeffMap_injective~coeffMap_intSeriesC IsLocalRing HahnSeries"
open scoped MatrixGroups ModularForm

variable {K : Type*} [Field K] (φ : Zbar →+* K)
  (A : ValuationSubring (AlgebraicClosure ℚ))
  (hloc : ∀ z : ℂ, (∃ x y : Zbar, y ∉ RingHom.ker φ ∧ (x : ℂ) = y * z) ↔ ∃ a : AlgebraicClosure ℚ, a ∈ A ∧ ιC a = z)

theorem map_toA_spec (P : PowerSeries Zbar) :
    (P.map (toA φ A hloc)).map (ιC.comp A.subtype) = P.map (algebraMap Zbar ℂ) := by
  rw [map_map']
  have : (ιC.comp A.subtype).comp (toA φ A hloc) = algebraMap Zbar ℂ :=
    RingHom.ext fun z => ιC_toA φ A hloc z
  rw [this]

theorem map_toA_residue (P : PowerSeries Zbar) :
    (P.map (toA φ A hloc)).map (residue ↥A) = P.map (φκ φ A hloc) := by
  rw [map_map']; rfl

include hloc in
theorem lawS_of (Γ : Subgroup SL(2, ℤ)) (hΓ1 : (1 : ℝ) ∈ ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods)
    (W : ValuationSubring ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))
    (hW : ∀ f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)),
        f ∈ W ↔ ∃ x y : PowerSeries ↥A, y.map (IsLocalRing.residue ↥A) ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
          = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ))))
    (red : ↥W →+* ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
    (hpres : ∀ (f : ↥W) (x y : PowerSeries ↥A), y.map (IsLocalRing.residue ↥A) ≠ 0 →
        ((f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) : LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
          = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ))) →
        ((red f : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A)) *
            HahnSeries.ofPowerSeries ℤ (ResidueField ↥A) (y.map (IsLocalRing.residue ↥A)) =
          HahnSeries.ofPowerSeries ℤ (ResidueField ↥A) (x.map (IsLocalRing.residue ↥A)))
    (w : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) ≃ₐ[AlgebraicClosure ℚ]
          ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))
    (hstab : ∀ f, w f ∈ W ↔ f ∈ W)
    (Sr : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) ≃+* ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
    (hSr : ∀ g : ↥W, Sr (red g) = red ⟨w g, (hstab g).mpr g.2⟩)
    (Wm : GL (Fin 2) ℝ)
    (hS : ∀ (x : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) (k : ℤ)
        (f g : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k),
        coeffMap ιC (x : LaurentSeries (AlgebraicClosure ℚ)) * ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
          ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
        coeffMap ιC ((w x : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) : LaurentSeries (AlgebraicClosure ℚ)) *
            ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] Wm)) =
          ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] Wm))) :
    ∀ (k : ℤ) (f g : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
      (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries Zbar),
      IsIntegralQExp ⇑f pf → IsIntegralQExp ⇑g pg →
      PfW.map (algebraMap Zbar ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] Wm)) →
      PgW.map (algebraMap Zbar ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] Wm)) →
      intSeriesC (ResidueField ↥A) pg ≠ 0 →
      ofPowerSeries ℤ (ResidueField ↥A) (PgW.map (φκ φ A hloc)) ≠ 0 →
      ∀ x : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ),
        (x : LaurentSeries (ResidueField ↥A)) = intSeriesC (ResidueField ↥A) pf / intSeriesC (ResidueField ↥A) pg →
        ((Sr x : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A)) *
            ofPowerSeries ℤ (ResidueField ↥A) (PgW.map (φκ φ A hloc)) =
          ofPowerSeries ℤ (ResidueField ↥A) (PfW.map (φκ φ A hloc)) := by
  intro k f g pf pg D PfW PgW hf hg hPf hPg hpg hPg0 x hx
  haveI : CharZero (AlgebraicClosure ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AlgebraicClosure ℚ)).injective

  have hpgQ : intSeriesC ℚ pg ≠ 0 := intSeriesC_ne_zero_of_ne_zero hpg
  have hpgL : intSeriesC (AlgebraicClosure ℚ) pg ≠ 0 := intSeriesC_ne_zero_of_ne_zero hpg
  have hpgC : intSeriesC ℂ pg ≠ 0 := intSeriesC_ne_zero_of_ne_zero hpg
  have hr : intSeriesC ℚ pf / intSeriesC ℚ pg ∈ qExpFunctionFieldC ℚ Γ := div_mem_qExpFunctionFieldC f g hf hg hpgQ
  let X : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hr⟩
  have hXcoe : (X : LaurentSeries (AlgebraicClosure ℚ)) = intSeriesC (AlgebraicClosure ℚ) pf / intSeriesC (AlgebraicClosure ℚ) pg := by
    show coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg) = _
    rw [coeffEmb, map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
  have hup : ∀ u : PowerSeries ℤ, ofPowerSeries ℤ (AlgebraicClosure ℚ) ((u.map (Int.castRingHom ↥A)).map (algebraMap ↥A (AlgebraicClosure ℚ))) =
      intSeriesC (AlgebraicClosure ℚ) u := fun u => by rw [map_map_int]; rfl
  have hdn : ∀ u : PowerSeries ℤ, ofPowerSeries ℤ (ResidueField ↥A) ((u.map (Int.castRingHom ↥A)).map (residue ↥A)) =
      intSeriesC (ResidueField ↥A) u := fun u => by rw [map_map_int]; rfl
  have hpgA : (pg.map (Int.castRingHom ↥A)).map (residue ↥A) ≠ 0 := by
    intro h0; apply hpg; rw [← hdn, h0, map_zero]
  have hXpres : (X : LaurentSeries (AlgebraicClosure ℚ)) *
        ofPowerSeries ℤ (AlgebraicClosure ℚ) ((pg.map (Int.castRingHom ↥A)).map (algebraMap ↥A (AlgebraicClosure ℚ))) =
      ofPowerSeries ℤ (AlgebraicClosure ℚ) ((pf.map (Int.castRingHom ↥A)).map (algebraMap ↥A (AlgebraicClosure ℚ))) := by
    rw [hup, hup, hXcoe, div_mul_cancel₀ _ hpgL]
  have hXW : X ∈ W := (hW X).mpr ⟨_, _, hpgA, hXpres⟩

  have hredX : red ⟨X, hXW⟩ = x := by
    apply Subtype.ext
    have h := hpres ⟨X, hXW⟩ _ _ hpgA hXpres
    rw [hdn, hdn] at h
    rw [hx]
    exact eq_div_of_mul_eq hpg h

  have hh1 : (0 : ℝ) < 1 := one_pos
  have hDC : (((D : ℝ) : ℂ)) = (D : ℂ) := by norm_cast
  have hcoeg : ⇑((D : ℝ) • g) = (D : ℂ) • ⇑g := by
    ext τ; rw [ModularForm.coe_smul, Pi.smul_apply, Pi.smul_apply, Complex.real_smul, hDC, smul_eq_mul]
  have hcoef : ⇑((D : ℝ) • f) = (D : ℂ) • ⇑f := by
    ext τ; rw [ModularForm.coe_smul, Pi.smul_apply, Pi.smul_apply, Complex.real_smul, hDC, smul_eq_mul]
  have hqg : UpperHalfPlane.qExpansion 1 ⇑((D : ℝ) • g) = (D : ℂ) • UpperHalfPlane.qExpansion 1 ⇑g := by
    rw [hcoeg]; exact ModularForm.qExpansion_smul hh1 hΓ1 (D : ℂ) g
  have hqf : UpperHalfPlane.qExpansion 1 ⇑((D : ℝ) • f) = (D : ℂ) • UpperHalfPlane.qExpansion 1 ⇑f := by
    rw [hcoef]; exact ModularForm.qExpansion_smul hh1 hΓ1 (D : ℂ) f
  have hcoeX : coeffMap ιC (X : LaurentSeries (AlgebraicClosure ℚ)) = intSeriesC ℂ pf / intSeriesC ℂ pg := by
    rw [hXcoe, map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
  have hgexp : ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) = intSeriesC ℂ pg := by
    rw [intSeriesC, hg]
  have hfexp : ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) = intSeriesC ℂ pf := by
    rw [intSeriesC, hf]
  have hyp : coeffMap ιC (X : LaurentSeries (AlgebraicClosure ℚ)) *
        ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑((D : ℝ) • g)) =
      ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑((D : ℝ) • f)) := by
    rw [hqg, hqf, PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul, map_mul, map_mul, hgexp, hfexp, hcoeX,
      HahnSeries.ofPowerSeries_C]
    rw [mul_left_comm, div_mul_cancel₀ _ hpgC]
  have hconc := hS X k ((D : ℝ) • f) ((D : ℝ) • g) hyp
  have hsg : (⇑((D : ℝ) • g) ∣[k] Wm) = (D : ℂ) • (⇑g ∣[k] Wm) := by
    rw [hcoeg, ModularForm.smul_slash, ← hDC, UpperHalfPlane.σ_ofReal]
  have hsf : (⇑((D : ℝ) • f) ∣[k] Wm) = (D : ℂ) • (⇑f ∣[k] Wm) := by
    rw [hcoef, ModularForm.smul_slash, ← hDC, UpperHalfPlane.σ_ofReal]
  rw [hsg, hsf, ← hPg, ← hPf] at hconc

  have epull : ∀ P : PowerSeries Zbar, ofPowerSeries ℤ ℂ (P.map (algebraMap Zbar ℂ)) =
      coeffMap ιC (ofPowerSeries ℤ (AlgebraicClosure ℚ) ((P.map (toA φ A hloc)).map (algebraMap ↥A (AlgebraicClosure ℚ)))) := by
    intro P
    rw [coeffMap_ofPowerSeries, map_map', ← map_toA_spec φ A hloc P, map_map']
    rfl
  rw [epull, epull, ← map_mul] at hconc
  have hwXpres : ((w X : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) : LaurentSeries (AlgebraicClosure ℚ)) *
        ofPowerSeries ℤ (AlgebraicClosure ℚ) (((PgW.map (toA φ A hloc))).map (algebraMap ↥A (AlgebraicClosure ℚ))) =
      ofPowerSeries ℤ (AlgebraicClosure ℚ) (((PfW.map (toA φ A hloc))).map (algebraMap ↥A (AlgebraicClosure ℚ))) :=
    coeffMap_injective ιC_injective hconc
  have hPgA : (PgW.map (toA φ A hloc)).map (residue ↥A) ≠ 0 := by
    rw [map_toA_residue]; exact ofPowerSeries_ne_zero_iff.mp hPg0

  have h := hpres ⟨w X, (hstab X).mpr hXW⟩ _ _ hPgA hwXpres
  rw [map_toA_residue, map_toA_residue] at h
  rw [← hredX, hSr]
  exact h

end SpecLaw

section Main

p2m_open "ModularCurve~coeffMap_injective~coeffMap_intSeriesC IsLocalRing HahnSeries"
open scoped MatrixGroups ModularForm

theorem transport_algebraMap {Γ : Subgroup SL(2, ℤ)} (A : ValuationSubring (AlgebraicClosure ℚ))
    (W : ValuationSubring ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))
    (hWA : ∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) (a : AlgebraicClosure ℚ) ∈ W)
    (red : ↥W →+* ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
    (hpres : ∀ (f : ↥W) (x y : PowerSeries ↥A), y.map (IsLocalRing.residue ↥A) ≠ 0 →
        ((f : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) : LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (y.map (algebraMap ↥A (AlgebraicClosure ℚ)))
          = HahnSeries.ofPowerSeries ℤ (AlgebraicClosure ℚ) (x.map (algebraMap ↥A (AlgebraicClosure ℚ))) →
        ((red f : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ)) : LaurentSeries (ResidueField ↥A)) *
            HahnSeries.ofPowerSeries ℤ (ResidueField ↥A) (y.map (IsLocalRing.residue ↥A)) =
          HahnSeries.ofPowerSeries ℤ (ResidueField ↥A) (x.map (IsLocalRing.residue ↥A)))
    (w : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) ≃ₐ[AlgebraicClosure ℚ]
          ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))
    (hstab : ∀ f, w f ∈ W ↔ f ∈ W)
    (Sr : ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) ≃+* ↥(qExpFunctionFieldC (ResidueField ↥A) Γ))
    (hSr : ∀ g : ↥W, Sr (red g) = red ⟨w g, (hstab g).mpr g.2⟩) :
    ∀ c : ResidueField ↥A, Sr (algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) c) =
      algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) c := by
  have red_const : ∀ a : ↥A,
      red ⟨algebraMap (AlgebraicClosure ℚ) _ (a : (AlgebraicClosure ℚ)), hWA a⟩ =
        algebraMap (ResidueField ↥A) ↥(qExpFunctionFieldC (ResidueField ↥A) Γ) (IsLocalRing.residue ↥A a) := by
    intro a
    have h := hpres ⟨algebraMap (AlgebraicClosure ℚ) _ (a : (AlgebraicClosure ℚ)), hWA a⟩ (PowerSeries.C a) 1
      (by rw [map_one]; exact one_ne_zero)
      (by
        rw [map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]
        show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : (AlgebraicClosure ℚ)) = HahnSeries.C (a : (AlgebraicClosure ℚ))
        rw [algebraMap_laurentSeries_eq_single]
        rfl)
    rw [map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C] at h
    apply Subtype.ext
    rw [h]
    show HahnSeries.C ((IsLocalRing.residue ↥A) a) = algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) ((IsLocalRing.residue ↥A) a)
    rw [algebraMap_laurentSeries_eq_single]
    rfl
  intro c
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
  rw [← red_const a, hSr]
  congr 1
  exact Subtype.ext (w.commutes (a : (AlgebraicClosure ℚ)))

end Main

end FrickePairAsm
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_intertwines_heckeAlphaModLH_heckeBetaModLH_and_reduction_slash_fricke.FrickePairAsm"

p2m_open "ModularCurve~coeffMap_injective~coeffMap_intSeriesC" in open  IsLocalRing HahnSeries FrickePairAsm in
open scoped MatrixGroups ModularForm in
set_option maxHeartbeats 3200000 in
theorem solution
    (p Q : ℕ) [Fact p.Prime] [NeZero Q] (hpQ : ¬ p ∣ Q) (H' : Subgroup (ZMod Q)ˣ)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p]
    (φ : ↥(integralClosure ℤ ℂ) →+* K)
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p)
    (WQ : GL (Fin 2) ℝ) (hWQ : (WQ : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (Q : ℝ), 0])
    (WQq : GL (Fin 2) ℝ) (hWQq : (WQq : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; ((Q * q : ℕ) : ℝ), 0]) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    ∃ (σ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H')) ≃ₐ[K]
            ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H')))
      (τ : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))) ≃ₐ[K]
            ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)))),

      (∀ x, τ (ModularCurve.heckeAlphaModLH K Q H' q x) = ModularCurve.heckeBetaModLH K Q H' q (σ x)) ∧

      (∀ x, τ (ModularCurve.heckeBetaModLH K Q H' q x) = ModularCurve.heckeAlphaModLH K Q H' q (σ x)) ∧

      (∀ x, σ (σ x) = x) ∧

      (∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH Q H' : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQ)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQ)) →
          ModularCurve.intSeriesC K pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ K (PgW.map φ) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H')),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg →
            ((σ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H'))) : LaurentSeries K) *
                HahnSeries.ofPowerSeries ℤ K (PgW.map φ) =
              HahnSeries.ofPowerSeries ℤ K (PfW.map φ)) ∧

      (∀ (k : ℤ) (f g : ModularForm ((CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q) :
              Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
          (pf pg : PowerSeries ℤ) (D : ℕ) (PfW PgW : PowerSeries ↥(integralClosure ℤ ℂ)),
          ModularCurve.IsIntegralQExp ⇑f pf → ModularCurve.IsIntegralQExp ⇑g pg →
          PfW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑f ∣[k] WQq)) →
          PgW.map (algebraMap ↥(integralClosure ℤ ℂ) ℂ) = UpperHalfPlane.qExpansion 1 ((D : ℂ) • (⇑g ∣[k] WQq)) →
          ModularCurve.intSeriesC K pg ≠ 0 →
          HahnSeries.ofPowerSeries ℤ K (PgW.map φ) ≠ 0 →
          ∀ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))),
            (x : LaurentSeries K) = ModularCurve.intSeriesC K pf / ModularCurve.intSeriesC K pg →
            ((τ x : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)))) :
                  LaurentSeries K) *
                HahnSeries.ofPowerSeries ℤ K (PgW.map φ) =
              HahnSeries.ofPowerSeries ℤ K (PfW.map φ))  := by
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hp : p.Prime := Fact.out
  have hpq : p ≠ q := fun h => hqp h.symm
  have hQK : ((Q : ℕ) : K) ≠ 0 := fun h => hpQ ((CharP.cast_eq_zero_iff K p Q).mp h)
  have hqK : ((q : ℕ) : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K p] at h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp h).symm
  have hpQq : ¬ p ∣ Q * q := by
    intro h
    rcases hp.dvd_mul.mp h with h1 | h2
    · exact hpQ h1
    · exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h2)

  obtain ⟨A, hA, hloc⟩ := FrickePairAsm.exists_place p φ
  haveI hcharκ : CharP (ResidueField ↥A) p := ValuationSubring.residueField_charP_of_liesOverPrime A hp hA
  haveI : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  letI : Algebra (ResidueField ↥A) K := (FrickePairAsm.θ φ A hloc).toAlgebra
  have hφ : (algebraMap (ResidueField ↥A) K).comp (FrickePairAsm.φκ φ A hloc) = φ := FrickePairAsm.θ_comp_φκ φ A hloc

  obtain ⟨w, w', hS0, hS0', h1, h2, h3, h3'⟩ :=
    ModularCurve.exists_algEquiv_pair_xHFunctionFieldBar_slash_fricke_intertwines_heckeAlphaHBar_heckeBetaHBar
      Q H' q FrickePairAsm.ιC WQ hWQ WQq hWQq

  have hTΓf : ModularGroup.T ∈ (CohCarrier.GammaH Q H') := translation_mem_GammaH Q H'
  have hTΓr : ModularGroup.T ∈ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)) := Subgroup.mem_inf.mpr ⟨translation_mem_GammaH Q H', by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.coe_T]⟩
  haveI hΓffi : (CohCarrier.GammaH Q H').FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH Q H')
  have hΓrH : (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)) = CohCarrier.GammaH (Q * q) (H'.comap (ZMod.unitsMap (dvd_mul_right Q q))) :=
    CohCarrier.gammaH_inf_gamma0_mul_eq_gammaH_comap_unitsMap Q q H'
  haveI hΓrfi : (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)).FiniteIndex := by
    rw [hΓrH]; exact Subgroup.finiteIndex_of_le (Gamma1_le_GammaH (Q * q) _)
  obtain ⟨W, hW, hWA, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC_of_liesOverPrime (CohCarrier.GammaH Q H') hTΓf p A hA
  obtain ⟨W', hW', hW'A, -⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_qExpFunctionFieldC_of_liesOverPrime (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)) hTΓr p A hA

  let jx : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH Q H'))) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (intFormRatiosC_subset ℚ _ (jqModC_mem_intFormRatiosC ℚ _))⟩
  have hjx : ((jx : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH Q H')))) : LaurentSeries (AlgebraicClosure ℚ)) =
      jqModC (AlgebraicClosure ℚ) := by
    show (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)
    exact map_jqModC _
  let jx' : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)))) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (intFormRatiosC_subset ℚ _ (jqModC_mem_intFormRatiosC ℚ _))⟩
  have hjx' : ((jx' : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))))) : LaurentSeries (AlgebraicClosure ℚ)) =
      jqModC (AlgebraicClosure ℚ) := by
    show (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)
    exact map_jqModC _
  have hwjx := ModularCurve.coe_apply_eq_qExpand_jqModC_of_forall_coeffMap_mul_qExpansion_slash_fricke_eq
    (CohCarrier.GammaH Q H') Q FrickePairAsm.ιC WQ hWQ w hS0 jx hjx
  have hwjx' := ModularCurve.coe_apply_eq_qExpand_jqModC_of_forall_coeffMap_mul_qExpansion_slash_fricke_eq
    (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)) (Q * q) FrickePairAsm.ιC WQq hWQq w' hS0' jx' hjx'
  have hstab : ∀ f, w f ∈ W ↔ f ∈ W :=
    ModularCurve.forall_apply_mem_gaussValuationSubring_iff_of_apply_jqModC_eq_qExpand_of_liesOverPrime
      p Q H' hpQ (CohCarrier.GammaH Q H') rfl A hA Q jx (w jx) hjx hwjx W hW w rfl (h3 jx)
  have hstab' : ∀ f, w' f ∈ W' ↔ f ∈ W' :=
    ModularCurve.forall_apply_mem_gaussValuationSubring_iff_of_apply_jqModC_eq_qExpand_of_liesOverPrime
      p (Q * q) (H'.comap (ZMod.unitsMap (dvd_mul_right Q q))) hpQq (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)) hΓrH A hA (Q * q) jx' (w' jx') hjx' hwjx' W' hW' w' rfl (h3' jx')

  have hin := ModularCurve.heckeDiamondInputsHAll Q H'
  obtain ⟨hβ0, -⟩ := hin.heckeInputsHAlong q hq
  have hβκ := ModularCurve.heckeBetaModLHDefined (ResidueField ↥A) Q H' q
  obtain ⟨red, red', hpres, hpres', hsurj, hsurj', hker, hker', hαc, hβc⟩ :=
    ModularCurve.exists_gaussReduction_pair_surjective_ker_heckeAlpha_heckeBeta_of_liesOverPrime_xHTop
      p Q H' q hpQ hpq hβ0 A hA hβκ W hW W' hW'

  obtain ⟨Sr, hSr⟩ := FrickePairAsm.exists_transport W red hsurj hker w.toRingEquiv (fun f => hstab f)
  obtain ⟨Tr, hTr⟩ := FrickePairAsm.exists_transport W' red' hsurj' hker' w'.toRingEquiv (fun f => hstab' f)
  have Sr_alg := transport_algebraMap A W hWA red hpres w hstab Sr hSr
  have Tr_alg := transport_algebraMap A W' hW'A red' hpres' w' hstab' Tr hTr
  let σκ : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH Q H')) ≃ₐ[ResidueField ↥A] ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH Q H')) :=
    AlgEquiv.ofRingEquiv (f := Sr) Sr_alg
  let τκ : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))) ≃ₐ[ResidueField ↥A] ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q))) :=
    AlgEquiv.ofRingEquiv (f := Tr) Tr_alg
  have σκ_red : ∀ g : ↥W, σκ (red g) = red ⟨w.toRingEquiv g.1, (hstab _).mpr g.2⟩ := hSr
  have τκ_red : ∀ g : ↥W', τκ (red' g) = red' ⟨w'.toRingEquiv g.1, (hstab' _).mpr g.2⟩ := hTr

  have law1 : ∀ x, τκ (heckeAlphaModLH (ResidueField ↥A) Q H' q x) = heckeBetaModLH (ResidueField ↥A) Q H' q (σκ x) := by
    intro x
    obtain ⟨f, rfl⟩ := hsurj x
    obtain ⟨hαf, hα'⟩ := hαc f
    obtain ⟨hβg, hβ'⟩ := hβc ⟨w.toRingEquiv f.1, (hstab _).mpr f.2⟩
    rw [← hα', τκ_red, σκ_red, ← hβ']
    congr 1
    exact Subtype.ext (h1 f)
  have law2 : ∀ x, τκ (heckeBetaModLH (ResidueField ↥A) Q H' q x) = heckeAlphaModLH (ResidueField ↥A) Q H' q (σκ x) := by
    intro x
    obtain ⟨f, rfl⟩ := hsurj x
    obtain ⟨hβf, hβ'⟩ := hβc f
    obtain ⟨hαg, hα'⟩ := hαc ⟨w.toRingEquiv f.1, (hstab _).mpr f.2⟩
    rw [← hβ', τκ_red, σκ_red, ← hα']
    congr 1
    exact Subtype.ext (h2 f)
  have law2' : ∀ x, σκ (σκ x) = x := by
    intro x
    obtain ⟨f, rfl⟩ := hsurj x
    rw [σκ_red, σκ_red]
    congr 1
    exact Subtype.ext (h3 f)

  have hΓf1 : (1 : ℝ) ∈ (((CohCarrier.GammaH Q H') : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hTΓf]; exact AddSubgroup.mem_zmultiples _
  have hΓr1 : (1 : ℝ) ∈ (((CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hTΓr]; exact AddSubgroup.mem_zmultiples _
  have lawS := FrickePairAsm.lawS_of φ A hloc (CohCarrier.GammaH Q H') hΓf1 W hW red hpres w hstab Sr hSr WQ hS0
  have lawS' := FrickePairAsm.lawS_of φ A hloc (CohCarrier.GammaH Q H' ⊓ CongruenceSubgroup.Gamma0 (Q * q)) hΓr1 W' hW' red' hpres' w' hstab' Tr hTr WQq hS0'

  obtain ⟨σ, τ, hK⟩ :=
    ModularCurve.exists_algEquiv_pair_qExpFunctionFieldC_laws_of_algEquiv_pair_laws_of_algebra_of_charP
      p Q H' K (ResidueField ↥A) q hq hQK hqK hβκ (ModularCurve.heckeBetaModLHDefined K Q H' q)
      (FrickePairAsm.φκ φ A hloc) WQ hWQ WQq hWQq σκ τκ ⟨law1, law2, law2', lawS, lawS'⟩
  rw [hφ] at hK
  exact ⟨σ, τ, hK⟩

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_intertwines_heckeAlphaModLH_heckeBetaModLH_and_reduction_slash_fricke.FrickePairAsm"

end S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_intertwines_heckeAlphaModLH_heckeBetaModLH_and_reduction_slash_fricke
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_pair_qExpFunctionFieldC_intertwines_heckeAlphaModLH_heckeBetaModLH_and_reduction_slash_fricke (solution)
