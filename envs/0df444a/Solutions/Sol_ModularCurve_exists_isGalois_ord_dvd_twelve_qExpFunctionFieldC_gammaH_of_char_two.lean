-- Prove2me | solution 1 for ModularCurve.exists_isGalois_ord_dvd_twelve_qExpFunctionFieldC_gammaH_of_char_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ddf56daf-9d41-5588-b020-5d56aace8382

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_ModularCurve_exists_natural_algHom_qExpFunctionFieldC_gamma1_of_transcendental_j
import Theorems.Thm_AlgebraicCurve_Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois
import Theorems.Thm_ModularCurve_exists_equivariant_torsion_reduction_ofJ
import Theorems.Thm_WeierstrassCurve_Affine_Point_vcInvFun_add
import Theorems.Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isGalois_ord_dvd_twelve_qExpFunctionFieldC_gammaH_of_char_two
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero"
p2m_attr_erase "simp" "ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

open WeierstrassCurve WeierstrassCurve.Affine ModularCurve AlgebraicCurve
open scoped IntermediateField Polynomial

noncomputable section

namespace P2MKcGH12

universe u

section E0

variable (K : Type*) [Field K] [CharP K 2]

lemma two_eq_zero : (2 : K) = 0 := by
  simpa using CharP.cast_eq_zero K 2

lemma three_eq_one : (3 : K) = 1 := by
  linear_combination two_eq_zero K

def E0 : WeierstrassCurve K := ⟨0, 0, 1, 0, 0⟩

lemma E0_Δ : (E0 K).Δ = 1 := by
  have h2 := two_eq_zero K
  simp only [E0, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  linear_combination (-14 : K) * h2

scoped instance E0_isElliptic : (E0 K).IsElliptic := ⟨by rw [E0_Δ]; exact isUnit_one⟩

lemma E0_j : (E0 K).j = 0 := by
  have hc4 : (E0 K).c₄ = 0 := by
    simp only [E0, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  rw [WeierstrassCurve.j, hc4]; ring

variable {K}

lemma smul_E0_eq_iff (γ : VariableChange K) :
    γ • E0 K = E0 K ↔
      (γ.u : K) ^ 3 = 1 ∧ γ.r = γ.s ^ 2 ∧ γ.s ^ 4 = γ.s ∧ γ.t ^ 2 + γ.t = γ.s ^ 6 := by
  have h2 := two_eq_zero K
  have h3K := three_eq_one K
  set v : K := ((γ.u⁻¹ : Kˣ) : K) with hv_def
  have hv : v ≠ 0 := (γ.u⁻¹).ne_zero
  have hvu : v * (γ.u : K) = 1 := by simp [hv_def]
  constructor
  · intro h
    have e1 := congrArg WeierstrassCurve.a₂ h
    have e3 := congrArg WeierstrassCurve.a₃ h
    have e4 := congrArg WeierstrassCurve.a₄ h
    have e6 := congrArg WeierstrassCurve.a₆ h
    simp only [variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆, E0, h2,
      h3K, mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub, mul_one, one_mul] at e1 e3 e4 e6
    rw [← hv_def] at e1 e3 e4 e6
    have e1' := (mul_eq_zero.mp e1).resolve_left (pow_ne_zero 2 hv)
    have e4' := (mul_eq_zero.mp e4).resolve_left (pow_ne_zero 4 hv)
    have e6' := (mul_eq_zero.mp e6).resolve_left (pow_ne_zero 6 hv)
    have hr : γ.r = γ.s ^ 2 := by linear_combination e1'
    refine ⟨?_, hr, ?_, ?_⟩
    · linear_combination (-(γ.u : K) ^ 3) * e3 + ((v * γ.u) ^ 2 + v * γ.u + 1) * hvu
    · linear_combination e4' - (γ.r + γ.s ^ 2) * hr
    · linear_combination -e6' + (γ.r ^ 2 + γ.r * γ.s ^ 2 + γ.s ^ 4) * hr
  · rintro ⟨hu3, hr, hs4, ht⟩
    have hv3 : v ^ 3 = 1 := by
      linear_combination (-(v ^ 3)) * hu3 + ((v * γ.u) ^ 2 + v * γ.u + 1) * hvu
    ext
    · simp only [variableChange_a₁, E0]
      rw [← hv_def]
      linear_combination v * γ.s * h2
    · simp only [variableChange_a₂, E0]
      rw [← hv_def]
      linear_combination 3 * v ^ 2 * hr + v ^ 2 * γ.s ^ 2 * h2
    · simp only [variableChange_a₃, E0]
      rw [← hv_def]
      linear_combination hv3 + v ^ 3 * γ.t * h2
    · simp only [variableChange_a₄, E0]
      rw [← hv_def]
      linear_combination (3 * v ^ 4 * (γ.r + γ.s ^ 2)) * hr + 3 * v ^ 4 * hs4
        + v ^ 4 * γ.s * (1 - γ.t) * h2
    · simp only [variableChange_a₆, E0]
      rw [← hv_def]
      linear_combination v ^ 6 * (γ.r ^ 2 + γ.r * γ.s ^ 2 + γ.s ^ 4) * hr - v ^ 6 * ht

variable (K) in

def negE0 : VariableChange K := ⟨1, 0, 0, 1⟩

lemma negE0_smul : negE0 K • E0 K = E0 K := by
  rw [smul_E0_eq_iff]
  refine ⟨by simp [negE0], by simp [negE0], by simp [negE0], ?_⟩
  simp only [negE0]
  linear_combination two_eq_zero K

lemma negE0_ne_one : negE0 K ≠ 1 := by
  intro h
  have := congrArg VariableChange.t h
  simp [negE0, VariableChange.one_def] at this

lemma negE0_mul_self : negE0 K * negE0 K = 1 := by
  rw [VariableChange.mul_def, VariableChange.one_def]
  apply VariableChange.ext
  · simp [negE0]
  · simp [negE0]
  · simp [negE0]
  · simp only [negE0, Units.val_one, one_pow, mul_one, mul_zero, add_zero]
    linear_combination two_eq_zero K

lemma vcXInv_negE0 (x : K) : vcXInv (negE0 K) x = x := by
  simp [vcXInv, negE0]

lemma vcYInv_negE0 (x y : K) : vcYInv (negE0 K) x y = (E0 K).toAffine.negY x y := by
  simp only [vcYInv, negE0, Affine.negY, inv_one, Units.val_one, one_pow, one_mul, zero_mul,
    sub_zero, E0]
  linear_combination y * two_eq_zero K

end E0

section Count

variable {K : Type*} [Field K] [CharP K 2] [IsAlgClosed K]

lemma natCard_eq_natDegree {p : K[X]} (hsep : p.Separable) (S : Set K)
    (hS : ∀ x, x ∈ S ↔ Polynomial.aeval x p = 0) : Nat.card S = p.natDegree := by
  have hp : p ≠ 0 := hsep.ne_zero
  have hS' : S = p.rootSet K := by
    ext x
    rw [hS, Polynomial.mem_rootSet]
    exact ⟨fun h => ⟨hp, h⟩, fun h => h.2⟩
  rw [hS', Nat.card_eq_fintype_card]
  exact Polynomial.card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _)

lemma natCard_cube_eq_one : Nat.card {x : K // x ^ 3 = 1} = 3 := by
  have h3 : ((3 : ℕ) : K) ≠ 0 := by
    rw [Nat.cast_ofNat, three_eq_one K]; exact one_ne_zero
  have hsep : (Polynomial.X ^ 3 - Polynomial.C (1 : K)).Separable := Polynomial.separable_X_pow_sub_C 1 h3 one_ne_zero
  have := natCard_eq_natDegree hsep {x : K | x ^ 3 = 1} (fun x => by
    simp only [Set.mem_setOf_eq, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      map_one]
    exact sub_eq_zero.symm)
  rw [Polynomial.natDegree_X_pow_sub_C] at this
  exact this

lemma natCard_units_cube_eq_one : Nat.card {u : Kˣ // (u : K) ^ 3 = 1} = 3 := by
  have e : {u : Kˣ // (u : K) ^ 3 = 1} ≃ {x : K // x ^ 3 = 1} :=
    { toFun := fun u => ⟨u.1, u.2⟩
      invFun := fun x => ⟨Units.mk0 x.1 (by
          intro h; have := x.2; rw [h] at this; norm_num at this), x.2⟩
      left_inv := fun u => Subtype.ext (Units.ext rfl)
      right_inv := fun x => rfl }
  rw [Nat.card_congr e, natCard_cube_eq_one]

lemma natCard_pow_four_eq_self : Nat.card {s : K // s ^ 4 = s} = 4 := by
  have h2 := two_eq_zero K
  have hsep : (Polynomial.X ^ 4 - Polynomial.X : K[X]).Separable := by
    rw [Polynomial.separable_def']
    refine ⟨0, -1, ?_⟩
    have hd : Polynomial.derivative (Polynomial.X ^ 4 - Polynomial.X : K[X]) = -1 := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
      have : (Polynomial.C ((4 : ℕ) : K) : K[X]) = 0 := by
        rw [show ((4 : ℕ) : K) = 2 * 2 by norm_num, h2, mul_zero, map_zero]
      rw [this, zero_mul, zero_sub]
    rw [hd]; ring
  have := natCard_eq_natDegree hsep {s : K | s ^ 4 = s} (fun x => by
    simp only [Set.mem_setOf_eq, map_sub, map_pow, Polynomial.aeval_X]
    exact sub_eq_zero.symm)
  rw [show (Polynomial.X ^ 4 - Polynomial.X : K[X]).natDegree = 4 by compute_degree!] at this
  exact this

lemma natCard_artinSchreier (c : K) : Nat.card {t : K // t ^ 2 + t = c} = 2 := by
  have h2 := two_eq_zero K
  have hsep : (Polynomial.X ^ 2 + Polynomial.X - Polynomial.C c : K[X]).Separable := by
    rw [Polynomial.separable_def']
    refine ⟨0, 1, ?_⟩
    have hd : Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.X - Polynomial.C c : K[X]) = 1 := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_add, Polynomial.derivative_X_pow,
        Polynomial.derivative_X, Polynomial.derivative_C]
      have : (Polynomial.C ((2 : ℕ) : K) : K[X]) = 0 := by
        rw [Nat.cast_ofNat, h2, map_zero]
      rw [this, zero_mul, zero_add, sub_zero]
    rw [hd]; ring
  have := natCard_eq_natDegree hsep {t : K | t ^ 2 + t = c} (fun x => by
    simp only [Set.mem_setOf_eq, map_sub, map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    exact sub_eq_zero.symm)
  rw [show (Polynomial.X ^ 2 + Polynomial.X - Polynomial.C c : K[X]).natDegree = 2 by compute_degree!] at this
  exact this

lemma exists_artinSchreier_root (c : K) : ∃ t : K, t ^ 2 + t = c := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X - Polynomial.C c : K[X]) (by
    rw [show (Polynomial.X ^ 2 + Polynomial.X - Polynomial.C c : K[X]).degree = 2 by compute_degree!]; norm_num)
  refine ⟨t, ?_⟩
  have : t ^ 2 + t - c = 0 := by simpa using ht
  linear_combination this

variable (K) in

def asRoot (c : K) : K := Classical.choose (exists_artinSchreier_root (c ^ 6))

lemma asRoot_spec (c : K) : asRoot K c ^ 2 + asRoot K c = c ^ 6 :=
  Classical.choose_spec (exists_artinSchreier_root (c ^ 6))

variable (K) in

abbrev Stab : Subgroup (VariableChange K) := MulAction.stabilizer (VariableChange K) (E0 K)

def stabEquiv : Stab K ≃
    {u : Kˣ // (u : K) ^ 3 = 1} × {s : K // s ^ 4 = s} × {τ : K // τ ^ 2 + τ = 0} where
  toFun γ :=
    have h := (smul_E0_eq_iff γ.1).mp γ.2
    (⟨γ.1.u, h.1⟩, ⟨γ.1.s, h.2.2.1⟩, ⟨γ.1.t - asRoot K γ.1.s, by
      linear_combination h.2.2.2 - asRoot_spec γ.1.s
        + (asRoot K γ.1.s ^ 2 - γ.1.t * asRoot K γ.1.s) * two_eq_zero K⟩)
  invFun x := ⟨⟨x.1.1, x.2.1.1 ^ 2, x.2.1.1, x.2.2.1 + asRoot K x.2.1.1⟩,
    (smul_E0_eq_iff _).mpr ⟨x.1.2, rfl, x.2.1.2, by
      linear_combination x.2.2.2 + asRoot_spec x.2.1.1
        + x.2.2.1 * asRoot K x.2.1.1 * two_eq_zero K⟩⟩
  left_inv γ := by
    have h := (smul_E0_eq_iff γ.1).mp γ.2
    apply Subtype.ext
    apply VariableChange.ext
    · rfl
    · exact h.2.1.symm
    · rfl
    · show γ.1.t - asRoot K γ.1.s + asRoot K γ.1.s = γ.1.t
      ring
  right_inv x := by
    ext
    · rfl
    · rfl
    · show x.2.2.1 + asRoot K x.2.1.1 - asRoot K x.2.1.1 = x.2.2.1
      ring

theorem natCard_stab : Nat.card (Stab K) = 24 := by
  rw [Nat.card_congr stabEquiv, Nat.card_prod, Nat.card_prod, natCard_units_cube_eq_one,
    natCard_pow_four_eq_self, natCard_artinSchreier]

scoped instance finite_stab : Finite (Stab K) := Nat.finite_of_card_ne_zero (by rw [natCard_stab]; norm_num)

variable (K) in

def negS : Stab K := ⟨negE0 K, negE0_smul⟩

lemma orderOf_negS : orderOf (negS K) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · exact Subtype.ext (by rw [pow_two]; exact negE0_mul_self)
  · intro h; exact negE0_ne_one (congrArg Subtype.val h)

variable (K) in

def Zneg : Subgroup (Stab K) := Subgroup.zpowers (negS K)

lemma natCard_Zneg : Nat.card (Zneg K) = 2 := by
  rw [Zneg, Nat.card_zpowers, orderOf_negS]

theorem index_Zneg : (Zneg K).index = 12 := by
  have h := (Zneg K).card_mul_index
  rw [natCard_Zneg, natCard_stab] at h
  omega

end Count

section AutPt

variable {L : Type*} [Field L] [DecidableEq L]

def px {W : Affine L} : W.Point → Option (L × L)
  | 0 => none
  | .some x y _ => some (x, y)

lemma px_injective {W : Affine L} : Function.Injective (px (W := W)) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hpx
  · rfl
  · simp [px] at hpx
  · simp [px] at hpx
  · simp only [px, Option.some.injEq, Prod.mk.injEq] at hpx
    obtain ⟨rfl, rfl⟩ := hpx
    rfl

lemma px_neg {W : Affine L} (P : W.Point) :
    px (-P) = (px P).map (fun q => (q.1, W.negY q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some]; rfl

def castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst e; exact AddEquiv.refl _

theorem castPt_eq_iff_heq {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₁.toAffine.Point)
    (Q : W₂.toAffine.Point) : castPt e P = Q ↔ HEq P Q := by
  subst e; exact Iff.rfl.trans heq_iff_eq.symm

lemma px_castPt {W₁ W₂ : WeierstrassCurve L} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    px (castPt e P) = px P := by
  subst e; rfl

def autPt {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point :=
  (castPt hγ).toAddMonoidHom.comp
    (AddMonoidHom.mk' (Point.vcInvFun γ W.toAffine) (Point.vcInvFun_add γ W.toAffine))

theorem autPt_apply {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P : W.toAffine.Point) : autPt γ hγ P = castPt hγ (Point.vcInvFun γ W.toAffine P) := rfl

theorem autPt_eq_iff_heq {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P Q : W.toAffine.Point) : autPt γ hγ P = Q ↔ HEq (Point.vcInvFun γ W.toAffine P) Q := by
  rw [autPt_apply, castPt_eq_iff_heq]

lemma px_autPt {W : WeierstrassCurve L} (γ : VariableChange L) (hγ : γ • W = W)
    (P : W.toAffine.Point) :
    px (autPt γ hγ P) = (px P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [show (Point.zero : W.toAffine.Point) = 0 from rfl, map_zero]; rfl
  · rw [autPt_apply, px_castPt]; rfl

lemma vcXInv_mul (C C' : VariableChange L) (x : L) :
    vcXInv (C * C') x = vcXInv C (vcXInv C' x) := by
  have hu : (C.u : L) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : L) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

lemma vcYInv_mul (C C' : VariableChange L) (x y : L) :
    vcYInv (C * C') x y = vcYInv C (vcXInv C' x) (vcYInv C' x y) := by
  have hu : (C.u : L) ≠ 0 := C.u.ne_zero
  have hu' : (C'.u : L) ≠ 0 := C'.u.ne_zero
  simp only [vcXInv, vcYInv, VariableChange.mul_def, Units.val_inv_eq_inv_val, Units.val_mul]
  field_simp
  ring

lemma vcXInv_one (x : L) : vcXInv (1 : VariableChange L) x = x := by
  simp [vcXInv, VariableChange.one_def]

lemma vcYInv_one (x y : L) : vcYInv (1 : VariableChange L) x y = y := by
  simp [vcYInv, VariableChange.one_def]

theorem autPt_one {W : WeierstrassCurve L} (h1 : (1 : VariableChange L) • W = W)
    (P : W.toAffine.Point) : autPt 1 h1 P = P := by
  apply px_injective
  rw [px_autPt]
  rcases px P with _ | ⟨x, y⟩
  · rfl
  · simp [vcXInv_one, vcYInv_one]

theorem autPt_mul {W : WeierstrassCurve L} (γ γ' : VariableChange L) (hγ : γ • W = W)
    (hγ' : γ' • W = W) (hm : (γ * γ') • W = W) (P : W.toAffine.Point) :
    autPt (γ * γ') hm P = autPt γ hγ (autPt γ' hγ' P) := by
  apply px_injective
  rw [px_autPt, px_autPt, px_autPt]
  rcases px P with _ | ⟨x, y⟩
  · rfl
  · simp [vcXInv_mul, vcYInv_mul]

end AutPt

section AutPtE0

variable {K : Type*} [Field K] [DecidableEq K] [CharP K 2]

theorem autPt_negE0 (Q : (E0 K).toAffine.Point) : autPt (negE0 K) negE0_smul Q = -Q := by
  apply px_injective
  rw [px_autPt, px_neg]
  rcases px Q with _ | ⟨x, y⟩
  · rfl
  · simp only [Option.map_some, vcXInv_negE0, vcYInv_negE0]

end AutPtE0

section PM

variable {G : Type*} [Group G] {P : Type*} [AddCommGroup P]
  (act : G → P →+ P) (h1 : ∀ x, act 1 x = x) (hmul : ∀ g h x, act (g * h) x = act g (act h x))
  (N : ℕ)

def IsPM (g : G) : Prop :=
  (∀ x : P, N • x = 0 → act g x = x) ∨ (∀ x : P, N • x = 0 → act g x = -x)

lemma nsmul_act_eq_zero (g : G) {x : P} (hx : N • x = 0) : N • act g x = 0 := by
  rw [← map_nsmul, hx, map_zero]

include h1 hmul in
lemma act_inv_act (g : G) (x : P) : act g (act g⁻¹ x) = x := by
  rw [← hmul, mul_inv_cancel, h1]

include h1 hmul in
lemma isPM_inv {g : G} (hg : IsPM act N g) : IsPM act N g⁻¹ := by
  rcases hg with hg | hg
  · refine Or.inl fun x hx => ?_
    have h := hg (act g⁻¹ x) (nsmul_act_eq_zero act N g⁻¹ hx)
    rw [act_inv_act act h1 hmul] at h
    exact h.symm
  · refine Or.inr fun x hx => ?_
    have h := hg (act g⁻¹ x) (nsmul_act_eq_zero act N g⁻¹ hx)
    rw [act_inv_act act h1 hmul] at h
    rw [← neg_eq_iff_eq_neg.mpr h]

include hmul in
lemma isPM_mul {g h : G} (hg : IsPM act N g) (hh : IsPM act N h) : IsPM act N (g * h) := by
  rcases hg with hg | hg <;> rcases hh with hh | hh
  · exact Or.inl fun x hx => by rw [hmul, hh x hx, hg x hx]
  · exact Or.inr fun x hx => by rw [hmul, hh x hx, map_neg, hg x hx]
  · exact Or.inr fun x hx => by rw [hmul, hh x hx, hg x hx]
  · exact Or.inl fun x hx => by rw [hmul, hh x hx, map_neg, hg x hx, neg_neg]

def pmSubgroup : Subgroup G where
  carrier := {g | IsPM act N g}
  one_mem' := Or.inl fun x _ => h1 x
  mul_mem' hg hh := isPM_mul act hmul N hg hh
  inv_mem' hg := isPM_inv act h1 hmul N hg

lemma mem_pmSubgroup_iff (g : G) : g ∈ pmSubgroup act h1 hmul N ↔ IsPM act N g := Iff.rfl

theorem pmSubgroup_normal : (pmSubgroup act h1 hmul N).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_pmSubgroup_iff] at hn ⊢
  rcases hn with hn | hn
  · refine Or.inl fun x hx => ?_
    rw [hmul, hmul, hn _ (nsmul_act_eq_zero act N g⁻¹ hx), act_inv_act act h1 hmul]
  · refine Or.inr fun x hx => ?_
    rw [hmul, hmul, hn _ (nsmul_act_eq_zero act N g⁻¹ hx), map_neg, act_inv_act act h1 hmul]

end PM

section Frame

variable (K E M : Type*) [Field K] [Field E] [Field M]
  [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]

def toSemilinear : (M ≃ₐ[E] M) →* SemilinearAut K M where
  toFun σ := SemilinearAut.ofAlgAut (σ.restrictScalars K)
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl

variable {K E M}

def decomp (W₀ : Place K M) : Subgroup (M ≃ₐ[E] M) :=
  (MulAction.stabilizer (SemilinearAut K M) W₀).comap (toSemilinear K E M)

lemma mem_decomp_iff (W₀ : Place K M) (σ : M ≃ₐ[E] M) :
    σ ∈ decomp (E := E) W₀ ↔ SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ := Iff.rfl

theorem isIntegral_of_apply_eq {F : Type*} [Field F] [Algebra K F]
    (x : F) (t : M) [FiniteDimensional K⟮t⟯ M] (ψ : F →ₐ[K] M) (hψ : ψ x = t) :
    ψ.toRingHom.IsIntegral := by
  intro y
  have hy : IsIntegral K⟮t⟯ y := Algebra.IsIntegral.isIntegral y
  obtain ⟨q, hqm, hq0⟩ := hy
  have hle : K⟮t⟯ ≤ ψ.fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact ⟨x, hψ⟩
  have hlifts : q.map (algebraMap K⟮t⟯ M) ∈ Polynomial.lifts ψ.toRingHom := by
    refine (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ?_
    rw [Polynomial.coeff_map]
    obtain ⟨f, hf⟩ := hle (q.coeff n).2
    exact ⟨f, hf⟩
  obtain ⟨q', hq'map, -, hq'monic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts (hqm.map _)
  refine ⟨q', hq'monic, ?_⟩
  rw [← Polynomial.eval_map, hq'map, Polynomial.eval_map]
  exact hq0

end Frame

section Torsion

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] (N : ℕ)

def tors (A : Type*) [AddCommGroup A] (N : ℕ) : Set A := {x | N • x = 0}

abbrev CycSub (A : Type*) [AddCommGroup A] (N : ℕ) : Type _ :=
  {H : AddSubgroup A // IsAddCyclic H ∧ Nat.card H = N}

variable {N}

def cycOf (g : A) (hg : addOrderOf g = N) : CycSub A N :=
  ⟨AddSubgroup.zmultiples g, ⟨⟨g, AddSubgroup.mem_zmultiples g⟩, fun y => by
      obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp y.2
      exact ⟨n, Subtype.ext (by simpa using hn)⟩⟩, by rw [Nat.card_zmultiples, hg]⟩

theorem nsmul_eq_zero_of_mem (H : CycSub A N) {x : A} (hx : x ∈ H.1) : N • x = 0 := by
  have h : Nat.card H.1 • (⟨x, hx⟩ : H.1) = 0 := card_nsmul_eq_zero'
  rw [H.2.2] at h
  exact congrArg Subtype.val h

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K]

theorem tors_facts (E₀ : WeierstrassCurve K) [E₀.IsElliptic] {N : ℕ} [NeZero N] (hN : (N : K) ≠ 0) :
    Nat.card (tors E₀.toAffine.Point N) = N ^ 2 ∧ ∃ g : E₀.toAffine.Point, addOrderOf g = N := by
  obtain ⟨eT⟩ := WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    (F := K) (K := K) E₀ hN
  have hb : (E₀⁄K) = E₀.toAffine := by
    show (E₀.baseChange K).toAffine = E₀.toAffine
    rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  rw [hb] at eT
  have hmem : ∀ P : E₀.toAffine.Point,
      P ∈ Submodule.torsionBy ℤ E₀.toAffine.Point N ↔ P ∈ tors _ N := by
    intro P
    rw [Submodule.mem_torsionBy_iff]
    show ((N : ℤ) • P = 0) ↔ N • P = 0
    rw [natCast_zsmul]
  have hset : (Submodule.torsionBy ℤ E₀.toAffine.Point N : Set E₀.toAffine.Point) = tors _ N :=
    Set.ext hmem
  constructor
  · have h1 : Nat.card (Submodule.torsionBy ℤ E₀.toAffine.Point N) = N ^ 2 := by
      rw [← Nat.card_congr eT.toEquiv, Nat.card_prod, Nat.card_zmod, sq]
    rw [← SetLike.coe_sort_coe, hset] at h1
    exact h1
  · refine ⟨(eT (1, 0)).1, ?_⟩
    have h1 : addOrderOf ((eT (1, 0)).1) = addOrderOf (eT (1, 0)) :=
      addOrderOf_injective (Submodule.torsionBy ℤ E₀.toAffine.Point N).subtype.toAddMonoidHom
        Subtype.val_injective (eT (1, 0))
    rw [h1, AddEquiv.addOrderOf_eq eT, Prod.addOrderOf_mk, ZMod.addOrderOf_one, addOrderOf_zero,
      Nat.lcm_one_right]

end Torsion

section Fixed

variable {K : Type*} [Field K] {M : Type*} [Field M] [Algebra K M] (t : M)
  (H : Subgroup (M ≃ₐ[K⟮t⟯] M))

lemma coe_mem_fixedField (x : K⟮t⟯) : (x : M) ∈ IntermediateField.fixedField H := by
  rw [IntermediateField.mem_fixedField_iff]
  intro σ _
  exact σ.commutes x

lemma self_mem_fixedField : t ∈ IntermediateField.fixedField H :=
  coe_mem_fixedField t H ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩

def tFix : IntermediateField.fixedField H := ⟨t, self_mem_fixedField t H⟩

@[scoped simp] lemma coe_tFix : ((tFix t H : IntermediateField.fixedField H) : M) = t := rfl

lemma mem_adjoin_tFix (x : K⟮t⟯) :
    (⟨x.1, coe_mem_fixedField t H x⟩ : IntermediateField.fixedField H) ∈ K⟮tFix t H⟯ := by
  have hv : ∀ p : K[X], ((Polynomial.aeval (tFix t H) p : IntermediateField.fixedField H) : M) =
      Polynomial.aeval t p := fun p => by
    have h := Polynomial.aeval_algHom_apply
      ((IntermediateField.fixedField H).val.restrictScalars K) (tFix t H) p
    rw [AlgHom.restrictScalars_apply, IntermediateField.coe_val, coe_tFix] at h
    exact h.symm
  obtain ⟨f, g, hfg⟩ := (IntermediateField.mem_adjoin_simple_iff K x.1).mp x.2
  rw [IntermediateField.mem_adjoin_simple_iff]
  refine ⟨f, g, Subtype.ext ?_⟩
  rw [IntermediateField.coe_div, hv, hv]
  exact hfg

def toAdjoinFix : K⟮t⟯ →+* K⟮tFix t H⟯ where
  toFun x := ⟨⟨x.1, coe_mem_fixedField t H x⟩, mem_adjoin_tFix t H x⟩
  map_one' := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := Subtype.ext (Subtype.ext rfl)
  map_zero' := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)

scoped instance algebraAdjoinFix : Algebra K⟮t⟯ K⟮tFix t H⟯ := (toAdjoinFix t H).toAlgebra

scoped instance smulAdjoinFix : SMul K⟮t⟯ K⟮tFix t H⟯ := Algebra.toSMul

lemma algebraMap_adjoinFix_apply (x : K⟮t⟯) :
    ((algebraMap K⟮t⟯ K⟮tFix t H⟯ x : IntermediateField.fixedField H) : M) = x := rfl

scoped instance isScalarTower_adjoinFix :
    IsScalarTower K⟮t⟯ K⟮tFix t H⟯ (IntermediateField.fixedField H) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem finiteDimensional_isGalois_fixedField [FiniteDimensional K⟮t⟯ M] [IsGalois K⟮t⟯ M]
    [H.Normal] :
    FiniteDimensional K⟮tFix t H⟯ (IntermediateField.fixedField H) ∧
      IsGalois K⟮tFix t H⟯ (IntermediateField.fixedField H) := by
  haveI : IsGalois K⟮t⟯ (IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H
  exact ⟨Module.Finite.of_restrictScalars_finite K⟮t⟯ _ _, IsGalois.tower_top_of_isGalois K⟮t⟯ _ _⟩

theorem apply_mem_fixedField [FiniteDimensional K⟮t⟯ M] [IsGalois K⟮t⟯ M] [H.Normal]
    (ψ : IntermediateField.fixedField H →ₐ[K] M) (hψ : ψ (tFix t H) = t)
    (y : IntermediateField.fixedField H) : ψ y ∈ IntermediateField.fixedField H := by
  haveI : IsGalois K⟮t⟯ (IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H

  have hcomm : ∀ x : K⟮t⟯, ψ (algebraMap K⟮t⟯ (IntermediateField.fixedField H) x) = x := by
    have h12 : ψ.comp (IsScalarTower.toAlgHom K K⟮t⟯ (IntermediateField.fixedField H)) =
        (K⟮t⟯).val := by
      refine IntermediateField.adjoin_algHom_ext K (s := {t}) fun x hx => ?_
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hψ
    intro x
    exact DFunLike.congr_fun h12 x
  let ψ' : IntermediateField.fixedField H →ₐ[K⟮t⟯] M := { ψ.toRingHom with commutes' := hcomm }
  have hrange := AlgHom.fieldRange_of_normal ψ'
  have hy : ψ y ∈ ψ'.fieldRange := AlgHom.mem_fieldRange.mpr ⟨y, rfl⟩
  rwa [hrange] at hy

end Fixed

section Main

open scoped MatrixGroups

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hM : ¬ 2 ∣ M)
  (K : Type u) [Field K] [IsAlgClosed K] [CharP K 2]
  (x : qExpFunctionFieldC K (CohCarrier.GammaH M H))
  (hx : (x : LaurentSeries K) = jqModC K)

include hM hx in
theorem main :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (ι : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] L),
      FiniteDimensional (IntermediateField.adjoin K ({ι x} : Set L)) L ∧
        IsGalois (IntermediateField.adjoin K ({ι x} : Set L)) L ∧
        ∀ P : Place K L, 0 < P.ord (ι x) → P.ord (ι x) ∣ 12 := by
  classical
  have hM0 : M ≠ 0 := NeZero.ne M
  have hMK : (M : K) ≠ 0 := fun h => hM ((CharP.cast_eq_zero_iff K 2 M).mp h)

  obtain ⟨Ω, _iF, _iD, _iA, t, ht, hfin, hgal, W₀, hW₀, θ, ρ, hfull, hθinj, hρE, hρmul, hequivC,
    hsurjC, -⟩ := ModularCurve.exists_equivariant_torsion_reduction_ofJ K 2 M hMK 0 (E0 K) (E0_j K)
  haveI := hfin
  haveI := hgal

  let tk : K⟮t⟯ := ⟨t, IntermediateField.mem_adjoin_simple_self K t⟩
  let E : WeierstrassCurve K⟮t⟯ := WeierstrassCurve.ofJ tk
  have hEj : E.j = tk := WeierstrassCurve.ofJ_j tk
  have hjt : algebraMap K⟮t⟯ Ω E.j = t := by rw [hEj]; rfl
  have hEtr : Transcendental K E.j := by
    rw [hEj]
    intro halg
    exact ht (by simpa using halg.algebraMap (A := Ω))
  have hσt : ∀ σ : Ω ≃ₐ[K⟮t⟯] Ω, σ t = t := fun σ => σ.commutes tk
  let act : (Ω ≃ₐ[K⟮t⟯] Ω) →
      (E.baseChange Ω).toAffine.Point →+ (E.baseChange Ω).toAffine.Point :=
    fun σ => WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K⟮t⟯] Ω)
  have hact1 : ∀ P, act 1 P = P := by
    rintro (_ | ⟨a, b, h⟩)
    · rfl
    · show Point.map _ (Point.some a b h) = _
      rw [Point.map_some]
      rfl
  have hactmul : ∀ σ τ P, act (σ * τ) P = act σ (act τ P) := by
    rintro σ τ (_ | ⟨a, b, h⟩)
    · rfl
    · show Point.map _ (Point.some a b h) = Point.map _ (Point.map _ (Point.some a b h))
      rw [Point.map_some, Point.map_some, Point.map_some]
      rfl

  let H' : Subgroup (Ω ≃ₐ[K⟮t⟯] Ω) := pmSubgroup act hact1 hactmul M
  haveI : H'.Normal := pmSubgroup_normal act hact1 hactmul M
  haveI : IsGalois K⟮t⟯ (IntermediateField.fixedField H') :=
    IsGalois.of_fixedField_normal_subgroup H'
  obtain ⟨hfinL, hgalL⟩ := finiteDimensional_isGalois_fixedField t H'

  obtain ⟨hcard₀, g₀, hg₀⟩ := tors_facts (E0 K) hMK
  have hθ : Set.InjOn θ (tors (E.baseChange Ω).toAffine.Point M) := by
    intro P hP Q hQ h
    have hPQ : M • (P - Q) = 0 := by
      rw [nsmul_sub, show M • P = 0 from hP, show M • Q = 0 from hQ, sub_zero]
    have := hθinj M (P - Q) hM hPQ (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.mp this
  have hθs : ∀ y ∈ tors (E0 K).toAffine.Point M,
      ∃ x ∈ tors (E.baseChange Ω).toAffine.Point M, θ x = y := by
    let θr : tors (E.baseChange Ω).toAffine.Point M → tors (E0 K).toAffine.Point M :=
      fun P => ⟨θ P.1, show M • θ P.1 = 0 by rw [← map_nsmul, show M • P.1 = 0 from P.2, map_zero]⟩
    have hinj : Function.Injective θr := fun P Q h =>
      Subtype.ext (hθ P.2 Q.2 (congrArg Subtype.val h))
    haveI : Finite (tors (E0 K).toAffine.Point M) :=
      Nat.finite_of_card_ne_zero (by rw [hcard₀]; exact pow_ne_zero 2 hM0)
    have hbij := hinj.bijective_of_nat_card_le (by rw [hcard₀]; exact le_of_eq hfull.symm)
    intro y hy
    obtain ⟨z, hz⟩ := hbij.2 ⟨y, hy⟩
    exact ⟨z.1, z.2, congrArg Subtype.val hz⟩

  have hle : qExpFunctionFieldC K (CohCarrier.GammaH M H) ≤
      qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) :=
    qExpFunctionFieldC_mono K (Gamma1_le_GammaH M H)
  let incl : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K]
      qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) :=
    IntermediateField.inclusion hle
  let x₁ : qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) := ⟨(x : LaurentSeries K), hle x.2⟩
  have hx₁ : (x₁ : LaurentSeries K) = jqModC K := hx
  have hincl : incl x = x₁ := rfl

  obtain ⟨Ψ, hnatD, hnegD⟩ :=
    ModularCurve.exists_natural_algHom_qExpFunctionFieldC_gamma1_of_transcendental_j K M hMK x₁ hx₁
      K⟮t⟯ Ω E hEtr hfull
  obtain ⟨P₁, hP₁, hθP₁⟩ := hθs g₀ (show M • g₀ = 0 by rw [← hg₀]; exact addOrderOf_nsmul_eq_zero g₀)
  have hordP₁ : addOrderOf P₁ = M := by
    refine Nat.dvd_antisymm (addOrderOf_dvd_of_nsmul_eq_zero hP₁) ?_
    rw [← hg₀, ← hθP₁]
    exact addOrderOf_map_dvd θ P₁
  have hordN₁ : addOrderOf (-P₁) = M := by rw [addOrderOf_neg]; exact hordP₁
  let Pt : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M} := ⟨P₁, hordP₁⟩
  let Nt : {P : (E.baseChange Ω).toAffine.Point // addOrderOf P = M} := ⟨-P₁, hordN₁⟩
  let ψ₁ : qExpFunctionFieldC K (CongruenceSubgroup.Gamma1 M) →ₐ[K] Ω := (Ψ Pt).1
  have hψ₁x : ψ₁ x₁ = t := (Ψ Pt).2.trans hjt
  let ψ : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] Ω := ψ₁.comp incl
  have hψx : ψ x = t := by
    show ψ₁ (incl x) = t
    rw [hincl]
    exact hψ₁x

  have hψ₁L : ∀ f, ψ₁ f ∈ IntermediateField.fixedField H' := by
    intro f
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have key : ((σ : Ω →ₐ[K⟮t⟯] Ω).restrictScalars K).comp ψ₁ = ψ₁ := by
      rcases hσ with hσ | hσ
      · have h1 : Pt.1 = WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K⟮t⟯] Ω) Pt.1 :=
          (hσ P₁ hP₁).symm
        exact (hnatD σ Pt Pt h1).symm
      · have hN : M • (-P₁) = 0 := by rw [smul_neg, show M • P₁ = 0 from hP₁, neg_zero]
        have h1 : Nt.1 = WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[K⟮t⟯] Ω) Pt.1 := by
          have h := hσ P₁ hP₁
          show -P₁ = act σ P₁
          rw [h]
        have h2 := hnatD σ Pt Nt h1
        rw [hnegD Pt Nt rfl] at h2
        exact h2.symm
    have h := DFunLike.congr_fun key f
    exact h
  have hψL : ∀ f, ψ f ∈ IntermediateField.fixedField H' := fun f => hψ₁L (incl f)
  let ι : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] IntermediateField.fixedField H' :=
    { toFun := fun f => ⟨ψ f, hψL f⟩
      map_one' := by
        apply Subtype.ext
        have h1 : ψ 1 = 1 := ψ.toRingHom.map_one
        exact h1
      map_mul' := fun a b => by
        apply Subtype.ext
        have h1 : ψ (a * b) = ψ a * ψ b := ψ.toRingHom.map_mul a b
        exact h1
      map_zero' := by
        apply Subtype.ext
        have h1 : ψ 0 = 0 := ψ.toRingHom.map_zero
        exact h1
      map_add' := fun a b => by
        apply Subtype.ext
        have h1 : ψ (a + b) = ψ a + ψ b := ψ.toRingHom.map_add a b
        exact h1
      commutes' := fun c => by
        apply Subtype.ext
        have h1 : ψ (algebraMap K (qExpFunctionFieldC K (CohCarrier.GammaH M H)) c) =
            algebraMap K Ω c := ψ.commutes c
        exact h1 }
  have hιx : ι x = tFix t H' := Subtype.ext hψx
  refine ⟨IntermediateField.fixedField H', inferInstance, inferInstance, ι, ?_, ?_, ?_⟩
  · rw [hιx]; exact hfinL
  · rw [hιx]; exact hgalL

  intro P hP
  rw [hιx] at hP ⊢

  have hint : ∀ φ : IntermediateField.fixedField H' →ₐ[K] Ω, φ (tFix t H') = t →
      φ.toRingHom.IsIntegral := fun φ hφ => isIntegral_of_apply_eq (tFix t H') t φ hφ
  let vK : IntermediateField.fixedField H' →ₐ[K] Ω :=
    (IntermediateField.fixedField H').val.restrictScalars K
  have hvK : vK (tFix t H') = t := rfl
  obtain ⟨-, -, hB3, hB4, hB5⟩ :=
    AlgebraicCurve.Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois K (tFix t H') t 0 vK hvK
      hfin hgal hint W₀ hW₀
  have e0 : (tFix t H' : IntermediateField.fixedField H') -
      algebraMap K (IntermediateField.fixedField H') 0 = tFix t H' := by
    rw [map_zero, sub_zero]
  rw [e0] at hB3 hB5
  obtain ⟨φ, hφt, hφP⟩ := hB3 P hP
  rw [← hφP, hB5 φ hφt]

  let D : Subgroup (Ω ≃ₐ[K⟮t⟯] Ω) := decomp W₀
  let X : Type u := {ψ' : IntermediateField.fixedField H' →ₐ[K] Ω // ψ' (tFix t H') = t}
  letI : MulAction (Ω ≃ₐ[K⟮t⟯] Ω) X :=
    { smul := fun σ ψ' => ⟨((σ : Ω →ₐ[K⟮t⟯] Ω).restrictScalars K).comp ψ'.1, by
        show σ (ψ'.1 (tFix t H')) = t
        rw [ψ'.2, hσt]⟩
      one_smul := fun ψ' => Subtype.ext (AlgHom.ext fun _ => rfl)
      mul_smul := fun σ τ ψ' => Subtype.ext (AlgHom.ext fun _ => rfl) }
  have smul_val : ∀ (σ : Ω ≃ₐ[K⟮t⟯] Ω) (ψ' : X),
      (σ • ψ').1 = ((σ : Ω →ₐ[K⟮t⟯] Ω).restrictScalars K).comp ψ'.1 := fun _ _ => rfl
  let x₀ : X := ⟨φ, hφt⟩

  have hfib : Nat.card {ψ' : X //
        W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2) = W₀.restrictAlong φ (hint φ hφt)} =
      Nat.card (MulAction.orbit D x₀) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun ψ' => ?_)
    rw [eq_comm, hB4 φ ψ'.1 hφt ψ'.2, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨σ, hσ, h⟩
      refine ⟨⟨σ, hσ⟩, Subtype.ext ?_⟩
      rw [Subgroup.smul_def, smul_val]
      exact h.symm
    · rintro ⟨σ, h⟩
      exact ⟨σ.1, σ.2, by rw [← h, Subgroup.smul_def, smul_val]⟩
  rw [hfib, Nat.card_coe_set_eq, ← MulAction.index_stabilizer]

  have hleS : H'.subgroupOf D ≤ MulAction.stabilizer D x₀ := by
    intro σ hσ
    rw [Subgroup.mem_subgroupOf] at hσ
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    rw [Subgroup.smul_def, smul_val]
    ext y
    show σ.1 (φ y) = φ y
    exact (IntermediateField.mem_fixedField_iff H' (φ y)).mp
      (apply_mem_fixedField t H' φ hφt y) σ.1 hσ

  have h1D : (1 : Ω ≃ₐ[K⟮t⟯] Ω) ∈ D := D.one_mem
  let ρD : D →* Stab K :=
    { toFun := fun σ => ⟨ρ σ.1, MulAction.mem_stabilizer_iff.mpr (hρE σ.1 σ.2)⟩
      map_one' := by
        apply Subtype.ext
        have h := hρmul 1 1 h1D h1D
        rw [mul_one] at h
        show ρ 1 = 1
        exact (mul_left_cancel (a := ρ 1) (by rw [mul_one]; exact h.symm))
      map_mul' := fun σ τ => Subtype.ext (hρmul σ.1 τ.1 σ.2 τ.2) }

  let actS : Stab K → (E0 K).toAffine.Point →+ (E0 K).toAffine.Point :=
    fun γ => autPt γ.1 (MulAction.mem_stabilizer_iff.mp γ.2)
  have hS1 : ∀ Q, actS 1 Q = Q := fun Q => autPt_one _ Q
  have hSmul : ∀ γ γ' Q, actS (γ * γ') Q = actS γ (actS γ' Q) :=
    fun γ γ' Q => autPt_mul γ.1 γ'.1 _ _ _ Q
  let A : Subgroup (Stab K) := pmSubgroup actS hS1 hSmul M
  haveI hAn : A.Normal := pmSubgroup_normal actS hS1 hSmul M
  have hZA : Zneg K ≤ A := by
    rw [Zneg, Subgroup.zpowers_le]
    exact Or.inr fun Q _ => autPt_negE0 Q

  have hequiv : ∀ (σ : D) (P : (E.baseChange Ω).toAffine.Point),
      θ (act σ.1 P) = actS (ρD σ) (θ P) :=
    fun σ P => ((autPt_eq_iff_heq _ _ _ _).mpr (hequivC σ.1 σ.2 P)).symm
  have htorsθ : ∀ P : (E.baseChange Ω).toAffine.Point, M • P = 0 → M • θ P = 0 := fun P hP => by
    rw [← map_nsmul, hP, map_zero]

  have hcomap : A.comap ρD ≤ H'.subgroupOf D := by
    intro σ hσ
    rw [Subgroup.mem_comap] at hσ
    rw [Subgroup.mem_subgroupOf]
    change IsPM act M σ.1
    rcases hσ with hσ | hσ
    · refine Or.inl fun P hP => ?_
      refine hθ (nsmul_act_eq_zero act M σ.1 hP) hP ?_
      rw [hequiv σ P]
      exact hσ (θ P) (htorsθ P hP)
    · refine Or.inr fun P hP => ?_
      refine hθ (nsmul_act_eq_zero act M σ.1 hP)
        (show M • (-P) = 0 by rw [smul_neg, hP, neg_zero]) ?_
      rw [hequiv σ P, map_neg]
      exact hσ (θ P) (htorsθ P hP)

  have hsup : ρD.range ⊔ A = ⊤ := by
    rw [eq_top_iff]
    intro γ _
    obtain ⟨σ, hσD, hσ⟩ := hsurjC γ.1 (MulAction.mem_stabilizer_iff.mp γ.2)
    let σD : D := ⟨σ, hσD⟩
    have key : γ⁻¹ * ρD σD ∈ A := by
      change IsPM actS M (γ⁻¹ * ρD σD)
      rcases hσ with hσ | hσ
      · refine Or.inl fun Q hQ => ?_
        obtain ⟨P, hP, rfl⟩ := hθs Q hQ
        have h : actS γ (θ P) = θ (act σ P) := (autPt_eq_iff_heq _ _ (θ P) _).mpr (hσ P)
        rw [hSmul, ← hequiv σD P, ← h, ← hSmul, inv_mul_cancel, hS1]
      · refine Or.inr fun Q hQ => ?_
        obtain ⟨P, hP, rfl⟩ := hθs Q hQ
        have h : actS γ (θ P) = -θ (act σ P) := (autPt_eq_iff_heq _ _ (θ P) _).mpr (hσ P)
        have h' : θ (act σ P) = -actS γ (θ P) := by rw [h, neg_neg]
        rw [hSmul, ← hequiv σD P, h', map_neg, ← hSmul, inv_mul_cancel, hS1]
    have hγ : γ = ρD σD * (γ⁻¹ * ρD σD)⁻¹ := by group
    rw [hγ]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨σD, rfl⟩)
      (Subgroup.mem_sup_right (A.inv_mem key))

  have hidx : (H'.subgroupOf D).index ∣ 12 := by
    have h2 : (A.comap ρD).index = A.index := by
      rw [Subgroup.index_comap, ← Subgroup.relIndex_sup_right ρD.range A, hsup,
        Subgroup.relIndex_top_right]
    calc (H'.subgroupOf D).index ∣ (A.comap ρD).index := Subgroup.index_dvd_of_le hcomap
      _ = A.index := h2
      _ ∣ (Zneg K).index := Subgroup.index_dvd_of_le hZA
      _ = 12 := index_Zneg
  have hst : (MulAction.stabilizer D x₀).index ∣ 12 := (Subgroup.index_dvd_of_le hleS).trans hidx
  exact_mod_cast hst

end Main

end P2MKcGH12
p2m_reactivate "P2MW.S_ModularCurve_exists_isGalois_ord_dvd_twelve_qExpFunctionFieldC_gammaH_of_char_two.P2MKcGH12"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_isGalois_ord_dvd_twelve_qExpFunctionFieldC_gammaH_of_char_two.P2MKcGH12"

open AlgebraicCurve ModularCurve

universe u in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (hM : ¬ 2 ∣ M)
    (K : Type u) [Field K] [IsAlgClosed K] [CharP K 2]
    (x : qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hx : (x : LaurentSeries K) = jqModC K) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (ι : qExpFunctionFieldC K (CohCarrier.GammaH M H) →ₐ[K] L),
      FiniteDimensional (IntermediateField.adjoin K ({ι x} : Set L)) L ∧
        IsGalois (IntermediateField.adjoin K ({ι x} : Set L)) L ∧
        ∀ P : Place K L, 0 < P.ord (ι x) → P.ord (ι x) ∣ 12 :=
  P2MKcGH12.main M H hM K x hx

end S_ModularCurve_exists_isGalois_ord_dvd_twelve_qExpFunctionFieldC_gammaH_of_char_two
end P2MW
export P2MW.S_ModularCurve_exists_isGalois_ord_dvd_twelve_qExpFunctionFieldC_gammaH_of_char_two (solution)
