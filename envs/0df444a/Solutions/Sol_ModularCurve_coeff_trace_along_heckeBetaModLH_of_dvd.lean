-- Prove2me | solution 1 for ModularCurve.coeff_trace_along_heckeBetaModLH_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/823ea414-20fa-5478-88a1-ebb5f27b0a8b

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaModLH
import Theorems.Thm_ModularCurve_finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_trace_along_heckeBetaModLH_of_dvd
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

open ModularCurve HahnSeries KaehlerDifferential AlgebraicCurve AlgebraicCurve.Differential

namespace TRBdvd

section Twist

variable {R : Type*} [Field R]

def twistFun (c : Rˣ) (x : LaurentSeries R) : LaurentSeries R where
  coeff n := ((c ^ n : Rˣ) : R) * x.coeff n
  isPWO_support' := x.isPWO_support.mono fun n hn => by
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro h
    exact hn (by rw [h, mul_zero])

@[scoped simp] theorem twistFun_coeff (c : Rˣ) (x : LaurentSeries R) (n : ℤ) :
    (twistFun c x).coeff n = ((c ^ n : Rˣ) : R) * x.coeff n := rfl

theorem support_twistFun (c : Rˣ) (x : LaurentSeries R) : (twistFun c x).support = x.support := by
  ext n
  simp only [HahnSeries.mem_support, twistFun_coeff, ne_eq, Units.mul_right_eq_zero]

theorem twistFun_single (c : Rˣ) (k : ℤ) (r : R) :
    twistFun c (single k r) = single k (((c ^ k : Rˣ) : R) * r) := by
  ext n
  by_cases h : n = k
  · subst h; simp
  · simp [coeff_single_of_ne h]

def twist (c : Rˣ) : LaurentSeries R →ₐ[R] LaurentSeries R where
  toFun := twistFun c
  map_one' := by
    rw [← single_zero_one, twistFun_single]; simp
  map_mul' x y := by
    ext a
    rw [twistFun_coeff,
      coeff_mul_right' (x := x) (y := y) (twistFun c y).isPWO_support
        (support_twistFun c y).symm.subset,
      coeff_mul_left' (x := twistFun c x) (y := twistFun c y) x.isPWO_support
        (support_twistFun c x).subset,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.mem_antidiagonal] at hij
    rw [twistFun_coeff, twistFun_coeff, ← hij.2.2, zpow_add, Units.val_mul]
    ring
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [mul_add]
  commutes' r := by
    rw [algebraMap_laurentSeries_eq_single]
    show twistFun c (single 0 r) = single 0 r
    rw [twistFun_single]; simp

@[scoped simp] theorem twist_coeff (c : Rˣ) (x : LaurentSeries R) (n : ℤ) :
    (twist c x).coeff n = ((c ^ n : Rˣ) : R) * x.coeff n := rfl

theorem twist_qExpand_of_pow_eq_one (c : Rˣ) (m : ℕ) [NeZero m] (hc : c ^ m = 1)
    (z : LaurentSeries R) : twist c (qExpand R m z) = qExpand R m z := by
  ext n
  rw [twist_coeff]
  by_cases h : (m : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [zpow_mul, zpow_natCast, hc, one_zpow, Units.val_one, one_mul]
  · rw [qExpand_coeff_of_not_dvd m _ h, mul_zero]

theorem twist_C (c : Rˣ) (r : R) : twist c (C r) = C r := by
  show twistFun c (single 0 r) = single 0 r
  rw [twistFun_single]; simp

theorem twist_injective (c : Rˣ) : Function.Injective (twist c) := by
  intro a b hab
  ext n
  have := congrArg (fun s : LaurentSeries R => s.coeff n) hab
  simp only [twist_coeff] at this
  exact (mul_right_inj' (Units.ne_zero _)).mp this

theorem twist_ne_zero (c : Rˣ) {x : LaurentSeries R} (hx : x ≠ 0) : twist c x ≠ 0 :=
  fun h => hx (twist_injective c (by rw [h, map_zero]))

end Twist

section RootSum

variable {R : Type*} [Field R]

def rootSum (u : Rˣ) (ℓ : ℕ) (x : LaurentSeries R) : LaurentSeries R :=
  ∑ j ∈ Finset.range ℓ, twist (u ^ j) x

theorem rootSum_apply (u : Rˣ) (ℓ : ℕ) (x : LaurentSeries R) :
    rootSum u ℓ x = ∑ j ∈ Finset.range ℓ, twist (u ^ j) x := rfl

theorem rootSum_add (u : Rˣ) (ℓ : ℕ) (x y : LaurentSeries R) :
    rootSum u ℓ (x + y) = rootSum u ℓ x + rootSum u ℓ y := by
  simp only [rootSum, map_add, Finset.sum_add_distrib]

theorem rootSum_zero (u : Rˣ) (ℓ : ℕ) : rootSum u ℓ (0 : LaurentSeries R) = 0 := by
  simp only [rootSum, map_zero, Finset.sum_const_zero]

theorem rootSum_mul_of_fixed (u : Rˣ) (ℓ : ℕ) (x y : LaurentSeries R)
    (hy : ∀ j : ℕ, twist (u ^ j) y = y) : rootSum u ℓ (x * y) = rootSum u ℓ x * y := by
  rw [rootSum_apply, rootSum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hy]

theorem sum_zpow_pow {ζ : R} {ℓ : ℕ} (hζ : IsPrimitiveRoot ζ ℓ) (n : ℤ) :
    ∑ j ∈ Finset.range ℓ, (ζ ^ n) ^ j = if (ℓ : ℤ) ∣ n then (ℓ : R) else 0 := by
  split_ifs with h
  · rw [(hζ.zpow_eq_one_iff_dvd n).mpr h]
    simp
  · have hne : ζ ^ n ≠ 1 := fun h' => h ((hζ.zpow_eq_one_iff_dvd n).mp h')
    rw [geom_sum_eq hne]
    have : (ζ ^ n) ^ ℓ = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [this, sub_self, zero_div]

theorem rootSum_coeff {ζ : R} {ℓ : ℕ} (hζ : IsPrimitiveRoot ζ ℓ) (hz : ζ ≠ 0)
    (x : LaurentSeries R) (n : ℤ) :
    (rootSum (Units.mk0 ζ hz) ℓ x).coeff n = if (ℓ : ℤ) ∣ n then (ℓ : R) * x.coeff n else 0 := by
  rw [rootSum_apply, HahnSeries.coeff_sum]
  simp only [twist_coeff]
  rw [← Finset.sum_mul]
  have h : ∀ j ∈ Finset.range ℓ, (((Units.mk0 ζ hz ^ j) ^ n : Rˣ) : R) = (ζ ^ n) ^ j := by
    intro j _
    rw [Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, Units.val_mk0, ← zpow_natCast,
      ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  rw [Finset.sum_congr rfl h, sum_zpow_pow hζ n]
  split_ifs <;> simp

end RootSum

section Trace

variable (K : Type*) [Field K] [IsAlgClosed K]

def EE (_ℓ : ℕ) : Type _ := AlgebraicClosure (LaurentSeries K)

variable (ℓ : ℕ) in
scoped instance : Field (EE K ℓ) := inferInstanceAs (Field (AlgebraicClosure (LaurentSeries K)))

variable (ℓ : ℕ) in
scoped instance : IsAlgClosed (EE K ℓ) := inferInstanceAs (IsAlgClosed (AlgebraicClosure (LaurentSeries K)))

def ιE (ℓ : ℕ) : LaurentSeries K →+* EE K ℓ :=
  algebraMap (LaurentSeries K) (AlgebraicClosure (LaurentSeries K))

theorem ιE_injective (ℓ : ℕ) : Function.Injective (ιE K ℓ) :=
  (algebraMap (LaurentSeries K) (AlgebraicClosure (LaurentSeries K))).injective

variable (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) (ℓ : ℕ) [Fact ℓ.Prime]

abbrev FXt : Type _ := ↥(qExpFunctionFieldC K (CohCarrier.GammaH N H'))

abbrev FUf : IntermediateField K (LaurentSeries K) :=
  qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))

abbrev FUt : Type _ := ↥(FUf K N H' ℓ)

abbrev bβ : FXt K N H' →ₐ[K] FUt K N H' ℓ := heckeBetaModLH K N H' ℓ

abbrev bα : FXt K N H' →ₐ[K] FUt K N H' ℓ := heckeAlphaModLH K N H' ℓ

@[reducible] def algAlongBeta : Algebra (FXt K N H') (FUt K N H' ℓ) :=
  algebraAlong (bβ K N H' ℓ)

@[reducible] def algBetaE : Algebra (FXt K N H') (EE K ℓ) :=
  (((ιE K ℓ).comp (algebraMap (FUt K N H' ℓ) (LaurentSeries K))).comp (bβ K N H' ℓ).toRingHom).toAlgebra

attribute [local instance] algAlongBeta algBetaE

theorem isScalarTower_beta : IsScalarTower K (FXt K N H') (FUt K N H' ℓ) :=
  isScalarTower_along (bβ K N H' ℓ)

attribute [local instance] isScalarTower_beta

theorem finrank_beta (hℓN : ℓ ∣ N) (hNK : ((N : ℕ) : K) ≠ 0) (hℓK : ((ℓ : ℕ) : K) ≠ 0)
    (hβ : HeckeBetaModLHDefined K N H' ℓ) :
    Module.finrank (FXt K N H') (FUt K N H' ℓ) = ℓ := by
  have h := ModularCurve.finrankAlong_heckeBetaModLH K N H' ℓ hNK hℓK hβ
  rw [if_pos hℓN] at h
  exact h

theorem finiteDimensional_beta (hℓK : ((ℓ : ℕ) : K) ≠ 0) :
    FiniteDimensional (FXt K N H') (FUt K N H' ℓ) :=
  (ModularCurve.finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH K N H' ℓ hℓK).2.1

theorem isSeparable_beta (hℓK : ((ℓ : ℕ) : K) ≠ 0) :
    Algebra.IsSeparable (FXt K N H') (FUt K N H' ℓ) :=
  (ModularCurve.finiteAlong_and_separableAlong_heckeAlphaModLH_heckeBetaModLH K N H' ℓ hℓK).2.2.2

variable {K N H' ℓ}

def sigmaTwist (hβ : HeckeBetaModLHDefined K N H' ℓ) (c : Kˣ) (hc : c ^ ℓ = 1) :
    FUt K N H' ℓ →ₐ[FXt K N H'] EE K ℓ where
  toRingHom := (ιE K ℓ).comp ((twist c).toRingHom.comp (algebraMap (FUt K N H' ℓ) (LaurentSeries K)))
  commutes' f := by
    show ιE K ℓ (twist c ((bβ K N H' ℓ f : FUt K N H' ℓ) : LaurentSeries K)) =
      ιE K ℓ ((bβ K N H' ℓ f : FUt K N H' ℓ) : LaurentSeries K)
    rw [coe_heckeBetaModLH K N H' ℓ hβ, twist_qExpand_of_pow_eq_one c ℓ hc]

theorem sigmaTwist_apply (hβ : HeckeBetaModLHDefined K N H' ℓ) (c : Kˣ) (hc : c ^ ℓ = 1) (v : FUt K N H' ℓ) :
    sigmaTwist hβ c hc v = ιE K ℓ (twist c (v : LaurentSeries K)) := rfl

def zu {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) : Kˣ := Units.mk0 ζ (hζ.ne_zero (NeZero.ne ℓ))

theorem zu_pow {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (j : ℕ) : (zu hζ ^ j) ^ ℓ = 1 := by
  ext
  rw [← pow_mul, mul_comm, pow_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, zu,
    Units.val_mk0, hζ.pow_eq_one, one_pow, Units.val_one]

def emb (hβ : HeckeBetaModLHDefined K N H' ℓ) {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) :
    Fin ℓ → (FUt K N H' ℓ →ₐ[FXt K N H'] EE K ℓ) :=
  fun j => sigmaTwist hβ (zu hζ ^ (j : ℕ)) (zu_pow hζ j)

variable (K N H') in

def xBar : FXt K N H' :=
  ⟨jqModC K, intFormRatiosC_subset K _ (ModularCurve.jqModC_mem_intFormRatiosC K (CohCarrier.GammaH N H'))⟩

theorem coe_xBar : ((xBar K N H' : FXt K N H') : LaurentSeries K) = jqModC K := rfl

theorem twist_sep {a b : Kˣ} (h : twist a (jqModC K) = twist b (jqModC K)) : (a : K) = b := by
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff (-1)) h
  simp only [twist_coeff, ModularCurve.coeff_jqModC_neg_one, mul_one] at h1
  have h2 : ((a ^ (-1 : ℤ) : Kˣ) : K) = ((b ^ (-1 : ℤ) : Kˣ) : K) := h1
  have h3 : a ^ (-1 : ℤ) = b ^ (-1 : ℤ) := Units.ext h2
  rw [zpow_neg_one, zpow_neg_one, inv_inj] at h3
  rw [h3]

theorem emb_injective (hβ : HeckeBetaModLHDefined K N H' ℓ) {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) :
    Function.Injective (emb hβ hζ) := by
  have vsome : ∀ j : Fin ℓ, emb hβ hζ j (bα K N H' ℓ (xBar K N H')) =
      ιE K ℓ (twist (zu hζ ^ (j : ℕ)) (jqModC K)) := by
    intro j
    show sigmaTwist hβ (zu hζ ^ (j : ℕ)) (zu_pow hζ j) (bα K N H' ℓ (xBar K N H')) = _
    rw [sigmaTwist_apply, coe_heckeAlphaModLH, coe_xBar]
  intro i j h
  have h' := congrArg (fun σ : FUt K N H' ℓ →ₐ[FXt K N H'] EE K ℓ => σ (bα K N H' ℓ (xBar K N H'))) h
  try simp only at h'
  rw [vsome, vsome] at h'
  have h1 := twist_sep (ιE_injective K ℓ h')
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, zu, Units.val_mk0] at h1
  exact Fin.ext (hζ.pow_inj i.2 j.2 h1)

theorem emb_bijective (hβ : HeckeBetaModLHDefined K N H' ℓ) (hℓN : ℓ ∣ N) (hNK : ((N : ℕ) : K) ≠ 0)
    (hℓK : ((ℓ : ℕ) : K) ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) :
    Function.Bijective (emb hβ hζ) := by
  haveI := finiteDimensional_beta K N H' ℓ hℓK
  haveI := isSeparable_beta K N H' ℓ hℓK
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨emb_injective hβ hζ, ?_⟩
  rw [Fintype.card_fin, AlgHom.card, finrank_beta K N H' ℓ hℓN hNK hℓK hβ]

theorem qExpand_trace (hβ : HeckeBetaModLHDefined K N H' ℓ) (hℓN : ℓ ∣ N) (hNK : ((N : ℕ) : K) ≠ 0)
    (hℓK : ((ℓ : ℕ) : K) ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ ℓ) (v : FUt K N H' ℓ) :
    qExpand K ℓ ((Algebra.trace (FXt K N H') (FUt K N H' ℓ) v : FXt K N H') : LaurentSeries K)
      = rootSum (zu hζ) ℓ (v : LaurentSeries K) := by
  haveI := finiteDimensional_beta K N H' ℓ hℓK
  haveI := isSeparable_beta K N H' ℓ hℓK
  apply ιE_injective K ℓ
  have h1 := trace_eq_sum_embeddings (EE K ℓ) (K := FXt K N H') (L := FUt K N H' ℓ) (x := v)
  have h2 : algebraMap (FXt K N H') (EE K ℓ) (Algebra.trace (FXt K N H') (FUt K N H' ℓ) v)
      = ιE K ℓ (qExpand K ℓ ((Algebra.trace (FXt K N H') (FUt K N H' ℓ) v : FXt K N H') : LaurentSeries K)) := by
    show ιE K ℓ ((bβ K N H' ℓ _ : FUt K N H' ℓ) : LaurentSeries K) = _
    rw [coe_heckeBetaModLH K N H' ℓ hβ]
  rw [← h2, h1, ← (emb_bijective hβ hℓN hNK hℓK hζ).sum_comp (fun σ => σ v), rootSum_apply, map_sum,
    Finset.sum_range]
  rfl

theorem coeff_trace (hβ : HeckeBetaModLHDefined K N H' ℓ) (hℓN : ℓ ∣ N) (hNK : ((N : ℕ) : K) ≠ 0)
    (hℓK : ((ℓ : ℕ) : K) ≠ 0) (v : FUt K N H' ℓ) (n : ℤ) :
    ((Algebra.trace (FXt K N H') (FUt K N H' ℓ) v : FXt K N H') : LaurentSeries K).coeff n
      = (ℓ : K) * (v : LaurentSeries K).coeff (n * ℓ) := by
  haveI : NeZero ((ℓ : ℕ) : K) := ⟨hℓK⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K ℓ
  have h := congrArg (fun s : LaurentSeries K => s.coeff ((ℓ : ℤ) * n)) (qExpand_trace hβ hℓN hNK hℓK hζ v)
  try simp only at h
  rw [qExpand_coeff_mul, zu, rootSum_coeff hζ, if_pos (dvd_mul_right _ _)] at h
  rw [h, mul_comm (ℓ : ℤ) n]

end Trace

end TRBdvd
p2m_reactivate "P2MW.S_ModularCurve_coeff_trace_along_heckeBetaModLH_of_dvd.TRBdvd"

open ModularCurve

theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ℓ ∣ N) (hNK : ((N : ℕ) : K) ≠ 0)
    (hβ : ModularCurve.HeckeBetaModLHDefined K N H' ℓ)
    (v : ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ)))) (n : ℤ) :
    (((letI := AlgebraicCurve.algebraAlong (ModularCurve.heckeBetaModLH K N H' ℓ);
        Algebra.trace ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))
          ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H' ⊓ CongruenceSubgroup.Gamma0 (N * ℓ))) v) :
        ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) : LaurentSeries K).coeff n =
      (ℓ : K) * (v : LaurentSeries K).coeff (n * ℓ) := by
  have hℓK : ((ℓ : ℕ) : K) ≠ 0 := by
    intro h0
    apply hNK
    obtain ⟨c, rfl⟩ := hℓN
    rw [Nat.cast_mul, h0, zero_mul]
  exact TRBdvd.coeff_trace hβ hℓN hNK hℓK v n

end
p2m_reactivate "P2MW.S_ModularCurve_coeff_trace_along_heckeBetaModLH_of_dvd.TRBdvd"

end S_ModularCurve_coeff_trace_along_heckeBetaModLH_of_dvd
end P2MW
export P2MW.S_ModularCurve_coeff_trace_along_heckeBetaModLH_of_dvd (solution)
