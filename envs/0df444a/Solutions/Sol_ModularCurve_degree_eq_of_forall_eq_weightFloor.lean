-- Prove2me | solution 1 for ModularCurve.degree_eq_of_forall_eq_weightFloor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/0675d82f-91cd-5de2-a5e6-bd88151eaab0

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_card_fibres_jqModC_modularFunctionFieldFullC_eq
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_degree_eq_of_forall_eq_weightFloor
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois HahnSeries.ramScale_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace DegC2

section Ord

variable {K : Type*} {FF : Type*} [Field K] [Field FF] [Algebra K FF] (w : Place K FF)

theorem mem_iff_le_one {f : FF} : f ∈ w.toValuationSubring ↔ w.adicValuation f ≤ 1 :=
  Place.mem_iff_adicValuation_le_one w

theorem ord_nonneg_iff {f : FF} (hf : f ≠ 0) : 0 ≤ w.ord f ↔ w.adicValuation f ≤ 1 := by
  rw [Place.ord, neg_nonneg, WithZero.log_le_iff_le_exp (w.adicValuation_ne_zero hf), WithZero.exp_zero]

theorem ord_pos_iff {f : FF} (hf : f ≠ 0) : 0 < w.ord f ↔ w.adicValuation f < 1 := by
  rw [Place.ord, neg_pos, ← WithZero.log_one,
    WithZero.log_lt_log (w.adicValuation_ne_zero hf) one_ne_zero]

theorem ord_neg_iff {f : FF} (hf : f ≠ 0) : w.ord f < 0 ↔ 1 < w.adicValuation f := by
  rw [Place.ord, neg_lt_zero, ← WithZero.log_one,
    WithZero.log_lt_log one_ne_zero (w.adicValuation_ne_zero hf)]

theorem ord_nonneg_of_mem {f : FF} (h : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [Place.ord_zero]
  · exact (ord_nonneg_iff w hf).2 ((mem_iff_le_one w).1 h)

theorem mem_of_ord_nonneg {f : FF} (h : 0 ≤ w.ord f) : f ∈ w.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact zero_mem _
  · exact (mem_iff_le_one w).2 ((ord_nonneg_iff w hf).1 h)

theorem ord_pow (f : FF) (n : ℕ) : w.ord (f ^ n) = n * w.ord f := by
  rw [← zpow_natCast, Place.ord_zpow]

theorem adicValuation_algebraMap {c : K} (hc : c ≠ 0) : w.adicValuation (algebraMap K FF c) = 1 := by
  apply le_antisymm (w.adicValuation_algebraMap_le_one c)
  have h1 : w.adicValuation (algebraMap K FF c) * w.adicValuation (algebraMap K FF c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  have h2 := w.adicValuation_algebraMap_le_one c⁻¹
  by_contra h
  rw [not_le] at h
  have : w.adicValuation (algebraMap K FF c) * w.adicValuation (algebraMap K FF c⁻¹) < 1 * 1 :=
    mul_lt_mul_of_lt_of_le_of_nonneg_of_pos h h2 zero_le' zero_lt_one
  rw [h1, one_mul] at this
  exact lt_irrefl _ this

theorem ord_algebraMap {c : K} (hc : c ≠ 0) : w.ord (algebraMap K FF c) = 0 := by
  rw [Place.ord, adicValuation_algebraMap w hc, WithZero.log_one, neg_zero]

theorem ord_sub_algebraMap_eq_zero_of_ord_pos {t : FF} (ht : t ≠ 0) {c : K} (hc : c ≠ 0) (h : 0 < w.ord t) :
    w.ord (t - algebraMap K FF c) = 0 := by
  have hv : w.adicValuation t < w.adicValuation (algebraMap K FF c) := by
    rw [adicValuation_algebraMap w hc]; exact (ord_pos_iff w ht).1 h
  rw [Place.ord, Valuation.map_sub_swap, Valuation.map_sub_eq_of_lt_left _ hv, adicValuation_algebraMap w hc,
    WithZero.log_one, neg_zero]

theorem ord_sub_algebraMap_eq_of_ord_neg {t : FF} (ht : t ≠ 0) (c : K) (h : w.ord t < 0) :
    w.ord (t - algebraMap K FF c) = w.ord t := by
  have hv : w.adicValuation (algebraMap K FF c) < w.adicValuation t :=
    lt_of_le_of_lt (w.adicValuation_algebraMap_le_one c) ((ord_neg_iff w ht).1 h)
  rw [Place.ord, Place.ord, Valuation.map_sub_eq_of_lt_left _ hv]

theorem ord_eq_zero_of_ord_sub_algebraMap_pos {t : FF} {c : K} (hc : c ≠ 0) (htc : t - algebraMap K FF c ≠ 0)
    (h : 0 < w.ord (t - algebraMap K FF c)) : w.ord t = 0 := by
  have hv : w.adicValuation (t - algebraMap K FF c) < w.adicValuation (algebraMap K FF c) := by
    rw [adicValuation_algebraMap w hc]; exact (ord_pos_iff w htc).1 h
  have : t = (t - algebraMap K FF c) + algebraMap K FF c := by ring
  rw [Place.ord, this, Valuation.map_add_eq_of_lt_right _ hv, adicValuation_algebraMap w hc, WithZero.log_one, neg_zero]

end Ord

theorem ord_eq_of_ord_sub_algebraMap_neg {K : Type*} {FF : Type*} [Field K] [Field FF] [Algebra K FF] (w : Place K FF)
    {t : FF} (c : K) (htc : t - algebraMap K FF c ≠ 0) (h : w.ord (t - algebraMap K FF c) < 0) :
    w.ord t = w.ord (t - algebraMap K FF c) := by
  have := ord_sub_algebraMap_eq_of_ord_neg w htc (-c) h
  rwa [map_neg, sub_neg_eq_add, sub_add_cancel] at this

end DegC2

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open DegC2 in
theorem solution
    (K : Type) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (h6N : ((6 * N : ℕ) : K) ≠ 0) (m : ℕ)
    (hram : ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      (0 < w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) →
          w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) ∣ 3) ∧
      (0 < w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728) →
          w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728) ∣ 2))
    (D : Divisor K ↥(modularFunctionFieldFullC K N))
    (hD : ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      D w = (if 0 < w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))
               then (2 * (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))) / 3 else 0)
          + (if 0 < w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728)
               then ((m : ℤ) * w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728)) / 2 else 0)
          + (if w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) < 0
               then (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) else 0)) :
    (D.degree : ℚ) = (m : ℚ) * (2 * genusFormula N - 2) + ((m / 2 : ℕ) : ℚ) * (nuTwo N : ℚ)
        + ((2 * m / 3 : ℕ) : ℚ) * (nuThree N : ℚ) + (m : ℚ) * (cuspCount N : ℚ) := by
  classical
  set a : ℕ := 2 * m / 3 with ha
  set b : ℕ := m / 2 with hb
  set j : ↥(modularFunctionFieldFullC K N) := ⟨jqModC K, jqModC_mem_full K N⟩ with hjdef
  have hjcoe : (j : LaurentSeries K) = jqModC K := rfl

  have hN : (N : K) ≠ 0 := fun h => h6N (by push_cast; rw [h, mul_zero])
  have h2 : (2 : K) ≠ 0 := fun h => h6N (by push_cast; rw [show (6 : K) = 2 * 3 by norm_num, h]; ring)
  have h3 : (3 : K) ≠ 0 := fun h => h6N (by push_cast; rw [show (6 : K) = 2 * 3 by norm_num, h]; ring)
  have h1728 : (1728 : K) ≠ 0 := by
    rw [show (1728 : K) = 2 ^ 6 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  haveI : IsCurveOver K ↥(modularFunctionFieldFullC K N) := isCurveOver_modularFunctionFieldFullC K N
  have hdeg1 : ∀ v : Place K ↥(modularFunctionFieldFullC K N), v.deg = 1 :=
    IsCurveOver.forall_deg_eq_one_of_isAlgClosed

  have hj0 : j ≠ 0 := by
    intro h
    have : (j : LaurentSeries K) = 0 := by rw [h]; rfl
    rw [hjcoe] at this
    exact (transcendental_jqModC K) (this ▸ isAlgebraic_zero)
  have hjc : j - algebraMap K ↥(modularFunctionFieldFullC K N) 1728 ≠ 0 := by
    intro h
    have h' : (j : LaurentSeries K) = algebraMap K (LaurentSeries K) 1728 := by
      rw [sub_eq_zero] at h; rw [h]; rfl
    rw [hjcoe] at h'
    exact (transcendental_jqModC K) (h' ▸ isAlgebraic_algebraMap (1728 : K))
  have htr : Transcendental K j := fun h =>
    (transcendental_jqModC K) (by simpa using h.algHom (modularFunctionFieldFullC K N).val)

  have hzero_c : ∀ v : Place K ↥(modularFunctionFieldFullC K N), 0 < v.ord j →
      v.ord (j - algebraMap K _ 1728) = 0 := fun v hv => ord_sub_algebraMap_eq_zero_of_ord_pos v hj0 h1728 hv
  have hpole_c : ∀ v : Place K ↥(modularFunctionFieldFullC K N), v.ord j < 0 →
      v.ord (j - algebraMap K _ 1728) = v.ord j := fun v hv => ord_sub_algebraMap_eq_of_ord_neg v hj0 1728 hv
  have hzero_j : ∀ v : Place K ↥(modularFunctionFieldFullC K N), 0 < v.ord (j - algebraMap K _ 1728) →
      v.ord j = 0 := fun v hv => ord_eq_zero_of_ord_sub_algebraMap_pos v h1728 hjc hv
  have hpole_j : ∀ v : Place K ↥(modularFunctionFieldFullC K N), v.ord (j - algebraMap K _ 1728) < 0 →
      v.ord j = v.ord (j - algebraMap K _ 1728) := fun v hv => ord_eq_of_ord_sub_algebraMap_neg v 1728 hjc hv

  obtain ⟨Dj, hDj, hDj0⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (F := ↥(modularFunctionFieldFullC K N)) j hj0
  obtain ⟨Dc, hDc, hDc0⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (F := ↥(modularFunctionFieldFullC K N)) (j - algebraMap K _ 1728) hjc

  set S0 := Dj.support.filter (fun v => 0 < v.ord j) with hS0def
  set S1 := Dc.support.filter (fun v => 0 < v.ord (j - algebraMap K _ 1728)) with hS1def
  set T := Dj.support.filter (fun v => v.ord j < 0) with hTdef
  have hS0 : ∀ v, v ∈ S0 ↔ 0 < v.ord j := fun v => by
    rw [hS0def, Finset.mem_filter, Finsupp.mem_support_iff, hDj v]
    exact ⟨And.right, fun h => ⟨ne_of_gt h, h⟩⟩
  have hS1 : ∀ v, v ∈ S1 ↔ 0 < v.ord (j - algebraMap K _ 1728) := fun v => by
    rw [hS1def, Finset.mem_filter, Finsupp.mem_support_iff, hDc v]
    exact ⟨And.right, fun h => ⟨ne_of_gt h, h⟩⟩
  have hT : ∀ v, v ∈ T ↔ v.ord j < 0 := fun v => by
    rw [hTdef, Finset.mem_filter, Finsupp.mem_support_iff, hDj v]
    exact ⟨And.right, fun h => ⟨ne_of_lt h, h⟩⟩
  obtain ⟨hcnt0, hcnt1, hcntT⟩ :=
    card_fibres_jqModC_modularFunctionFieldFullC_eq K N h6N S0 S1 T hS0 hS1 hT

  have hψpos : 0 < dedekindPsi N := by
    rw [dedekindPsi]
    have h1 : (1 : ℕ) ∈ N.divisors.filter Squarefree := by
      rw [Finset.mem_filter]; exact ⟨Nat.one_mem_divisors.2 (NeZero.ne N), squarefree_one⟩
    have := Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) h1
    simp only [Nat.div_one] at this
    exact lt_of_lt_of_le (Nat.pos_of_ne_zero (NeZero.ne N)) this
  have hfr := finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN
  haveI : FiniteDimensional ↥(IntermediateField.adjoin K ({j} : Set ↥(modularFunctionFieldFullC K N)))
      ↥(modularFunctionFieldFullC K N) := Module.finite_of_finrank_pos (by rw [hfr]; exact hψpos)
  let P : Divisor K ↥(modularFunctionFieldFullC K N) := ∑ v ∈ T, Finsupp.single v (-(v.ord j))
  have hP : ∀ v, P v = max 0 (-v.ord j) := by
    intro v
    simp only [P, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq' T v]
    by_cases hv : v ∈ T
    · rw [if_pos hv, max_eq_right]; have := (hT v).1 hv; omega
    · rw [if_neg hv, max_eq_left]; have := (hT v).not.1 hv; omega
  have hPdeg := degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental j htr P hP
  rw [hfr] at hPdeg
  have hPdeg' : Divisor.degree P = ∑ v ∈ T, -(v.ord j) := by
    simp only [P, map_sum, Divisor.degree_single, hdeg1, Nat.cast_one, mul_one]
  have hTsum : ∑ v ∈ T, v.ord j = -(dedekindPsi N : ℤ) := by
    have : ∑ v ∈ T, -(v.ord j) = (dedekindPsi N : ℤ) := hPdeg'.symm.trans hPdeg
    rw [Finset.sum_neg_distrib] at this
    linarith

  have hdegsum : ∀ E : Divisor K ↥(modularFunctionFieldFullC K N), Divisor.degree E = ∑ v ∈ E.support, E v := by
    intro E
    conv_lhs => rw [← Finsupp.sum_single E]
    rw [Finsupp.sum, map_sum]
    simp only [Divisor.degree_single, hdeg1, Nat.cast_one, mul_one]

  have hsupp_j : Dj.support = S0 ∪ T := by
    ext v
    rw [Finset.mem_union, hS0, hT, Finsupp.mem_support_iff, hDj v]
    constructor
    · intro h; rcases lt_trichotomy (v.ord j) 0 with h' | h' | h'
      · exact Or.inr h'
      · exact absurd h' h
      · exact Or.inl h'
    · rintro (h | h) <;> omega
  have hdisj_0T : Disjoint S0 T := by
    rw [Finset.disjoint_left]; intro v h0 hT'
    have := (hS0 v).1 h0; have := (hT v).1 hT'; omega
  have hS0sum : ∑ v ∈ S0, v.ord j = (dedekindPsi N : ℤ) := by
    have h := hdegsum Dj
    rw [hDj0, hsupp_j, Finset.sum_union hdisj_0T] at h
    simp only [hDj] at h
    linarith

  have hsupp_c : Dc.support = S1 ∪ T := by
    ext v
    rw [Finset.mem_union, hS1, hT, Finsupp.mem_support_iff, hDc v]
    constructor
    · intro h; rcases lt_trichotomy (v.ord (j - algebraMap K _ 1728)) 0 with h' | h' | h'
      · right; rw [hpole_j v h']; exact h'
      · exact absurd h' h
      · exact Or.inl h'
    · rintro (h | h)
      · exact ne_of_gt h
      · rw [hpole_c v h]; exact ne_of_lt h
  have hdisj_1T : Disjoint S1 T := by
    rw [Finset.disjoint_left]; intro v h1 hT'
    have := (hS1 v).1 h1; have := hzero_j v this; have := (hT v).1 hT'; omega
  have hS1sum : ∑ v ∈ S1, v.ord (j - algebraMap K _ 1728) = (dedekindPsi N : ℤ) := by
    have h := hdegsum Dc
    rw [hDc0, hsupp_c, Finset.sum_union hdisj_1T] at h
    simp only [hDc] at h
    have : ∑ v ∈ T, v.ord (j - algebraMap K _ 1728) = ∑ v ∈ T, v.ord j :=
      Finset.sum_congr rfl fun v hv => hpole_c v ((hT v).1 hv)
    linarith

  have hval0 : ∀ v ∈ S0, v.ord j = 1 ∨ v.ord j = 3 := by
    intro v hv
    have hpos := (hS0 v).1 hv
    have hdvd := (hram v).1 hpos
    have hle := Int.le_of_dvd (by norm_num) hdvd
    interval_cases h : v.ord j
    · exact Or.inl rfl
    · exfalso; norm_num at hdvd
    · exact Or.inr rfl
  have hval1 : ∀ v ∈ S1, v.ord (j - algebraMap K _ 1728) = 1 ∨ v.ord (j - algebraMap K _ 1728) = 2 := by
    intro v hv
    have hpos := (hS1 v).1 hv
    have hdvd := (hram v).2 hpos
    have hle := Int.le_of_dvd (by norm_num) hdvd
    interval_cases h : v.ord (j - algebraMap K _ 1728)
    · exact Or.inl rfl
    · exact Or.inr rfl

  set A0 := S0.filter (fun v => v.ord j = 1) with hA0
  set B0 := S0.filter (fun v => ¬ v.ord j = 1) with hB0
  have hB0val : ∀ v : Place K ↥(modularFunctionFieldFullC K N), v ∈ B0 → v.ord j = 3 := fun v hv => by
    rw [hB0, Finset.mem_filter] at hv
    exact (hval0 v hv.1).resolve_left hv.2
  have hcard0 : (A0.card : ℤ) + B0.card = S0.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := S0)
      (fun v : Place K ↥(modularFunctionFieldFullC K N) => v.ord j = 1)
  have hA0val : ∀ v : Place K ↥(modularFunctionFieldFullC K N), v ∈ A0 → v.ord j = 1 :=
    fun v hv => (Finset.mem_filter.1 hv).2
  have hsum0 : (A0.card : ℤ) + 3 * B0.card = (dedekindPsi N : ℤ) := by
    rw [← hS0sum, ← Finset.sum_filter_add_sum_filter_not S0 (fun v => v.ord j = 1)]
    have hA : ∑ v ∈ A0, v.ord j = ∑ v ∈ A0, (1 : ℤ) := Finset.sum_congr rfl fun v hv => hA0val v hv
    have hB : ∑ v ∈ B0, v.ord j = ∑ v ∈ B0, (3 : ℤ) := Finset.sum_congr rfl fun v hv => hB0val v hv
    rw [hA, hB]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    ring
  have hsumD0 : ∑ v ∈ S0, (2 * (m : ℤ) * v.ord j) / 3 = (A0.card : ℤ) * (a : ℤ) + B0.card * (2 * m) := by
    rw [← Finset.sum_filter_add_sum_filter_not S0 (fun v => v.ord j = 1)]
    have hA : ∑ v ∈ A0, (2 * (m : ℤ) * v.ord j) / 3 = ∑ v ∈ A0, (a : ℤ) :=
      Finset.sum_congr rfl fun v hv => by rw [hA0val v hv, mul_one, ha]; norm_cast
    have hB : ∑ v ∈ B0, (2 * (m : ℤ) * v.ord j) / 3 = ∑ v ∈ B0, (2 * (m : ℤ)) :=
      Finset.sum_congr rfl fun v hv => by rw [hB0val v hv, Int.mul_ediv_cancel _ (by norm_num : (3 : ℤ) ≠ 0)]
    rw [hA, hB]
    simp only [Finset.sum_const, smul_eq_mul]
    push_cast
    ring

  set A1 := S1.filter (fun v => v.ord (j - algebraMap K _ 1728) = 1) with hA1
  set B1 := S1.filter (fun v => ¬ v.ord (j - algebraMap K _ 1728) = 1) with hB1
  have hB1val : ∀ v : Place K ↥(modularFunctionFieldFullC K N), v ∈ B1 → v.ord (j - algebraMap K _ 1728) = 2 := fun v hv => by
    rw [hB1, Finset.mem_filter] at hv
    exact (hval1 v hv.1).resolve_left hv.2
  have hcard1 : (A1.card : ℤ) + B1.card = S1.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := S1)
      (fun v : Place K ↥(modularFunctionFieldFullC K N) => v.ord (j - algebraMap K _ 1728) = 1)
  have hA1val : ∀ v : Place K ↥(modularFunctionFieldFullC K N), v ∈ A1 → v.ord (j - algebraMap K _ 1728) = 1 :=
    fun v hv => (Finset.mem_filter.1 hv).2
  have hsum1 : (A1.card : ℤ) + 2 * B1.card = (dedekindPsi N : ℤ) := by
    rw [← hS1sum, ← Finset.sum_filter_add_sum_filter_not S1 (fun v => v.ord (j - algebraMap K _ 1728) = 1)]
    have hA : ∑ v ∈ A1, v.ord (j - algebraMap K _ 1728) = ∑ v ∈ A1, (1 : ℤ) :=
      Finset.sum_congr rfl fun v hv => hA1val v hv
    have hB : ∑ v ∈ B1, v.ord (j - algebraMap K _ 1728) = ∑ v ∈ B1, (2 : ℤ) :=
      Finset.sum_congr rfl fun v hv => hB1val v hv
    rw [hA, hB]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    ring
  have hsumD1 : ∑ v ∈ S1, ((m : ℤ) * v.ord (j - algebraMap K _ 1728)) / 2 =
      (A1.card : ℤ) * (b : ℤ) + B1.card * m := by
    rw [← Finset.sum_filter_add_sum_filter_not S1 (fun v => v.ord (j - algebraMap K _ 1728) = 1)]
    have hA : ∑ v ∈ A1, ((m : ℤ) * v.ord (j - algebraMap K _ 1728)) / 2 = ∑ v ∈ A1, (b : ℤ) :=
      Finset.sum_congr rfl fun v hv => by rw [hA1val v hv, mul_one, hb]; norm_cast
    have hB : ∑ v ∈ B1, ((m : ℤ) * v.ord (j - algebraMap K _ 1728)) / 2 = ∑ v ∈ B1, (m : ℤ) :=
      Finset.sum_congr rfl fun v hv => by rw [hB1val v hv, Int.mul_ediv_cancel _ (by norm_num : (2 : ℤ) ≠ 0)]
    rw [hA, hB]
    simp only [Finset.sum_const, smul_eq_mul]
    push_cast
    ring

  have hDS0 : ∀ v ∈ S0, D v = (2 * (m : ℤ) * v.ord j) / 3 := fun v hv => by
    have h0 := (hS0 v).1 hv
    rw [hD v, if_pos h0, if_neg (show ¬ 0 < v.ord (j - algebraMap K _ 1728) from by rw [hzero_c v h0]; exact lt_irrefl 0),
      if_neg (show ¬ v.ord j < 0 from by omega)]
    ring
  have hDS1 : ∀ v ∈ S1, D v = ((m : ℤ) * v.ord (j - algebraMap K _ 1728)) / 2 := fun v hv => by
    have h1 := (hS1 v).1 hv
    have hj := hzero_j v h1
    rw [hD v, if_neg (show ¬ 0 < v.ord j from by omega), if_pos h1, if_neg (show ¬ v.ord j < 0 from by omega)]
    ring
  have hDT : ∀ v ∈ T, D v = (m : ℤ) * v.ord j := fun v hv => by
    have ht := (hT v).1 hv
    rw [hD v, if_neg (show ¬ 0 < v.ord j from by omega),
      if_neg (show ¬ 0 < v.ord (j - algebraMap K _ 1728) from by rw [hpole_c v ht]; omega), if_pos ht]
    ring
  have hdisj_01 : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]; intro v h0 h1
    have := hzero_c v ((hS0 v).1 h0); have := (hS1 v).1 h1; omega
  have hDsupp : D.support ⊆ S0 ∪ S1 ∪ T := by
    intro v hv
    rw [Finsupp.mem_support_iff, hD v] at hv
    rw [Finset.mem_union, Finset.mem_union, hS0, hS1, hT]
    by_contra h
    push_neg at h
    obtain ⟨⟨h0, h1⟩, h2⟩ := h
    rw [if_neg (not_lt.2 h0), if_neg (not_lt.2 h1), if_neg (not_lt.2 h2)] at hv
    exact hv (by ring)
  have hDdeg : Divisor.degree D = ∑ v ∈ S0 ∪ S1 ∪ T, D v := by
    rw [hdegsum D]
    exact Finset.sum_subset hDsupp fun v _ hv => by simpa [Finsupp.mem_support_iff] using hv
  rw [Finset.sum_union (Finset.disjoint_union_left.2 ⟨hdisj_0T, hdisj_1T⟩), Finset.sum_union hdisj_01,
    Finset.sum_congr rfl hDS0, Finset.sum_congr rfl hDS1, Finset.sum_congr rfl hDT, hsumD0, hsumD1,
    ← Finset.mul_sum, hTsum] at hDdeg

  have hA0card : (A0.card : ℤ) = nuThree N := by
    have h3 : (3 : ℤ) * S0.card = dedekindPsi N + 2 * nuThree N := by exact_mod_cast hcnt0
    linarith
  have hB0card : 3 * (B0.card : ℤ) = dedekindPsi N - nuThree N := by linarith
  have hA1card : (A1.card : ℤ) = nuTwo N := by
    have h2' : (2 : ℤ) * S1.card = dedekindPsi N + nuTwo N := by exact_mod_cast hcnt1
    linarith
  have hB1card : 2 * (B1.card : ℤ) = dedekindPsi N - nuTwo N := by linarith
  have hTcard : (T.card : ℤ) = cuspCount N := by exact_mod_cast hcntT
  rw [hDdeg, genusFormula]
  push_cast
  have hB0q : (B0.card : ℚ) = ((dedekindPsi N : ℚ) - nuThree N) / 3 := by
    have : (3 : ℚ) * B0.card = dedekindPsi N - nuThree N := by exact_mod_cast hB0card
    linarith
  have hB1q : (B1.card : ℚ) = ((dedekindPsi N : ℚ) - nuTwo N) / 2 := by
    have : (2 : ℚ) * B1.card = dedekindPsi N - nuTwo N := by exact_mod_cast hB1card
    linarith
  have hA0q : (A0.card : ℚ) = nuThree N := by exact_mod_cast hA0card
  have hA1q : (A1.card : ℚ) = nuTwo N := by exact_mod_cast hA1card
  rw [hA0q, hB0q, hA1q, hB1q]
  ring

end S_ModularCurve_degree_eq_of_forall_eq_weightFloor
end P2MW
export P2MW.S_ModularCurve_degree_eq_of_forall_eq_weightFloor (solution)
