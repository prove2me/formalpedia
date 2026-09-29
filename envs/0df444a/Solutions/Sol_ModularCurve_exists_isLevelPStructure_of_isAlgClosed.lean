-- Prove2me | solution 1 for ModularCurve.exists_isLevelPStructure_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/7ff7b32f-687f-5501-b69b-b4655becbc37

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Theorems.Thm_ModularCurve_exists_torsionPt_indepElt_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isLevelPStructure_of_isAlgClosed
p2m_attr_erase "instance" "instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

namespace ModularCurve
p2m_export "ModularCurve" "LevelPData IsLevelPStructure exists_torsionPt_indepElt_ne_zero"
p2m_open "ModularCurve"

open WeierstrassCurve Polynomial

theorem exists_torsionPt_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K]
    (W : WeierstrassCurve K) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) :
    ∃ x y : K, W.toAffine.Equation x y ∧ (W.preΨ p).eval x = 0 := by
  have hp := (Fact.out : p.Prime)
  have hpZ : ((p : ℤ) : K) ≠ 0 := by rwa [Int.cast_natCast]
  have hdeg : (W.preΨ p).natDegree = (p ^ 2 - 1) / 2 := by
    rw [W.natDegree_preΨ hpZ, Int.natAbs_natCast,
      if_neg (by simpa using Nat.not_even_iff_odd.mpr (hp.odd_of_ne_two hp2))]
  have hpos : 0 < (W.preΨ p).natDegree := by
    rw [hdeg]
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    have h2 : 2 ≤ p := hp.two_le
    have : p ^ 2 - 1 = 2 * (2 * k * (k + 1)) := by rw [hk, Nat.sub_eq_of_eq_add]; ring
    rw [this, Nat.mul_div_cancel_left _ two_pos]
    have hk1 : 1 ≤ k := by omega
    positivity
  have hdeg0 : (W.preΨ p).degree ≠ 0 := (Polynomial.natDegree_pos_iff_degree_pos.mp hpos).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (W.preΨ p) hdeg0

  let q : K[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
  have hq : q = X ^ 2 + (C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) := by
    simp only [q]; rw [add_sub_assoc]
  have htail : (C (W.a₁ * x + W.a₃) * X - C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)).degree <
      ((2 : ℕ) : WithBot ℕ) :=
    lt_of_le_of_lt ((degree_sub_le _ _).trans
      (max_le (degree_C_mul_X_le _) (degree_C_le.trans zero_le_one)))
      (WithBot.coe_lt_coe.mpr one_lt_two)
  have hqdeg : q.natDegree = 2 := by
    rw [hq, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]; exact htail
  have hqpos : 0 < q.natDegree := by rw [hqdeg]; exact two_pos
  have hqdeg0 : q.degree ≠ 0 := (Polynomial.natDegree_pos_iff_degree_pos.mp hqpos).ne'
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q hqdeg0
  refine ⟨x, y, ?_, hx⟩
  rw [WeierstrassCurve.Affine.equation_iff]
  have hy' := hy
  simp only [q, IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hy'
  linear_combination hy'

theorem exists_isLevelPStructure_of_isAlgClosed' {K : Type u} [Field K] [IsAlgClosed K]
    (W : WeierstrassCurve K) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hΔ : W.Δ ≠ 0) : ∃ D : LevelPData K, IsLevelPStructure W p D := by
  obtain ⟨x₁, y₁, h₁, h₁'⟩ := exists_torsionPt_of_isAlgClosed W hp2 hpK
  obtain ⟨x, y, h, h', hi₁, hi₂, -, -⟩ :=
    exists_torsionPt_indepElt_ne_zero W hp2 hpK hΔ x₁ y₁ x₁ y₁ h₁ h₁' h₁ h₁'
  exact ⟨⟨x, y, x₁, y₁⟩,
    { equation_P := h, equation_Q := h₁, preΨ_P := h', preΨ_Q := h₁',
      isUnit_indepElt_PQ := isUnit_iff_ne_zero.mpr hi₁,
      isUnit_indepElt_QP := isUnit_iff_ne_zero.mpr hi₂ }⟩

end ModularCurve

theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hΔ : W.Δ ≠ 0) :
    ∃ D : ModularCurve.LevelPData K, ModularCurve.IsLevelPStructure W p D :=
  ModularCurve.exists_isLevelPStructure_of_isAlgClosed' W hp2 hpK hΔ

end S_ModularCurve_exists_isLevelPStructure_of_isAlgClosed
end P2MW
export P2MW.S_ModularCurve_exists_isLevelPStructure_of_isAlgClosed (solution)
