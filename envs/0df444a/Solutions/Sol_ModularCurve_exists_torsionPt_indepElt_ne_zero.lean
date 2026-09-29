-- Prove2me | solution 1 for ModularCurve.exists_torsionPt_indepElt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/cd932463-17d1-5cd9-a593-e87ad0652d31

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Theorems.Thm_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_torsionPt_indepElt_ne_zero
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

namespace ModularCurve
p2m_export "ModularCurve" "indepElt indepElt_eq_zero_iff_mem_zmultiples"
p2m_open "ModularCurve"

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

theorem indepElt_ne_zero_iff_not_mem_zmultiples' {F : Type u} [Field F] [DecidableEq F]
    {W : WeierstrassCurve F} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {x₀ y₀ x y : F} (h₀ : W.toAffine.Nonsingular x₀ y₀) (h : W.toAffine.Nonsingular x y)
    (hP₀ : p • (Point.some x₀ y₀ h₀) = 0) :
    indepElt W p x₀ x ≠ 0 ↔ Point.some x y h ∉ AddSubgroup.zmultiples (Point.some x₀ y₀ h₀) :=
  (ModularCurve.indepElt_eq_zero_iff_mem_zmultiples hp2 h₀ h hP₀).not

section Symm
variable {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

theorem not_mem_zmultiples_symm {p : ℕ} [Fact p.Prime] {P₀ P : W.toAffine.Point}
    (hP₀ : p • P₀ = 0) (hP₀0 : P₀ ≠ 0) (hP : p • P = 0) (hP0 : P ≠ 0)
    (hn : P ∉ AddSubgroup.zmultiples P₀) : P₀ ∉ AddSubgroup.zmultiples P := by
  intro hmem
  apply hn

  have hle : AddSubgroup.zmultiples P₀ ≤ AddSubgroup.zmultiples P :=
    AddSubgroup.zmultiples_le.mpr hmem
  have hc₀ : Nat.card (AddSubgroup.zmultiples P₀) = p := by
    rw [Nat.card_zmultiples, addOrderOf_eq_prime hP₀ hP₀0]
  have hc : Nat.card (AddSubgroup.zmultiples P) = p := by
    rw [Nat.card_zmultiples, addOrderOf_eq_prime hP hP0]
  haveI : Finite (AddSubgroup.zmultiples P) := Nat.finite_of_card_ne_zero (by rw [hc]; exact (Fact.out : p.Prime).ne_zero)
  have heq : AddSubgroup.zmultiples P₀ = AddSubgroup.zmultiples P :=
    AddSubgroup.eq_of_le_of_card_ge hle (by rw [hc, hc₀])
  rw [heq]
  exact AddSubgroup.mem_zmultiples P

end Symm

section Existence

variable {K : Type u} [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) {p : ℕ} [Fact p.Prime]

theorem exists_torsion_not_mem [DecidableEq K] [W.IsElliptic] (hpK : (p : K) ≠ 0) (hp2 : p ≠ 2)
    (Q₁ Q₂ : W.toAffine.Point) (hQ₁ : p • Q₁ = 0) (hQ₁0 : Q₁ ≠ 0) (hQ₂ : p • Q₂ = 0)
    (hQ₂0 : Q₂ ≠ 0) :
    ∃ X : W.toAffine.Point, p • X = 0 ∧ X ≠ 0 ∧ X ∉ AddSubgroup.zmultiples Q₁ ∧
      X ∉ AddSubgroup.zmultiples Q₂ := by
  have hp := (Fact.out : p.Prime)

  have hcard : Nat.card (Submodule.torsionBy ℤ W.toAffine.Point p) = p ^ 2 := by
    have h := WeierstrassCurve.card_torsion_of_isAlgClosed (F := K) (K := K) W (n := p) hpK
    have e : W.map (algebraMap K K) = W := by
      rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]
    change Nat.card (Submodule.torsionBy ℤ (W.map (algebraMap K K)).toAffine.Point p) = p ^ 2 at h
    rw [e] at h
    exact h

  by_contra hcon
  push_neg at hcon
  let T : Set W.toAffine.Point := (Submodule.torsionBy ℤ W.toAffine.Point p : Set _)
  let L : Set W.toAffine.Point :=
    (AddSubgroup.zmultiples Q₁ : Set _) ∪ (AddSubgroup.zmultiples Q₂ : Set _)
  have hsub : T ⊆ L := by
    intro X hX
    have hX' : p • X = 0 := by
      have := (Submodule.mem_torsionBy_iff (R := ℤ) (p : ℤ) X).mp hX
      rwa [natCast_zsmul] at this
    by_cases hX0 : X = 0
    · left; rw [hX0]; exact zero_mem _
    by_cases h1 : X ∈ AddSubgroup.zmultiples Q₁
    · left; exact h1
    · right; exact hcon X hX' hX0 h1
  have hc₁ : (AddSubgroup.zmultiples Q₁ : Set W.toAffine.Point).ncard = p := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Nat.card_zmultiples,
      addOrderOf_eq_prime hQ₁ hQ₁0]
  have hc₂ : (AddSubgroup.zmultiples Q₂ : Set W.toAffine.Point).ncard = p := by
    rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, Nat.card_zmultiples,
      addOrderOf_eq_prime hQ₂ hQ₂0]
  have hT : T.ncard = p ^ 2 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have hfin₁ : (AddSubgroup.zmultiples Q₁ : Set W.toAffine.Point).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hc₁]; exact hp.ne_zero)
  have hfin₂ : (AddSubgroup.zmultiples Q₂ : Set W.toAffine.Point).Finite :=
    Set.finite_of_ncard_ne_zero (by rw [hc₂]; exact hp.ne_zero)
  have hle : T.ncard ≤ L.ncard := Set.ncard_le_ncard hsub (hfin₁.union hfin₂)
  have hL : L.ncard ≤ p + p := by
    calc L.ncard ≤ (AddSubgroup.zmultiples Q₁ : Set W.toAffine.Point).ncard +
        (AddSubgroup.zmultiples Q₂ : Set W.toAffine.Point).ncard := Set.ncard_union_le _ _
      _ = p + p := by rw [hc₁, hc₂]
  rw [hT] at hle
  have h3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · have := hp.two_le; rcases h with ⟨k, rfl⟩; omega
  nlinarith

omit [IsAlgClosed K] in

theorem eval_preΨ_eq_zero_of_nsmul_eq_zero [DecidableEq K] [W.IsElliptic] (hp2 : p ≠ 2) {x y : K}
    (h : W.toAffine.Nonsingular x y) (hP : p • Point.some x y h = 0) :
    (W.preΨ p).eval x = 0 := by
  rw [WeierstrassCurve.preΨ_ofNat]
  exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W ((Fact.out : p.Prime).odd_of_ne_two hp2) h).mp hP

omit [IsAlgClosed K] in
theorem nsmul_eq_zero_of_eval_preΨ_eq_zero [DecidableEq K] [W.IsElliptic] (hp2 : p ≠ 2) {x y : K}
    (h : W.toAffine.Nonsingular x y) (hx : (W.preΨ p).eval x = 0) :
    p • Point.some x y h = 0 := by
  rw [WeierstrassCurve.preΨ_ofNat] at hx
  exact (WeierstrassCurve.Affine.Point.nsmul_some_eq_zero_iff_eval_prePsi W ((Fact.out : p.Prime).odd_of_ne_two hp2) h).mpr hx

theorem exists_torsionPt_indepElt_ne_zero' (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hΔ : W.Δ ≠ 0)
    (x₁ y₁ x₂ y₂ : K) (h₁ : W.toAffine.Equation x₁ y₁) (h₁' : (W.preΨ p).eval x₁ = 0)
    (h₂ : W.toAffine.Equation x₂ y₂) (h₂' : (W.preΨ p).eval x₂ = 0) :
    ∃ x y : K, W.toAffine.Equation x y ∧ (W.preΨ p).eval x = 0 ∧
      indepElt W p x x₁ ≠ 0 ∧ indepElt W p x₁ x ≠ 0 ∧
      indepElt W p x x₂ ≠ 0 ∧ indepElt W p x₂ x ≠ 0 := by
  classical
  haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have hn₁ : W.toAffine.Nonsingular x₁ y₁ :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular (W := W.toAffine)).mp h₁
  have hn₂ : W.toAffine.Nonsingular x₂ y₂ :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular (W := W.toAffine)).mp h₂
  have hQ₁ := nsmul_eq_zero_of_eval_preΨ_eq_zero W hp2 hn₁ h₁'
  have hQ₂ := nsmul_eq_zero_of_eval_preΨ_eq_zero W hp2 hn₂ h₂'
  obtain ⟨X, hX, hX0, hX₁, hX₂⟩ := exists_torsion_not_mem W hpK hp2 _ _ hQ₁
    (Point.some_ne_zero hn₁) hQ₂ (Point.some_ne_zero hn₂)
  rcases X with _ | ⟨x, y, hxy⟩
  · exact absurd rfl hX0
  refine ⟨x, y, hxy.1, eval_preΨ_eq_zero_of_nsmul_eq_zero W hp2 hxy hX, ?_, ?_, ?_, ?_⟩
  · exact (indepElt_ne_zero_iff_not_mem_zmultiples' hp2 hxy hn₁ hX).mpr
      (not_mem_zmultiples_symm hQ₁ (Point.some_ne_zero hn₁) hX (Point.some_ne_zero hxy) hX₁)
  · exact (indepElt_ne_zero_iff_not_mem_zmultiples' hp2 hn₁ hxy hQ₁).mpr hX₁
  · exact (indepElt_ne_zero_iff_not_mem_zmultiples' hp2 hxy hn₂ hX).mpr
      (not_mem_zmultiples_symm hQ₂ (Point.some_ne_zero hn₂) hX (Point.some_ne_zero hxy) hX₂)
  · exact (indepElt_ne_zero_iff_not_mem_zmultiples' hp2 hn₂ hxy hQ₂).mpr hX₂

end Existence

end ModularCurve

theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] (W : WeierstrassCurve K) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hΔ : W.Δ ≠ 0)
    (x₁ y₁ x₂ y₂ : K) (h₁ : W.toAffine.Equation x₁ y₁) (h₁' : (W.preΨ p).eval x₁ = 0)
    (h₂ : W.toAffine.Equation x₂ y₂) (h₂' : (W.preΨ p).eval x₂ = 0) :
    ∃ x y : K, W.toAffine.Equation x y ∧ (W.preΨ p).eval x = 0 ∧
      ModularCurve.indepElt W p x x₁ ≠ 0 ∧ ModularCurve.indepElt W p x₁ x ≠ 0 ∧
      ModularCurve.indepElt W p x x₂ ≠ 0 ∧ ModularCurve.indepElt W p x₂ x ≠ 0 :=
  ModularCurve.exists_torsionPt_indepElt_ne_zero' W hp2 hpK hΔ x₁ y₁ x₂ y₂ h₁ h₁' h₂ h₂'

end S_ModularCurve_exists_torsionPt_indepElt_ne_zero
end P2MW
export P2MW.S_ModularCurve_exists_torsionPt_indepElt_ne_zero (solution)
