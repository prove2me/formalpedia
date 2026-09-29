-- Prove2me | solution 1 for ModularCurve.indepElt_eq_zero_iff_mem_zmultiples
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/90d53cfa-1034-549c-bafd-f56821b425a6

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_WeierstrassCurve_DivPolyMulFormulaCore
import Theorems.Thm_WeierstrassCurve_card_torsion_of_isAlgClosed
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

namespace ModularCurve
p2m_export "ModularCurve" "indepElt LevelPData IsLevelPStructure"
p2m_open "ModularCurve"

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

section FieldDictionary

variable {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

theorem nsmul_ne_zero_of_prime {p : ℕ} [Fact p.Prime] {P : W.toAffine.Point} (hP : p • P = 0)
    (hP0 : P ≠ 0) {a : ℕ} (ha1 : 1 ≤ a) (hap : a < p) : a • P ≠ 0 := by
  intro ha
  have hord : addOrderOf P = p := addOrderOf_eq_prime hP hP0
  have hdvd : p ∣ a := hord ▸ addOrderOf_dvd_of_nsmul_eq_zero ha
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

theorem lowTorsionFree_of_prime {p : ℕ} [Fact p.Prime] {x₀ y₀ : F}
    (h₀ : W.toAffine.Nonsingular x₀ y₀) (hP₀ : p • (Point.some x₀ y₀ h₀) = 0) {a : ℕ}
    (hap : a < p) : LowTorsionFree a h₀ :=
  fun k hk1 hka => nsmul_ne_zero_of_prime hP₀ (Point.some_ne_zero h₀) hk1 (lt_of_le_of_lt hka hap)

theorem exists_nsmul_eq_some_of_prime {p : ℕ} [Fact p.Prime] {x₀ y₀ : F}
    (h₀ : W.toAffine.Nonsingular x₀ y₀) (hP₀ : p • (Point.some x₀ y₀ h₀) = 0) {a : ℕ}
    (ha1 : 1 ≤ a) (hap : a < p) :
    (W.ΨSq a).eval x₀ ≠ 0 ∧ ∃ (xa ya : F) (ha : W.toAffine.Nonsingular xa ya),
      a • Point.some x₀ y₀ h₀ = Point.some xa ya ha ∧ xa * (W.ΨSq a).eval x₀ = (W.Φ a).eval x₀ := by
  obtain ⟨hΨ, hx⟩ := mfred_all h₀ a ha1 (lowTorsionFree_of_prime h₀ hP₀ hap)
  refine ⟨hΨ, ?_⟩
  have hne : a • Point.some x₀ y₀ h₀ ≠ 0 :=
    nsmul_ne_zero_of_prime hP₀ (Point.some_ne_zero h₀) ha1 hap
  rcases haP : a • Point.some x₀ y₀ h₀ with _ | ⟨xa, ya, ha⟩
  · exact absurd haP hne
  · refine ⟨xa, ya, ha, rfl, ?_⟩
    rw [haP, Point.xOrZero_some] at hx
    exact hx

theorem some_eq_or_eq_neg_of_x_eq {x y₁ y₂ : F} (h₁ : W.toAffine.Nonsingular x y₁)
    (h₂ : W.toAffine.Nonsingular x y₂) :
    Point.some x y₁ h₁ = Point.some x y₂ h₂ ∨ Point.some x y₁ h₁ = -Point.some x y₂ h₂ := by
  by_cases hy : y₁ = W.toAffine.negY x y₂
  · right
    rw [Point.neg_some]
    subst hy
    rfl
  · left
    have := Y_eq_of_Y_ne h₁.1 h₂.1 rfl hy
    subst this
    rfl

theorem mem_zmultiples_iff_of_prime {p : ℕ} [Fact p.Prime] {P₀ P : W.toAffine.Point}
    (hP₀ : p • P₀ = 0) (hP₀0 : P₀ ≠ 0) :
    P ∈ AddSubgroup.zmultiples P₀ ↔ ∃ n : ℕ, n < p ∧ n • P₀ = P := by
  have hord : addOrderOf P₀ = p := addOrderOf_eq_prime hP₀ hP₀0
  have hfin : IsOfFinAddOrder P₀ :=
    isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨p, (Fact.out : p.Prime).pos, hP₀⟩
  rw [← hfin.mem_multiples_iff_mem_zmultiples, AddSubmonoid.mem_multiples_iff]
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n % p, Nat.mod_lt _ (Fact.out : p.Prime).pos, ?_⟩
    rw [← hord]
    exact mod_addOrderOf_nsmul P₀ n
  · rintro ⟨n, -, rfl⟩
    exact ⟨n, rfl⟩

theorem indepElt_eq_zero_iff_mem_zmultiples' {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {x₀ y₀ x y : F}
    (h₀ : W.toAffine.Nonsingular x₀ y₀) (h : W.toAffine.Nonsingular x y)
    (hP₀ : p • (Point.some x₀ y₀ h₀) = 0) :
    indepElt W p x₀ x = 0 ↔ Point.some x y h ∈ AddSubgroup.zmultiples (Point.some x₀ y₀ h₀) := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨k, hk⟩ : Odd p := hp.odd_of_ne_two hp2
  have hk' : p = 2 * k + 1 := hk
  rw [indepElt, Finset.prod_eq_zero_iff, mem_zmultiples_iff_of_prime hP₀ (Point.some_ne_zero h₀)]
  constructor
  · rintro ⟨a, ha, hzero⟩
    rw [Finset.mem_Icc] at ha
    have hap : a < p := by omega
    obtain ⟨hΨ, xa, ya, hxa, haP, hmf⟩ := exists_nsmul_eq_some_of_prime h₀ hP₀ ha.1 hap
    have hx : x = xa := mul_right_cancel₀ hΨ (by rw [hmf]; exact sub_eq_zero.mp hzero)
    subst hx
    rcases some_eq_or_eq_neg_of_x_eq h hxa with heq | heq
    · exact ⟨a, hap, by rw [haP, heq]⟩
    · refine ⟨p - a, by omega, ?_⟩
      have : (p - a) • Point.some x₀ y₀ h₀ + a • Point.some x₀ y₀ h₀ = 0 := by
        rw [← add_nsmul, Nat.sub_add_cancel hap.le, hP₀]
      rw [eq_neg_of_add_eq_zero_left this, haP, heq]
  · rintro ⟨n, hnp, hnP⟩
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [zero_nsmul] at hnP
      exact Point.some_ne_zero h hnP.symm

    by_cases hle : 2 * n ≤ p - 1
    · refine ⟨n, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      obtain ⟨hΨ, xa, ya, hxa, haP, hmf⟩ := exists_nsmul_eq_some_of_prime h₀ hP₀ (by omega) hnp
      rw [hnP] at haP
      cases haP
      rw [hmf, sub_self]
    · refine ⟨p - n, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      obtain ⟨hΨ, xa, ya, hxa, haP, hmf⟩ :=
        exists_nsmul_eq_some_of_prime h₀ hP₀ (a := p - n) (by omega) (by omega)
      have hneg : (p - n) • Point.some x₀ y₀ h₀ = -Point.some x y h := by
        have : (p - n) • Point.some x₀ y₀ h₀ + n • Point.some x₀ y₀ h₀ = 0 := by
          rw [← add_nsmul, Nat.sub_add_cancel hnp.le, hP₀]
        rw [eq_neg_of_add_eq_zero_left this, hnP]
      rw [hneg, Point.neg_some] at haP
      cases haP
      rw [hmf, sub_self]

theorem indepElt_ne_zero_iff_not_mem_zmultiples {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {x₀ y₀ x y : F} (h₀ : W.toAffine.Nonsingular x₀ y₀) (h : W.toAffine.Nonsingular x y)
    (hP₀ : p • (Point.some x₀ y₀ h₀) = 0) :
    indepElt W p x₀ x ≠ 0 ↔ Point.some x y h ∉ AddSubgroup.zmultiples (Point.some x₀ y₀ h₀) :=
  (indepElt_eq_zero_iff_mem_zmultiples' hp2 h₀ h hP₀).not

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

end FieldDictionary

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
  · exact (indepElt_ne_zero_iff_not_mem_zmultiples hp2 hxy hn₁ hX).mpr
      (not_mem_zmultiples_symm hQ₁ (Point.some_ne_zero hn₁) hX (Point.some_ne_zero hxy) hX₁)
  · exact (indepElt_ne_zero_iff_not_mem_zmultiples hp2 hn₁ hxy hQ₁).mpr hX₁
  · exact (indepElt_ne_zero_iff_not_mem_zmultiples hp2 hxy hn₂ hX).mpr
      (not_mem_zmultiples_symm hQ₂ (Point.some_ne_zero hn₂) hX (Point.some_ne_zero hxy) hX₂)
  · exact (indepElt_ne_zero_iff_not_mem_zmultiples hp2 hn₂ hxy hQ₂).mpr hX₂

theorem exists_torsionPt (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) (hΔ : W.Δ ≠ 0) :
    ∃ x y : K, W.toAffine.Equation x y ∧ (W.preΨ p).eval x = 0 := by
  classical
  haveI : W.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have hp := (Fact.out : p.Prime)
  have hcard : Nat.card (Submodule.torsionBy ℤ W.toAffine.Point p) = p ^ 2 := by
    have h := WeierstrassCurve.card_torsion_of_isAlgClosed (F := K) (K := K) W (n := p) hpK
    have e : W.map (algebraMap K K) = W := by
      rw [Algebra.algebraMap_self, WeierstrassCurve.map_id]
    change Nat.card (Submodule.torsionBy ℤ (W.map (algebraMap K K)).toAffine.Point p) = p ^ 2 at h
    rw [e] at h
    exact h
  haveI : Finite (Submodule.torsionBy ℤ W.toAffine.Point p) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hp.ne_zero)
  have h1 : 1 < Nat.card (Submodule.torsionBy ℤ W.toAffine.Point p) := by
    rw [hcard]; exact Nat.one_lt_pow two_ne_zero hp.one_lt
  haveI : Nontrivial (Submodule.torsionBy ℤ W.toAffine.Point p) :=
    Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨⟨X, hX⟩, hX1⟩ := exists_ne (0 : Submodule.torsionBy ℤ W.toAffine.Point p)
  have hX' : p • X = 0 := by
    have := (Submodule.mem_torsionBy_iff (R := ℤ) (p : ℤ) X).mp hX
    rwa [natCast_zsmul] at this
  have hX0 : X ≠ 0 := fun h0 => hX1 (Subtype.ext h0)
  rcases X with _ | ⟨x, y, hxy⟩
  · exact absurd rfl hX0
  · exact ⟨x, y, hxy.1, eval_preΨ_eq_zero_of_nsmul_eq_zero W hp2 hxy hX'⟩

theorem exists_isLevelPStructure_of_isAlgClosed' (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hΔ : W.Δ ≠ 0) : ∃ D : LevelPData K, IsLevelPStructure W p D := by
  obtain ⟨x₁, y₁, h₁, h₁'⟩ := exists_torsionPt W hp2 hpK hΔ
  obtain ⟨x, y, h, h', hi₁, hi₂, -, -⟩ :=
    exists_torsionPt_indepElt_ne_zero' W hp2 hpK hΔ x₁ y₁ x₁ y₁ h₁ h₁' h₁ h₁'
  exact ⟨⟨x, y, x₁, y₁⟩,
    { equation_P := h, equation_Q := h₁, preΨ_P := h', preΨ_Q := h₁',
      isUnit_indepElt_PQ := isUnit_iff_ne_zero.mpr hi₁,
      isUnit_indepElt_QP := isUnit_iff_ne_zero.mpr hi₂ }⟩

end Existence

end ModularCurve

theorem solution
    {F : Type u} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {x₀ y₀ x y : F} (h₀ : W.toAffine.Nonsingular x₀ y₀)
    (h : W.toAffine.Nonsingular x y)
    (hP₀ : p • WeierstrassCurve.Affine.Point.some x₀ y₀ h₀ = 0) :
    ModularCurve.indepElt W p x₀ x = 0 ↔
      WeierstrassCurve.Affine.Point.some x y h ∈
        AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.some x₀ y₀ h₀) :=
  ModularCurve.indepElt_eq_zero_iff_mem_zmultiples' hp2 h₀ h hP₀

end S_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples
end P2MW
export P2MW.S_ModularCurve_indepElt_eq_zero_iff_mem_zmultiples (solution)
