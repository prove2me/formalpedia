-- Prove2me | solution 1 for MazurHuang.N19.exists_tate_parameters_of_order_nineteen
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T15:09:51.721961+00:00
-- url     : https://prove2.me/submissions/1cd551da-ae01-4a16-beb7-ecc5d72b11ab

/-
An order-nineteen point supplies nondegenerate Tate parameters
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Definitions.Def_MazurHuang_NineteenTatePolynomial
import Theorems.Thm_MazurHuang_exists_tate_normal_form_of_addOrderOf_gt_three
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_some_eq_some_div
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq

/-!
## Division-polynomial interface

The fork proves the two statements `KeystoneLadder.xRep_nsmul_same_xPair` and
`KeystoneLadder.nsmul_eq_zero_iff_ΨSq_eval` below by its own x-only Montgomery-ladder /
elliptic-divisibility-sequence development (13 modules `scratch.Ward*`, `scratch.Psi*`,
`scratch.Keystone*`).  The platform library already holds Proved theorems that contain these
facts in greater generality:

* `WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff` (`n • P = 0 ↔ ψₙ(P) = 0`),
* `WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div` (`x(nP) = Φₙ(x) / Ψₙ²(x)`),
* `WeierstrassCurve.isCoprime_Phi_PsiSq` (`Φₙ` and `Ψₙ²` are coprime).

This section re-derives the fork's two interface statements, with their original wording, from
those three theorems, so that the remaining source modules are used unchanged.  The hypotheses
`h4`, `hψ_ne`, `hc3` of the fork's statements are kept for source compatibility and are not used.
`SameP1Vec`, its two lemmas and `xPair` are copied from `scratch/KeystoneLadder.lean`.
-/
section KeystoneInterface

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Classical

namespace KeystoneLadder

variable {k : Type*} [Field k]

/-- Projective equality on Mathlib's `Fin 2` representatives, oriented as `v = c • u`
for a nonzero scalar `c`. This stronger orientation excludes the zero vector on the right. -/
def SameP1Vec (u v : Fin 2 → k) : Prop :=
  ∃ c : k, c ≠ 0 ∧ v = c • u

namespace SameP1Vec

lemma second_eq_zero_of_same_infty {v : Fin 2 → k}
    (h : SameP1Vec (![1, 0] : Fin 2 → k) v) : v 1 = 0 := by
  rcases h with ⟨c, _hc, rfl⟩
  simp

lemma second_ne_zero_of_same_affine {x : k} {v : Fin 2 → k}
    (h : SameP1Vec (![x, 1] : Fin 2 → k) v) : v 1 ≠ 0 := by
  rcases h with ⟨c, hc, rfl⟩
  simpa using hc

end SameP1Vec

/-- The division-polynomial representative `[Φₙ(x) : Ψₙ²(x)]` of `x(nP)`. -/
noncomputable def xPair (W : WeierstrassCurve k) (n : ℤ) (x : k) : Fin 2 → k :=
  ![(W.Φ n).eval x, (W.ΨSq n).eval x]

/-- On the curve, `ψₙ(x, y)² = Ψₙ²(x)`: the evaluation at a point of Mathlib's identities
`CoordinateRing.mk_ψ` and `CoordinateRing.mk_Ψ_sq` in the coordinate ring. -/
private theorem evalEval_ψ_sq_eq (V : WeierstrassCurve k) {x y : k}
    (h : V.toAffine.Equation x y) (n : ℤ) :
    (V.ψ n).evalEval x y ^ 2 = (V.ΨSq n).eval x := by
  have hmk : Affine.CoordinateRing.mk V (V.ψ n * V.ψ n) =
      Affine.CoordinateRing.mk V (C (V.ΨSq n)) := by
    rw [map_mul, Affine.CoordinateRing.mk_ψ, ← sq, Affine.CoordinateRing.mk_Ψ_sq]
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp hmk
  have h0 : (V.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_C] at h1
  rw [sq]
  exact h1

/-- The projective x-coordinate formula `x(nP) = [Φₙ(x) : Ψₙ²(x)]`, for a curve given directly
(no base change), assembled from the three platform theorems. -/
private theorem xRep_nsmul_same_xPair_core (V : WeierstrassCurve k) [V.IsElliptic]
    {n : ℕ} {x y : k} (h : V.toAffine.Nonsingular x y) :
    SameP1Vec
      ((n • (Point.some x y h : V.toAffine.Point)).xRep)
      (xPair V (n : ℤ) x) := by
  have hsq := evalEval_ψ_sq_eq V h.1 (n : ℤ)
  by_cases hψ : (V.ψ (n : ℤ)).evalEval x y = 0
  · have hzero : n • (Point.some x y h : V.toAffine.Point) = 0 := by
      rw [← natCast_zsmul]
      exact (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff V h (n : ℤ)).mpr hψ
    have hΨ : (V.ΨSq (n : ℤ)).eval x = 0 := by
      rw [← hsq, hψ]
      exact zero_pow two_ne_zero
    have hΦ : (V.Φ (n : ℤ)).eval x ≠ 0 := by
      obtain ⟨a, b, hab⟩ := WeierstrassCurve.isCoprime_Phi_PsiSq V (n : ℤ)
      intro hΦ0
      have h1 := congrArg (Polynomial.eval x) hab
      rw [eval_add, eval_mul, eval_mul, hΦ0, hΨ, mul_zero, mul_zero, add_zero, eval_one] at h1
      exact zero_ne_one h1
    rw [hzero, Point.xRep_zero]
    refine ⟨(V.Φ (n : ℤ)).eval x, hΦ, ?_⟩
    simp only [xPair, hΨ, Matrix.smul_cons, Matrix.smul_empty, smul_eq_mul, mul_one, mul_zero]
  · obtain ⟨y', h', hP⟩ :=
      WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div V h hψ
    have hΨ : (V.ΨSq (n : ℤ)).eval x ≠ 0 := by
      rw [← hsq]
      exact pow_ne_zero 2 hψ
    have hcross : (V.Φ (n : ℤ)).eval x =
        (V.ΨSq (n : ℤ)).eval x * ((V.Φ (n : ℤ)).eval x / (V.ΨSq (n : ℤ)).eval x) := by
      field_simp
    rw [← natCast_zsmul, hP, Point.xRep_some]
    refine ⟨(V.ΨSq (n : ℤ)).eval x, hΨ, ?_⟩
    simp only [xPair, Matrix.smul_cons, Matrix.smul_empty, smul_eq_mul, mul_one, ← hcross]

/-- The projective division-polynomial coordinate formula (statement as in
`scratch/KeystoneEDS.lean`). -/
theorem xRep_nsmul_same_xPair (W : WeierstrassCurve k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0)
    {n : ℕ} {x y : k} (h : (W⁄k).Nonsingular x y) :
    SameP1Vec
      ((n • (Point.some x y h : (W⁄k).Point)).xRep)
      (xPair W (n : ℤ) x) := by
  have hW : W.baseChange k = W := by
    first
      | exact W.map_id
      | (ext <;> simp [WeierstrassCurve.baseChange])
  have key : ∀ (V : WeierstrassCurve k) (_hV : V = W) (h' : V.toAffine.Nonsingular x y),
      SameP1Vec ((n • (Point.some x y h' : V.toAffine.Point)).xRep) (xPair W (n : ℤ) x) := by
    intro V hV h'
    subst hV
    exact xRep_nsmul_same_xPair_core V h'
  exact key (W.baseChange k) hW h

/-- Keystone target reduced to the projective division-polynomial coordinate formula
(statement and proof as in `scratch/KeystoneEDS.lean`). -/
theorem nsmul_eq_zero_iff_ΨSq_eval (W : WeierstrassCurve k) [W.IsElliptic]
    (h4 : (4 : k) ≠ 0) (hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (hc3 : W.Ψ₃ ≠ 0)
    {n : ℕ} {x y : k} (h : (W⁄k).Nonsingular x y) :
    n • (Point.some x y h : (W⁄k).Point) = 0 ↔ (W.ΨSq (n : ℤ)).eval x = 0 := by
  classical
  let P : (W⁄k).Point := Point.some x y h
  constructor
  · intro hn
    have hsame :
        SameP1Vec ((n • P).xRep) (xPair W (n : ℤ) x) :=
      xRep_nsmul_same_xPair (W := W) h4 hψ_ne hc3 (n := n) h
    have hsecond :=
      SameP1Vec.second_eq_zero_of_same_infty (v := xPair W (n : ℤ) x) (by
        simpa [P, hn] using hsame)
    simpa [xPair] using hsecond
  · intro hψ
    by_contra hn
    cases hnp : n • P with
    | zero =>
        exact hn hnp
    | some xn yn hnonsing =>
        have hsame :
            SameP1Vec ((n • P).xRep) (xPair W (n : ℤ) x) :=
          xRep_nsmul_same_xPair (W := W) h4 hψ_ne hc3 (n := n) h
        have hsecond_ne :
            (xPair W (n : ℤ) x) 1 ≠ 0 :=
          SameP1Vec.second_ne_zero_of_same_affine
            (x := xn) (v := xPair W (n : ℤ) x) (by
              simpa [hnp] using hsame)
        exact hsecond_ne (by simpa [xPair] using hψ)

end KeystoneLadder

end KeystoneInterface

-- Source scratch/TateZ2xZ10Reduction.lean:73-100; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section

open scoped WeierstrassCurve.Affine

namespace Scratch.TateZ2xZ10Reduction

noncomputable section

/-- The Tate normal form `y^2 + (1-c)xy - by = x^3 - bx^2`. -/
def tateNormalFormCurve (b c : ℚ) : WeierstrassCurve ℚ where
  a₁ := 1 - c
  a₂ := -b
  a₃ := -b
  a₄ := 0
  a₆ := 0

@[simp] lemma tateNormalFormCurve_a₁ (b c : ℚ) :
    (tateNormalFormCurve b c).a₁ = 1 - c := rfl

@[simp] lemma tateNormalFormCurve_a₂ (b c : ℚ) :
    (tateNormalFormCurve b c).a₂ = -b := rfl

@[simp] lemma tateNormalFormCurve_a₃ (b c : ℚ) :
    (tateNormalFormCurve b c).a₃ = -b := rfl

@[simp] lemma tateNormalFormCurve_a₄ (b c : ℚ) :
    (tateNormalFormCurve b c).a₄ = 0 := rfl

@[simp] lemma tateNormalFormCurve_a₆ (b c : ℚ) :
    (tateNormalFormCurve b c).a₆ = 0 := rfl
end
end Scratch.TateZ2xZ10Reduction
end

-- Source FLT/Assumptions/MazurProof/TateNormalFormBridge.lean:13-32; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section

open scoped WeierstrassCurve.Affine

namespace MazurProof.TateNormalFormBridge

open Scratch.TateZ2xZ10Reduction

noncomputable section

private lemma tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Nonsingular (tateNormalFormCurve b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [tateNormalFormCurve]

/-- The marked origin on Tate normal form. -/
def tateOrigin (b c : ℚ)
    [WeierstrassCurve.IsElliptic (tateNormalFormCurve b c)] :
    WeierstrassCurve.Affine.Point (tateNormalFormCurve b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular b c)

/-- The Tate-normal-form bridge with only the order and nonvanishing data (statement as in
`FLT/Assumptions/MazurProof/TateNormalFormBridge.lean`), here obtained from the published
theorem `MazurHuang.exists_tate_normal_form_of_addOrderOf_gt_three`, which states the same
fact with the curve and the marked point written out. -/
theorem exists_tate_normalized_of_addOrder_gt_three
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (n : ℕ) (hn : 3 < n)
    (hP : addOrderOf P = n) :
    ∃ b c : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (tateNormalFormCurve b c),
        addOrderOf (tateOrigin b c) = n ∧ b ≠ 0 := by
  obtain ⟨b, c, hb, hEll, _h, hord⟩ :=
    MazurHuang.exists_tate_normal_form_of_addOrderOf_gt_three E P n hn hP
  exact ⟨b, c, hEll, hord, hb⟩

end

end MazurProof.TateNormalFormBridge

end

-- Source FLT/Assumptions/MazurProof/TateOrder19.lean:5-258; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section

/-!
# The concrete order-19 Tate-normal-form condition

Parallels `TateOrder13` and `TateOrder17`: connects the Tate-normal-form
bridge, the division-polynomial recurrence, and the explicit identity
`ψ₁₉(0,0) = -(b¹²⁰ F₁₉(b,c))`.

A rational point of exact order 19 yields concrete Tate parameters
with `b ≠ 0` and `F19 b c = 0`.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOrder19

open Scratch.TateZ2xZ10Reduction

noncomputable section

private abbrev W (b c : ℚ) : WeierstrassCurve ℚ :=
  tateNormalFormCurve b c

private theorem psi_ne_zero_rat (W : WeierstrassCurve ℚ) :
    ∀ m : ℤ, m ≠ 0 → W.ψ m ≠ 0 := by
  have hψ₂_ne : W.ψ₂ ≠ 0 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact ne_of_apply_ne Polynomial.natDegree (by
      rw [Polynomial.natDegree_linear
        (Polynomial.C_ne_zero.mpr (two_ne_zero (α := ℚ))),
        Polynomial.natDegree_zero]
      omega)
  have hψ₂_deg : W.ψ₂.natDegree ≤ 1 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact Polynomial.natDegree_linear_le
  have hPsi_ne : ∀ n : ℕ, n ≠ 0 → W.Ψ (n : ℤ) ≠ 0 := by
    intro n hn
    rw [WeierstrassCurve.Ψ_ofNat]
    have hC : Polynomial.C (W.preΨ' n) ≠ 0 :=
      Polynomial.C_ne_zero.mpr
        (W.preΨ'_ne_zero (Nat.cast_ne_zero.mpr hn))
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      exact mul_ne_zero hC hψ₂_ne
    · simp only [heven, ↓reduceIte, mul_one]
      exact hC
  have hPsi_deg : ∀ n : ℕ, n ≠ 0 →
      (W.Ψ (n : ℤ)).natDegree < W.toAffine.polynomial.natDegree := by
    intro n _
    rw [WeierstrassCurve.Affine.natDegree_polynomial,
      WeierstrassCurve.Ψ_ofNat]
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      calc
        (Polynomial.C (W.preΨ' n) * W.ψ₂).natDegree
            ≤ 0 + 1 := Polynomial.natDegree_mul_le |>.trans
              (Nat.add_le_add (Polynomial.natDegree_C _).le hψ₂_deg)
        _ < 2 := by omega
    · simp only [heven, ↓reduceIte, mul_one]
      have hdeg : (Polynomial.C (W.preΨ' n)).natDegree = 0 :=
        Polynomial.natDegree_C _
      omega
  intro m hm hpsi
  suffices hPsi :
      WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (W.Ψ m) ≠ 0 by
    exact hPsi (by
      rw [← WeierstrassCurve.Affine.CoordinateRing.mk_ψ, hpsi, map_zero])
  rcases m with n | n
  · exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsi_ne n (by intro h; exact hm (by simp [h])))
      (hPsi_deg n (by intro h; exact hm (by simp [h])))
  · rw [show (Int.negSucc n : ℤ) = -(↑(n + 1) : ℤ) by
        simp [Int.negSucc_eq],
      WeierstrassCurve.Ψ_neg, map_neg, neg_ne_zero]
    exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsi_ne _ (Nat.succ_ne_zero n))
      (hPsi_deg _ (Nat.succ_ne_zero n))

private theorem nsmul_eq_zero_iff_PsiSq_eval
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {n : ℕ} {x y : ℚ} (h : (W⁄ℚ).Nonsingular x y) :
    n • (WeierstrassCurve.Affine.Point.some x y h : (W⁄ℚ).Point) = 0 ↔
      (W.ΨSq (n : ℤ)).eval x = 0 := by
  have h4 : (4 : ℚ) ≠ 0 := by norm_num
  have hc3 : W.Ψ₃ ≠ 0 :=
    WeierstrassCurve.Ψ₃_ne_zero W (by norm_num)
  have key := KeystoneLadder.nsmul_eq_zero_iff_ΨSq_eval
    W h4 (psi_ne_zero_rat W) hc3 (n := n) h
  convert key using 3
  congr
  exact Subsingleton.elim _ _

/-! ## Division polynomial recurrence evaluated at X=0

For preΨ'(19) we need intermediate values up to preΨ'(11):
  preΨ'(19) = preΨ'_odd 7, m = 7 (odd)
  preΨ'(19) = preΨ'(11) * preΨ'(9)³ - preΨ'(8) * preΨ'(10)³ * Ψ₂Sq²
-/

private lemma eval_prePsi_five (b c : ℚ) :
    ((W b c).preΨ' 5).eval 0 =
      ((W b c).preΨ₄).eval 0 * ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).Ψ₃.eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 0)
  simpa using h

private lemma eval_prePsi_six (b c : ℚ) :
    ((W b c).preΨ' 6).eval 0 =
      ((W b c).preΨ' 3).eval 0 * ((W b c).preΨ' 5).eval 0 -
        ((W b c).preΨ' 3).eval 0 * (((W b c).preΨ' 4).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 0)
  simpa using h

private lemma eval_prePsi_seven (b c : ℚ) :
    ((W b c).preΨ' 7).eval 0 =
      ((W b c).preΨ' 5).eval 0 * (((W b c).preΨ' 3).eval 0) ^ 3 -
        ((W b c).preΨ' 4).eval 0 ^ 3 * ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 1)
  simpa using h

private lemma eval_prePsi_eight (b c : ℚ) :
    ((W b c).preΨ' 8).eval 0 =
      (((W b c).preΨ' 3).eval 0) ^ 2 * ((W b c).preΨ' 4).eval 0 *
        ((W b c).preΨ' 6).eval 0 -
      ((W b c).preΨ' 4).eval 0 * (((W b c).preΨ' 5).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 1)
  simpa using h

private lemma eval_prePsi_nine (b c : ℚ) :
    ((W b c).preΨ' 9).eval 0 =
      ((W b c).preΨ' 6).eval 0 * (((W b c).preΨ' 4).eval 0) ^ 3 *
        ((W b c).Ψ₂Sq.eval 0) ^ 2 -
      ((W b c).preΨ' 3).eval 0 * (((W b c).preΨ' 5).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 2)
  simpa [show Even (2 : ℕ) by decide] using h

private lemma eval_prePsi_ten (b c : ℚ) :
    ((W b c).preΨ' 10).eval 0 =
      (((W b c).preΨ' 4).eval 0) ^ 2 * ((W b c).preΨ' 5).eval 0 *
        ((W b c).preΨ' 7).eval 0 -
      ((W b c).preΨ' 3).eval 0 * ((W b c).preΨ' 5).eval 0 *
        (((W b c).preΨ' 6).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 2)
  simpa using h

private lemma eval_prePsi_eleven (b c : ℚ) :
    ((W b c).preΨ' 11).eval 0 =
      ((W b c).preΨ' 7).eval 0 * (((W b c).preΨ' 5).eval 0) ^ 3 -
      ((W b c).preΨ' 4).eval 0 * (((W b c).preΨ' 6).eval 0) ^ 3 *
        ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 3)
  simpa [show ¬ Even (3 : ℕ) by decide] using h

private lemma eval_prePsi_nineteen (b c : ℚ) :
    ((W b c).preΨ' 19).eval 0 =
      ((W b c).preΨ' 11).eval 0 * (((W b c).preΨ' 9).eval 0) ^ 3 -
      ((W b c).preΨ' 8).eval 0 * (((W b c).preΨ' 10).eval 0) ^ 3 *
        ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 7)
  simpa [show ¬ Even (7 : ℕ) by decide] using h

set_option maxHeartbeats 0 in
theorem prePsi_nineteen_eval_tate_origin (b c : ℚ) :
    ((W b c).preΨ' 19).eval 0 =
      -(b ^ 120 * _root_.MazurProof.TateNFDivision.F19 b c) := by
  rw [eval_prePsi_nineteen, eval_prePsi_eleven, eval_prePsi_ten,
    eval_prePsi_nine, eval_prePsi_eight, eval_prePsi_seven,
    eval_prePsi_six, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, _root_.MazurProof.TateNFDivision.F19]
  ring

/-! ## Connection to torsion order -/

private lemma tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Nonsingular (W b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [W]

def tateOrigin (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Point (W b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular b c)

private lemma tateOrigin_eq_normalized_origin
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    tateOrigin b c = TateNormalFormBridge.tateOrigin b c := by
  change WeierstrassCurve.Affine.Point.some 0 0 _ =
    WeierstrassCurve.Affine.Point.some 0 0 _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

theorem F19_eq_zero_of_tateOrigin_order_nineteen
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    (hb : b ≠ 0) (hord : addOrderOf (tateOrigin b c) = 19) :
    _root_.MazurProof.TateNFDivision.F19 b c = 0 := by
  have h19 : (19 : ℕ) • tateOrigin b c = 0 := by
    simpa [hord] using addOrderOf_nsmul_eq_zero (tateOrigin b c)
  have hPsiSq : ((W b c).ΨSq (19 : ℤ)).eval 0 = 0 :=
    (nsmul_eq_zero_iff_PsiSq_eval (W b c)
      (tate_origin_nonsingular b c)).mp h19
  have hpre : ((W b c).preΨ' 19).eval 0 = 0 := by
    change ((W b c).ΨSq (19 : ℕ)).eval 0 = 0 at hPsiSq
    rw [(W b c).ΨSq_ofNat 19] at hPsiSq
    simpa [show ¬ Even (19 : ℕ) by decide] using hPsiSq
  rw [prePsi_nineteen_eval_tate_origin] at hpre
  have hpre' : b ^ 120 * _root_.MazurProof.TateNFDivision.F19 b c = 0 := neg_eq_zero.mp hpre
  exact (mul_eq_zero.mp hpre').resolve_left (pow_ne_zero 120 hb)

theorem tateOrigin_order_nineteen_of_F19_eq_zero
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    (_hb : b ≠ 0) (hF19 : _root_.MazurProof.TateNFDivision.F19 b c = 0) :
    addOrderOf (tateOrigin b c) = 19 := by
  have hpre : ((W b c).preΨ' 19).eval 0 = 0 := by
    rw [prePsi_nineteen_eval_tate_origin, hF19, mul_zero, neg_zero]
  have hPsiSq : ((W b c).ΨSq (19 : ℤ)).eval 0 = 0 := by
    change ((W b c).ΨSq (19 : ℕ)).eval 0 = 0
    rw [(W b c).ΨSq_ofNat 19]
    simp [show ¬ Even (19 : ℕ) by decide, hpre]
  have h19 : (19 : ℕ) • tateOrigin b c = 0 :=
    (nsmul_eq_zero_iff_PsiSq_eval (W b c)
      (tate_origin_nonsingular b c)).mpr hPsiSq
  have hne : tateOrigin b c ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero _
  letI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  exact addOrderOf_eq_prime h19 hne

theorem exists_tate_parameters_of_order_nineteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 19) :
    ∃ b c : ℚ,
      ∃ _hEll : WeierstrassCurve.IsElliptic (W b c),
        addOrderOf (tateOrigin b c) = 19 ∧
          b ≠ 0 ∧ _root_.MazurProof.TateNFDivision.F19 b c = 0 := by
  obtain ⟨b, c, hEll, hord, hb⟩ :=
    TateNormalFormBridge.exists_tate_normalized_of_addOrder_gt_three
      E P 19 (by norm_num) hP
  letI : WeierstrassCurve.IsElliptic (W b c) := hEll
  have horigin : addOrderOf (tateOrigin b c) = 19 := by
    rw [tateOrigin_eq_normalized_origin]
    exact hord
  exact ⟨b, c, inferInstance, horigin, hb,
    F19_eq_zero_of_tateOrigin_order_nineteen b c hb horigin⟩

end

end MazurProof.TateOrder19

end

open scoped WeierstrassCurve.Affine
theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) (hP : addOrderOf P = 19) :
    ∃ b c : ℚ, b ≠ 0 ∧ MazurProof.TateNFDivision.F19 b c = 0 := by
  obtain ⟨b, c, _hEll, _hord, hb, hF⟩ :=
    MazurProof.TateOrder19.exists_tate_parameters_of_order_nineteen E P hP
  exact ⟨b, c, hb, hF⟩
