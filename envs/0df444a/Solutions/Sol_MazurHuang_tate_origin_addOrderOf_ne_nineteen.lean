-- Prove2me | solution 1 for MazurHuang.tate_origin_addOrderOf_ne_nineteen
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-07T17:23:48.143977+00:00
-- url     : https://prove2.me/submissions/61e5d2e5-e67b-4a03-bdae-18a0e8e5c0e8

import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_MazurHuang_diamond_quotient_x_eq_zero

set_option maxHeartbeats 1000000

-- ===== FLT.Assumptions.MazurProof.TateNFDivision =====
section
/-!
# Division polynomials at the Tate normal form origin

For the Tate normal form `y² + (1-c)xy - by = x³ - bx²` with marked point
`P = (0,0)`, the division polynomials `ψₙ` evaluated at `P` factor as
`ψₙ(P) = b^eₙ · Fₙ(b,c)` where `Fₙ` is a small polynomial.

The condition "P has exact order n" is `Fₙ(b,c) = 0` (with `b ≠ 0` and
nonsingularity).  These compact factors are the foundation for all cyclic
torsion exclusions via Tate normal form.

## References

* Kubert, "Universal bounds on the torsion of elliptic curves", 1976
* The division polynomial recurrence specialized at the origin
-/

namespace MazurProof.TateNFDivision

variable {K : Type*} [Field K]

/-! ## Tate normal form curve and origin -/


/-! ## Weierstrass invariants of the Tate normal form -/





/-! ## Compact factors of ψₙ(0,0) / b^eₙ

These are the NON-trivial factors after removing the power of `b`.
The order-n condition at the Tate origin is `Fₙ(b,c) = 0`.
-/










/-- `-ψ₁₉(0,0) / b¹²⁰`.  80 monomials, total degree 15–24. -/
def F19 (b c : K) : K :=
    b ^ 15
      - 10 * b ^ 14 * c
      - 20 * b ^ 13 * c ^ 3
      + 45 * b ^ 13 * c ^ 2
      + 69 * b ^ 12 * c ^ 5
      + 195 * b ^ 12 * c ^ 4
      - 120 * b ^ 12 * c ^ 3
      - 121 * b ^ 11 * c ^ 7
      - 588 * b ^ 11 * c ^ 6
      - 861 * b ^ 11 * c ^ 5
      + 210 * b ^ 11 * c ^ 4
      + 105 * b ^ 10 * c ^ 9
      + 870 * b ^ 10 * c ^ 8
      + 2235 * b ^ 10 * c ^ 7
      + 2275 * b ^ 10 * c ^ 6
      - 252 * b ^ 10 * c ^ 5
      - 48 * b ^ 9 * c ^ 11
      - 585 * b ^ 9 * c ^ 10
      - 2720 * b ^ 9 * c ^ 9
      - 4995 * b ^ 9 * c ^ 8
      - 4005 * b ^ 9 * c ^ 7
      + 210 * b ^ 9 * c ^ 6
      + 11 * b ^ 8 * c ^ 13
      + 183 * b ^ 8 * c ^ 12
      + 1320 * b ^ 8 * c ^ 11
      + 4851 * b ^ 8 * c ^ 10
      + 7290 * b ^ 8 * c ^ 9
      + 4950 * b ^ 8 * c ^ 8
      - 120 * b ^ 8 * c ^ 7
      - b ^ 7 * c ^ 15
      - 21 * b ^ 7 * c ^ 14
      - 231 * b ^ 7 * c ^ 13
      - 1531 * b ^ 7 * c ^ 12
      - 5466 * b ^ 7 * c ^ 11
      - 7308 * b ^ 7 * c ^ 10
      - 4410 * b ^ 7 * c ^ 9
      + 45 * b ^ 7 * c ^ 8
      + 120 * b ^ 6 * c ^ 14
      + 990 * b ^ 6 * c ^ 13
      + 4117 * b ^ 6 * c ^ 12
      + 5166 * b ^ 6 * c ^ 11
      + 2862 * b ^ 6 * c ^ 10
      - 10 * b ^ 6 * c ^ 9
      - 34 * b ^ 5 * c ^ 16
      - 165 * b ^ 5 * c ^ 15
      - 465 * b ^ 5 * c ^ 14
      - 2190 * b ^ 5 * c ^ 13
      - 2610 * b ^ 5 * c ^ 12
      - 1350 * b ^ 5 * c ^ 11
      + b ^ 5 * c ^ 10
      + 25 * b ^ 4 * c ^ 18
      + 150 * b ^ 4 * c ^ 17
      + 363 * b ^ 4 * c ^ 16
      + 320 * b ^ 4 * c ^ 15
      + 885 * b ^ 4 * c ^ 14
      + 945 * b ^ 4 * c ^ 13
      + 455 * b ^ 4 * c ^ 12
      - 6 * b ^ 3 * c ^ 20
      - 45 * b ^ 3 * c ^ 19
      - 161 * b ^ 3 * c ^ 18
      - 333 * b ^ 3 * c ^ 17
      - 225 * b ^ 3 * c ^ 16
      - 281 * b ^ 3 * c ^ 15
      - 240 * b ^ 3 * c ^ 14
      - 105 * b ^ 3 * c ^ 13
      + b ^ 2 * c ^ 22
      + 6 * b ^ 2 * c ^ 21
      + 21 * b ^ 2 * c ^ 20
      + 56 * b ^ 2 * c ^ 19
      + 126 * b ^ 2 * c ^ 18
      + 81 * b ^ 2 * c ^ 17
      + 61 * b ^ 2 * c ^ 16
      + 39 * b ^ 2 * c ^ 15
      + 15 * b ^ 2 * c ^ 14
      - 15 * b * c ^ 19
      - 10 * b * c ^ 18
      - 6 * b * c ^ 17
      - 3 * b * c ^ 16
      - b * c ^ 15
      - c ^ 21

/-! ## Expanded forms (useful for ring-level reasoning) -/







/-! ## Two-division polynomial (for rational 2-torsion detection) -/



/-! ## Relation to Weierstrass invariants -/


/-! ## Order conditions at the Tate origin

Exact order `n` at the origin means `Fₙ(b,c) = 0` and all proper divisor
conditions are nonzero.
-/








/-! ## Composite order systems via coprime decomposition -/








end MazurProof.TateNFDivision

end

-- ===== scratch.TateZ2xZ10Reduction =====
section
/-!
# Tate-normal-form reduction layer for `ZMod 2 × ZMod 10`

This file builds the forward-direction reduction up to the current formal wall.

API survey, from the local tree and Mathlib as used here:

* Nonzero affine coordinates.  `WeierstrassCurve.Affine.Point W` is the
  inductive type `zero | some x y h`.  Mathlib provides `Point.mk`,
  `Point.some_ne_zero`, and `Point.xRep`; there is no `Point.pointEquiv` in the
  local Mathlib checkout.  No extra abstraction is needed to extract `(x,y)`
  from a proof `P ≠ 0`: case-splitting on `P` gives the affine coordinates.

* Variable changes.  `WeierstrassCurve.VariableChange R` exists and acts on
  Weierstrass curves by `(X,Y) ↦ (u^2 X + r, u^3 Y + u^2 s X + t)`.  The hard
  Mathlib survey for this file found the following.

  * `Mathlib/AlgebraicGeometry/EllipticCurve/VariableChange.lean` provides the
    curve-level group action, coefficient formulas `variableChange_a₁` through
    `variableChange_a₆`, preservation of `IsElliptic`, base-change compatibility
    for variable changes, and `variableChange_j`.
  * `Affine.Basic` provides ring-hom/base-change transport for equations and
    nonsingularity, plus only a specialized
    `equation_iff_variableChange`/`nonsingular_iff_variableChange` for translating
    a point to `(0,0)`.  It does not provide a general point map for
    `(u,r,s,t)`.
  * `Affine.Point` provides `Point.map` only for base change along algebra
    homomorphisms; its `map_add'` proof uses the affine addition formulas under
    ring homs.  There is no `Point.mapEquiv`, `Affine.map`, or `≃+` for
    variable changes.
  * `Jacobian.Point` provides `toAffineAddEquiv` between Jacobian and affine
    point groups and base-change lemmas for Jacobian formulas, but no
    `VariableChange` action on Jacobian/projective point classes.
  * `IsomOfJ.lean` constructs curve-level variable changes from equal
    `j`-invariants; it does not construct point-group isomorphisms.

  Consequently the point-level transport below is built directly.  The forward
  map sends an old affine point `(x,y)` on `W` to the new coordinates
  `X = u^{-2}(x-r)`, `Y = u^{-3}(y-s(x-r)-t)` on `C • W`; the inverse map uses
  the defining coordinate formulas.  The additive proof reduces to the affine
  slope identity `ℓ' = u^{-1}(ℓ-s)` and ring-checked equivariance of `addX` and
  `addY`.

* Computing `n • P`.  The affine point file has explicit group-law lemmas:
  `Point.add_of_X_ne`, `Point.add_of_Y_eq`, `Point.add_self_of_Y_eq`,
  `Point.add_self_of_Y_ne`, and the underlying formulas `slope`, `addX`,
  `addY`.  This supports direct coordinate calculations, as in the existing
  obstruction files.  Mathlib does not provide Tate normal form, Kubert's
  order-10 table, or a canned theorem that a point of order `10` can be
  normalized to `(0,0)` with the roadmap's `b,c` formulas.

* Division polynomials.  `DivisionPolynomial/Basic.lean` defines
  `ψ₂`, `Ψ₂Sq`, `Ψ₃`, `preΨ₄`, `preΨ`, `ΨSq`, `Ψ`, `ψ`, `Φ`, and `φ`, with
  map/base-change lemmas; `DivisionPolynomial/Degree.lean` proves degree and
  leading-coefficient facts.  The only direct bridge to the 2-torsion cubic is
  `Ψ₂Sq_eq : W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly`.  The survey found no
  theorem connecting `P` satisfying `n • P = 0` or `addOrderOf P = n` to
  evaluating `ψ n`, `Ψ n`, `preΨ n`, or `Φ n` at the coordinates of `P`.
  Thus division polynomials do not currently avoid the explicit `5P`
  group-law computation needed for order `10`.

The proven content below is split accordingly:

* the pure finite-group extraction from an injective `ZMod 2 × ZMod 10`;
* raw Tate-normal-form and change-of-variable algebra;
* one precisely named helper marking the missing point-level group-law
  preservation/normalization theorem.
-/

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

-- ===== scratch.KeystoneEDS =====
section
/-! Replacement for the Keystone EDS export: the multiplication-by-`n` criterion
`n • P = 0 ↔ ΨSqₙ(x) = 0`, derived from the platform theorem
`WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff`. -/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace KeystoneLadder

theorem evalEval_ψ_sq {k : Type*} [Field k] (W : WeierstrassCurve k) {x y : k}
    (h : W.toAffine.Equation x y) (n : ℤ) :
    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x := by
  have hmk : CoordinateRing.mk W.toAffine (W.ψ n ^ 2) =
      CoordinateRing.mk W.toAffine (C (W.ΨSq n)) := by
    rw [map_pow, CoordinateRing.mk_ψ, CoordinateRing.mk_Ψ_sq]
  obtain ⟨q, hq⟩ := AdjoinRoot.mk_eq_mk.mp hmk
  have he : (W.ψ n ^ 2 - C (W.ΨSq n)).evalEval x y = 0 := by
    rw [hq, evalEval_mul, h, zero_mul]
  rw [evalEval_sub, evalEval_pow, evalEval_C, sub_eq_zero] at he
  exact he

theorem nsmul_eq_zero_iff_ΨSq_eval {k : Type*} [Field k] [DecidableEq k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (_h4 : (4 : k) ≠ 0) (_hψ_ne : ∀ n : ℤ, n ≠ 0 → W.ψ n ≠ 0) (_hc3 : W.Ψ₃ ≠ 0)
    {n : ℕ} {x y : k} (h : (W⁄k).Nonsingular x y) :
    n • (Point.some x y h : (W⁄k).Point) = 0 ↔ (W.ΨSq (n : ℤ)).eval x = 0 := by
  have key := WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff W h (n : ℤ)
  rw [← evalEval_ψ_sq W h.1 (n : ℤ), pow_eq_zero_iff two_ne_zero, ← key, natCast_zsmul]
  rfl

end KeystoneLadder

end

-- ===== FLT.Assumptions.MazurProof.TateOrder19 =====
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
  exact key

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
      -(b ^ 120 * TateNFDivision.F19 b c) := by
  rw [eval_prePsi_nineteen, eval_prePsi_eleven, eval_prePsi_ten,
    eval_prePsi_nine, eval_prePsi_eight, eval_prePsi_seven,
    eval_prePsi_six, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, TateNFDivision.F19]
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


theorem F19_eq_zero_of_tateOrigin_order_nineteen
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    (hb : b ≠ 0) (hord : addOrderOf (tateOrigin b c) = 19) :
    TateNFDivision.F19 b c = 0 := by
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
  have hpre' : b ^ 120 * TateNFDivision.F19 b c = 0 := neg_eq_zero.mp hpre
  exact (mul_eq_zero.mp hpre').resolve_left (pow_ne_zero 120 hb)



end

end MazurProof.TateOrder19

end

-- ===== FLT.Assumptions.MazurProof.N19SutherlandModels =====
section
/-!
# Explicit affine models for the order-nineteen Tate equation

This file records Sutherland's raw and optimized affine models of `X₁(19)`.
It also gives the direct algebraic quotient of the optimized model by the
order-three diamond action:

`V² + V = U³ + U² + U`.

All maps are verified by polynomial identities.  No modular interpretation
of the formulas is used below.
-/

namespace MazurProof.N19SutherlandModels

noncomputable section

/-! ## The raw and optimized equations -/

/-- Sutherland's raw equation in the Tate parameters
`b = r s (r - 1)` and `c = s (r - 1)`. -/
def rawF19 (r s : ℚ) : ℚ :=
    r ^ 6
      - r ^ 5 * s ^ 7 + 11 * r ^ 5 * s ^ 6 - 48 * r ^ 5 * s ^ 5
      + 105 * r ^ 5 * s ^ 4 - 121 * r ^ 5 * s ^ 3
      + 69 * r ^ 5 * s ^ 2 - 20 * r ^ 5 * s - r ^ 5
      - 2 * r ^ 4 * s ^ 7 + 12 * r ^ 4 * s ^ 6 - 9 * r ^ 4 * s ^ 5
      - 60 * r ^ 4 * s ^ 4 + 144 * r ^ 4 * s ^ 3
      - 105 * r ^ 4 * s ^ 2 + 35 * r ^ 4 * s
      - 3 * r ^ 3 * s ^ 7 + 3 * r ^ 3 * s ^ 6 + 21 * r ^ 3 * s ^ 5
      - 30 * r ^ 3 * s ^ 4 - 41 * r ^ 3 * s ^ 3
      + 51 * r ^ 3 * s ^ 2 - 21 * r ^ 3 * s
      + r ^ 2 * s ^ 9 - 6 * r ^ 2 * s ^ 8 + 21 * r ^ 2 * s ^ 7
      - 50 * r ^ 2 * s ^ 6 + 66 * r ^ 2 * s ^ 5
      - 31 * r ^ 2 * s ^ 4 + 25 * r ^ 2 * s ^ 3
      - 18 * r ^ 2 * s ^ 2 + 7 * r ^ 2 * s
      + 3 * r * s ^ 6 - 15 * r * s ^ 5 + 10 * r * s ^ 4
      - 6 * r * s ^ 3 + 3 * r * s ^ 2 - r * s + s ^ 6

set_option maxHeartbeats 0 in
/-- The repository division factor and the raw equation differ only by
the displayed Tate-boundary factors. -/
theorem F19_raw_identity (r s : ℚ) :
    TateNFDivision.F19 (r * s * (r - 1)) (s * (r - 1)) =
      s ^ 15 * (r - 1) ^ 24 * rawF19 r s := by
  simp only [TateNFDivision.F19, rawF19]
  ring

/-- Sutherland's optimized affine plane equation for `X₁(19)`. -/
def optF19 (x y : ℚ) : ℚ :=
    y ^ 5
      - (x ^ 2 + 2) * y ^ 4
      - (2 * x ^ 3 + 2 * x ^ 2 + 2 * x - 1) * y ^ 3
      + (x ^ 5 + 3 * x ^ 4 + 7 * x ^ 3 + 6 * x ^ 2 + 2 * x) * y ^ 2
      - (x ^ 5 + 2 * x ^ 4 + 4 * x ^ 3 + 3 * x ^ 2) * y
      + x ^ 3 + x ^ 2

/-! ## The raw-to-optimized chart -/

/-- The common denominator in Sutherland's raw-to-optimized chart. -/
def rawDelta (r s : ℚ) : ℚ :=
  r * s ^ 2 - 3 * r * s + r + s ^ 2

/-- The first numerator in the raw-to-optimized chart. -/
def rawXFactor (r s : ℚ) : ℚ :=
  r * s - 2 * r + 1

/-- The horizontal coordinate in Sutherland's optimized chart. -/
def rawToOptX (r s : ℚ) : ℚ :=
  -(s - 1) * rawXFactor r s / rawDelta r s

/-- The second numerator in the raw-to-optimized chart. -/
def rawYNumerator (r s : ℚ) : ℚ :=
  r ^ 2 * s - 3 * r ^ 2 + r * s + 3 * r - s ^ 2 - 1

/-- The vertical coordinate in Sutherland's optimized chart. -/
def rawToOptY (r s : ℚ) : ℚ :=
  (s - 1) * rawYNumerator r s / ((r - s) * rawDelta r s)

/-- Specializing the raw equation to `r=s` leaves only boundary factors. -/
theorem rawF19_r_eq_s (s : ℚ) :
    rawF19 s s = -s ^ 2 * (s - 1) ^ 10 := by
  simp only [rawF19]
  ring

/-- Specializing the raw equation to `s=1` leaves the factor `(r-1)⁶`. -/
theorem rawF19_s_one (r : ℚ) :
    rawF19 r 1 = (r - 1) ^ 6 := by
  simp only [rawF19]
  ring

/-- The raw equation after solving `rawXFactor r s = 0` for `s`. -/
theorem rawF19_x_factor_zero (r : ℚ) (hr : r ≠ 0) :
    rawF19 r ((2 * r - 1) / r) = (r - 1) ^ 13 / r ^ 7 := by
  simp only [rawF19]
  field_simp [hr]
  ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The raw equation after solving `rawDelta r s = 0` for `r`. -/
theorem rawF19_delta_zero (s : ℚ) (hsq : s ^ 2 - 3 * s + 1 ≠ 0) :
    rawF19 (-s ^ 2 / (s ^ 2 - 3 * s + 1)) s =
      s ^ 3 * (s - 1) ^ 18 / (s ^ 2 - 3 * s + 1) ^ 6 := by
  let q : ℚ := s ^ 2 - 3 * s + 1
  have hq : q ≠ 0 := by simpa [q] using hsq
  change rawF19 (-s ^ 2 / q) s = s ^ 3 * (s - 1) ^ 18 / q ^ 6
  apply (eq_div_iff (pow_ne_zero 6 hq)).2
  simp only [rawF19]
  field_simp [hq]
  dsimp only [q]
  ring

/-- A nonboundary raw point does not lie on the diagonal `r=s`. -/
theorem raw_r_sub_s_ne_zero {r s : ℚ}
    (hs : s ≠ 0) (hr1 : r - 1 ≠ 0) (hraw : rawF19 r s = 0) :
    r - s ≠ 0 := by
  intro hrs
  have hrseq : r = s := sub_eq_zero.mp hrs
  rw [hrseq, rawF19_r_eq_s] at hraw
  exact (mul_ne_zero
    (neg_ne_zero.mpr (pow_ne_zero 2 hs))
    (pow_ne_zero 10 (sub_ne_zero.mpr (by
      intro h
      apply hr1
      rw [hrseq, h]
      norm_num)))) hraw

/-- A nonboundary raw point has `s ≠ 1`. -/
theorem raw_s_sub_one_ne_zero {r s : ℚ}
    (hr1 : r - 1 ≠ 0) (hraw : rawF19 r s = 0) :
    s - 1 ≠ 0 := by
  intro hs
  have hseq : s = 1 := sub_eq_zero.mp hs
  rw [hseq, rawF19_s_one] at hraw
  exact pow_ne_zero 6 hr1 hraw

/-- The first horizontal numerator is nonzero at a nonboundary raw point. -/
theorem rawXFactor_ne_zero {r s : ℚ}
    (hr : r ≠ 0) (hr1 : r - 1 ≠ 0) (hraw : rawF19 r s = 0) :
    rawXFactor r s ≠ 0 := by
  intro hx
  have hs : s = (2 * r - 1) / r := by
    apply (eq_div_iff hr).2
    simp only [rawXFactor] at hx
    linarith
  rw [hs, rawF19_x_factor_zero r hr] at hraw
  have : (r - 1) ^ 13 = 0 := by
    simpa [pow_ne_zero 7 hr] using hraw
  exact hr1 (eq_zero_of_pow_eq_zero this)

/-- The common chart denominator is nonzero at a nonboundary raw point. -/
theorem rawDelta_ne_zero {r s : ℚ}
    (hs : s ≠ 0) (hr1 : r - 1 ≠ 0) (hraw : rawF19 r s = 0) :
    rawDelta r s ≠ 0 := by
  intro hdelta
  have hcoef : s ^ 2 - 3 * s + 1 ≠ 0 := by
    intro hzero
    have hs2 : s ^ 2 = 0 := by
      simp only [rawDelta] at hdelta
      linear_combination hdelta - r * hzero
    exact hs (eq_zero_of_pow_eq_zero hs2)
  have hr : r = -s ^ 2 / (s ^ 2 - 3 * s + 1) := by
    apply (eq_div_iff hcoef).2
    simp only [rawDelta] at hdelta
    linear_combination hdelta
  rw [hr, rawF19_delta_zero s hcoef] at hraw
  have hprod : s ^ 3 * (s - 1) ^ 18 = 0 := by
    simpa [pow_ne_zero 6 hcoef] using hraw
  rcases mul_eq_zero.mp hprod with hs3 | hs1
  · exact hs (eq_zero_of_pow_eq_zero hs3)
  · have hsone : s = 1 := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hs1)
    rw [hsone] at hr
    norm_num at hr
    exact hr1 (sub_eq_zero.mpr hr)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The raw-to-optimized chart carries the raw equation to the optimized
equation, with an explicit residual factor. -/
theorem raw_to_opt_residual_identity {r s : ℚ}
    (hrs : r - s ≠ 0) (hdelta : rawDelta r s ≠ 0) :
    optF19 (rawToOptX r s) (rawToOptY r s) =
      (s - 1) ^ 2 * (s ^ 2 - r - s + 1) ^ 2 *
          rawXFactor r s ^ 4 /
        ((s - r) ^ 5 * rawDelta r s ^ 7) * rawF19 r s := by
  simp only [optF19, rawToOptX, rawToOptY]
  have hsr : s - r ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hrs))
  have hry : (r - s) * rawDelta r s ≠ 0 :=
    mul_ne_zero hrs hdelta
  field_simp [hrs, hsr, hdelta, hry]
  simp only [rawYNumerator, rawXFactor, rawDelta, rawF19]
  ring

/-- The optimized horizontal coordinate is nonzero on the nonboundary
raw locus. -/
theorem rawToOptX_ne_zero {r s : ℚ}
    (hs1 : s - 1 ≠ 0) (hx : rawXFactor r s ≠ 0)
    (hdelta : rawDelta r s ≠ 0) :
    rawToOptX r s ≠ 0 := by
  exact div_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr hs1) hx) hdelta

/-! ## The order-three quotient of the optimized model -/

/-- Numerator of the horizontal quotient coordinate. -/
def diamondUNumerator (x y : ℚ) : ℚ :=
    y ^ 4
      - (x ^ 2 + 1) * y ^ 3
      - x * (2 * x ^ 2 + 3 * x + 1) * y ^ 2
      + x ^ 2 * (x ^ 3 + 3 * x ^ 2 + 5 * x + 4) * y
      - x ^ 2 * (x + 1)

/-- Numerator of the vertical quotient coordinate. -/
def diamondVNumerator (x y : ℚ) : ℚ :=
    (x + 1) * y ^ 4
      - (x ^ 3 + x ^ 2 + x + 1) * y ^ 3
      - x * (2 * x ^ 3 + 5 * x ^ 2 + 4 * x + 1) * y ^ 2
      + x ^ 2 * (x ^ 4 + 4 * x ^ 3 + 8 * x ^ 2 + 9 * x + 5) * y
      - x ^ 2 * (x ^ 2 + 3 * x + 2)

/-- Horizontal coordinate on the genus-one diamond quotient. -/
def diamondU (x y : ℚ) : ℚ :=
  diamondUNumerator x y / x ^ 3

/-- Vertical coordinate on the genus-one diamond quotient. -/
def diamondV (x y : ℚ) : ℚ :=
  diamondVNumerator x y / x ^ 3

/-- Residual of the elliptic equation `V²+V=U³+U²+U`. -/
def diamondResidual (u v : ℚ) : ℚ :=
  v ^ 2 + v - u ^ 3 - u ^ 2 - u

/-- Polynomial certificate for the quotient residual identity. -/
def diamondCertificate (x y : ℚ) : ℚ :=
    y ^ 7
      - (2 * x ^ 2 + 1) * y ^ 6
      + (x ^ 4 - 4 * x ^ 3 - 6 * x ^ 2 - x) * y ^ 5
      + (6 * x ^ 5 + 13 * x ^ 4 + 11 * x ^ 3 + 9 * x ^ 2) * y ^ 4
      + (-2 * x ^ 7 - 2 * x ^ 6 + 5 * x ^ 5 + 6 * x ^ 4 -
          2 * x ^ 2) * y ^ 3
      + (-4 * x ^ 8 - 19 * x ^ 7 - 38 * x ^ 6 - 41 * x ^ 5 -
          21 * x ^ 4 - x ^ 3) * y ^ 2
      + (x ^ 10 + 6 * x ^ 9 + 17 * x ^ 8 + 29 * x ^ 7 +
          32 * x ^ 6 + 23 * x ^ 5 + 9 * x ^ 4) * y
      - x ^ 8 - 4 * x ^ 7 - 7 * x ^ 6 - 5 * x ^ 5 - x ^ 4

set_option maxHeartbeats 0 in
/-- The explicit quotient coordinates satisfy the genus-one equation on the
optimized order-nineteen locus. -/
theorem diamond_residual_identity {x y : ℚ} (hx : x ≠ 0) :
    diamondResidual (diamondU x y) (diamondV x y) =
      -diamondCertificate x y * optF19 x y / x ^ 9 := by
  simp only [diamondResidual, diamondU, diamondV, diamondUNumerator,
    diamondVNumerator, diamondCertificate, optF19]
  field_simp [hx]
  ring

/-! ## The zero horizontal fibre -/

/-- First coefficient in the Bézout certificate for the zero horizontal
fibre of the diamond quotient. -/
def zeroFiberBezoutA (x y : ℚ) : ℚ :=
    (x ^ 2 - x - 1) * y ^ 3
      + (-x ^ 4 + x ^ 3 - x) * y ^ 2
      + (-2 * x ^ 5 - x ^ 4 + 5 * x ^ 3 + 3 * x ^ 2) * y
      + x ^ 7 + 2 * x ^ 6 + 2 * x ^ 5 + x ^ 4 - x ^ 3 - x ^ 2

/-- Second coefficient in the Bézout certificate for the zero horizontal
fibre of the diamond quotient. -/
def zeroFiberBezoutB (x y : ℚ) : ℚ :=
    (-x ^ 2 + x + 1) * y ^ 4
      + (x ^ 4 - x ^ 3 + x ^ 2 - 1) * y ^ 3
      + (2 * x ^ 5 - 3 * x ^ 3 - 4 * x ^ 2 - 2 * x) * y ^ 2
      + (-x ^ 7 - 2 * x ^ 6 - 4 * x ^ 5 - x ^ 4 +
          4 * x ^ 3 + 2 * x ^ 2) * y
      + x ^ 7 + x ^ 6 + x ^ 5 + x ^ 4 - x ^ 3 - x ^ 2

/-- The optimized equation and the zero horizontal numerator force
`x⁷(x+1)²=0`. -/
theorem zero_fiber_bezout (x y : ℚ) :
    zeroFiberBezoutA x y * optF19 x y +
        zeroFiberBezoutB x y * diamondUNumerator x y =
      x ^ 7 * (x + 1) ^ 2 := by
  simp only [zeroFiberBezoutA, zeroFiberBezoutB, optF19,
    diamondUNumerator]
  ring

/-- A nonzero optimized point in the zero horizontal fibre has `x=-1`. -/
theorem x_eq_neg_one_of_diamondU_eq_zero {x y : ℚ}
    (hx : x ≠ 0) (hopt : optF19 x y = 0)
    (hU : diamondU x y = 0) :
    x = -1 := by
  have hUN : diamondUNumerator x y = 0 := by
    simp only [diamondU] at hU
    exact (div_eq_zero_iff).mp hU |>.resolve_right (pow_ne_zero 3 hx)
  have hprod : x ^ 7 * (x + 1) ^ 2 = 0 := by
    rw [← zero_fiber_bezout x y, hopt, hUN]
    ring
  have hplus : (x + 1) ^ 2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 7 hx)
  linarith [eq_zero_of_pow_eq_zero hplus]

/-- The equation `rawToOptX r s = -1` forces a boundary point of the raw
order-nineteen equation. -/
theorem rawToOptX_ne_neg_one {r s : ℚ}
    (hs : s ≠ 0) (hr1 : r - 1 ≠ 0) (hraw : rawF19 r s = 0)
    (hdelta : rawDelta r s ≠ 0) :
    rawToOptX r s ≠ -1 := by
  intro hx
  have hboundary : s ^ 2 - r - s + 1 = 0 := by
    simp only [rawToOptX] at hx
    field_simp [hdelta] at hx
    simp only [rawXFactor, rawDelta] at hx
    linear_combination hx
  have hr : r = s ^ 2 - s + 1 := by
    linarith
  rw [hr] at hraw hr1
  have hspecial : rawF19 (s ^ 2 - s + 1) s =
      -s * (s - 1) ^ 16 := by
    simp only [rawF19]
    ring
  rw [hspecial] at hraw
  have hs1 : s - 1 = 0 :=
    eq_zero_of_pow_eq_zero
      ((mul_eq_zero.mp hraw).resolve_left (neg_ne_zero.mpr hs))
  apply hr1
  rw [sub_eq_zero.mp hs1]
  norm_num

end

end MazurProof.N19SutherlandModels

end

-- ===== FLT.Assumptions.MazurProof.TateOrder19Quotient =====
section
/-!
# The algebraic order-nineteen quotient argument

The only arithmetic input to this file is the statement that every affine
rational point on

`v² + v = u³ + u² + u`

has `u=0`.  From that input, the explicit identities in
`N19SutherlandModels` exclude every rational solution of the Tate division
factor `F₁₉(b,c)=0` with `b ≠ 0`.

This is a direct algebraic proof.  It does not use a modular interpretation
of either affine model or of the quotient map.
-/

namespace MazurProof.TateOrder19Quotient

open N19SutherlandModels

noncomputable section

set_option maxHeartbeats 0 in
/-- The rational-point classification of the genus-one quotient implies the
global nonvanishing statement required by the order-nineteen exclusion. -/
theorem no_F19_rational_solution_of_diamond_x_eq_zero
    (hclass :
      ∀ u v : ℚ, diamondResidual u v = 0 → u = 0)
    (b c : ℚ) (hb : b ≠ 0) :
    TateNFDivision.F19 b c ≠ 0 := by
  intro hF19
  have hc : c ≠ 0 := by
    intro hc
    subst c
    norm_num [TateNFDivision.F19] at hF19
    exact hb hF19
  have hbc : b - c ≠ 0 := by
    intro hbc
    have hbeq : b = c := sub_eq_zero.mp hbc
    rw [hbeq] at hF19 hb
    norm_num [TateNFDivision.F19] at hF19
    ring_nf at hF19
    exact hb (eq_zero_of_pow_eq_zero hF19)
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hr : r ≠ 0 := by
    exact div_ne_zero hb hc
  have hs : s ≠ 0 := by
    exact div_ne_zero (pow_ne_zero 2 hc) hbc
  have hr1 : r - 1 ≠ 0 := by
    intro hr1
    have hrEq : r = 1 := sub_eq_zero.mp hr1
    apply hbc
    dsimp [r] at hrEq
    field_simp [hc] at hrEq
    linarith
  have hcCoord : c = s * (r - 1) := by
    dsimp [r, s]
    field_simp [hc, hbc]
  have hbCoord : b = r * s * (r - 1) := by
    calc
      b = r * c := by
        dsimp [r]
        field_simp [hc]
      _ = r * s * (r - 1) := by rw [hcCoord]; ring
  have hraw : rawF19 r s = 0 := by
    rw [hbCoord, hcCoord, F19_raw_identity] at hF19
    exact (mul_eq_zero.mp hF19).resolve_left
      (mul_ne_zero (pow_ne_zero 15 hs) (pow_ne_zero 24 hr1))
  have hrs : r - s ≠ 0 :=
    raw_r_sub_s_ne_zero hs hr1 hraw
  have hs1 : s - 1 ≠ 0 :=
    raw_s_sub_one_ne_zero hr1 hraw
  have hxFactor : rawXFactor r s ≠ 0 :=
    rawXFactor_ne_zero hr hr1 hraw
  have hdelta : rawDelta r s ≠ 0 :=
    rawDelta_ne_zero hs hr1 hraw
  let x : ℚ := rawToOptX r s
  let y : ℚ := rawToOptY r s
  have hx : x ≠ 0 := by
    dsimp [x]
    exact rawToOptX_ne_zero hs1 hxFactor hdelta
  have hopt : optF19 x y = 0 := by
    dsimp [x, y]
    rw [raw_to_opt_residual_identity hrs hdelta, hraw]
    ring
  let u : ℚ := diamondU x y
  let v : ℚ := diamondV x y
  have hdiamond : diamondResidual u v = 0 := by
    dsimp [u, v]
    rw [diamond_residual_identity hx, hopt]
    ring
  have hu : u = 0 := hclass u v hdiamond
  have hxneg : x = -1 := by
    apply x_eq_neg_one_of_diamondU_eq_zero hx hopt
    exact hu
  have hxnot : rawToOptX r s ≠ -1 :=
    rawToOptX_ne_neg_one hs hr1 hraw hdelta
  exact hxnot (by simpa [x] using hxneg)

end

end MazurProof.TateOrder19Quotient

end


open scoped WeierstrassCurve.Affine in
theorem solution (b c : ℚ) (hb : b ≠ 0)
    [({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).IsElliptic]
    (h : ({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).toAffine.Nonsingular 0 0) :
    addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) ≠ 19 := by
  intro hord
  have : (Scratch.TateZ2xZ10Reduction.tateNormalFormCurve b c).IsElliptic := ‹_›
  have hF := MazurProof.TateOrder19.F19_eq_zero_of_tateOrigin_order_nineteen b c hb hord
  refine MazurProof.TateOrder19Quotient.no_F19_rational_solution_of_diamond_x_eq_zero ?_ b c hb hF
  intro u v huv
  apply MazurHuang.diamond_quotient_x_eq_zero u v
  unfold MazurProof.N19SutherlandModels.diamondResidual at huv
  linear_combination huv
