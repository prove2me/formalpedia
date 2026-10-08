-- Prove2me | solution 1 for MazurHuang.tate_origin_addOrderOf_ne_seventeen
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-07T17:26:23.93003+00:00
-- url     : https://prove2.me/submissions/b93fe94a-0539-4a5d-a034-21951fcfa02c

import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_MazurHuang_x0_seventeen_two_isogeny_model_points

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









/-- `ψ₁₇(0,0) / b⁹⁶`.  53 monomials, total degree 12–19. -/
def F17 (b c : K) : K :=
    b ^ 12
      - 10 * b ^ 11 * c
      + 10 * b ^ 10 * c ^ 3
      + 45 * b ^ 10 * c ^ 2
      - 39 * b ^ 9 * c ^ 5
      - 75 * b ^ 9 * c ^ 4
      - 120 * b ^ 9 * c ^ 3
      + 50 * b ^ 8 * c ^ 7
      + 249 * b ^ 8 * c ^ 6
      + 246 * b ^ 8 * c ^ 5
      + 210 * b ^ 8 * c ^ 4
      - 31 * b ^ 7 * c ^ 9
      - 246 * b ^ 7 * c ^ 8
      - 681 * b ^ 7 * c ^ 7
      - 461 * b ^ 7 * c ^ 6
      - 252 * b ^ 7 * c ^ 5
      + 9 * b ^ 6 * c ^ 11
      + 105 * b ^ 6 * c ^ 10
      + 485 * b ^ 6 * c ^ 9
      + 1035 * b ^ 6 * c ^ 8
      + 540 * b ^ 6 * c ^ 7
      + 210 * b ^ 6 * c ^ 6
      - b ^ 5 * c ^ 13
      - 15 * b ^ 5 * c ^ 12
      - 120 * b ^ 5 * c ^ 11
      - 469 * b ^ 5 * c ^ 10
      - 945 * b ^ 5 * c ^ 9
      - 405 * b ^ 5 * c ^ 8
      - 120 * b ^ 5 * c ^ 7
      + 30 * b ^ 4 * c ^ 12
      + 195 * b ^ 4 * c ^ 11
      + 519 * b ^ 4 * c ^ 10
      + 190 * b ^ 4 * c ^ 9
      + 45 * b ^ 4 * c ^ 8
      + 15 * b ^ 3 * c ^ 14
      + 45 * b ^ 3 * c ^ 13
      + 20 * b ^ 3 * c ^ 12
      - 159 * b ^ 3 * c ^ 11
      - 51 * b ^ 3 * c ^ 10
      - 10 * b ^ 3 * c ^ 9
      - 2 * b ^ 2 * c ^ 16
      - 15 * b ^ 2 * c ^ 15
      - 39 * b ^ 2 * c ^ 14
      - 49 * b ^ 2 * c ^ 13
      + 21 * b ^ 2 * c ^ 12
      + 6 * b ^ 2 * c ^ 11
      + b ^ 2 * c ^ 10
      + b * c ^ 18
      + 3 * b * c ^ 17
      + 6 * b * c ^ 16
      + 10 * b * c ^ 15
      + 15 * b * c ^ 14
      - c ^ 15


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

open Polynomial WeierstrassCurve.Affine

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

-- ===== FLT.Assumptions.MazurProof.TateOrder17 =====
section
/-!
# The concrete order-17 Tate-normal-form condition

Parallels `TateOrder13`: connects the Tate-normal-form bridge, the
division-polynomial recurrence, and the explicit identity
`ψ₁₇(0,0) = b⁹⁶ F₁₇(b,c)`.

A rational point of exact order 17 yields concrete Tate parameters
with `b ≠ 0` and `F17 b c = 0`.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOrder17

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

/-! ## Division polynomial recurrence evaluated at X=0 -/

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

private lemma eval_prePsi_seventeen (b c : ℚ) :
    ((W b c).preΨ' 17).eval 0 =
      ((W b c).preΨ' 10).eval 0 * (((W b c).preΨ' 8).eval 0) ^ 3 *
        ((W b c).Ψ₂Sq.eval 0) ^ 2 -
      ((W b c).preΨ' 7).eval 0 * (((W b c).preΨ' 9).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 6)
  simpa [show Even (6 : ℕ) by decide] using h

set_option maxHeartbeats 0 in
theorem prePsi_seventeen_eval_tate_origin (b c : ℚ) :
    ((W b c).preΨ' 17).eval 0 =
      b ^ 96 * TateNFDivision.F17 b c := by
  rw [eval_prePsi_seventeen, eval_prePsi_ten, eval_prePsi_nine,
    eval_prePsi_eight, eval_prePsi_seven,
    eval_prePsi_six, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, TateNFDivision.F17]
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


theorem F17_eq_zero_of_tateOrigin_order_seventeen
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    (hb : b ≠ 0) (hord : addOrderOf (tateOrigin b c) = 17) :
    TateNFDivision.F17 b c = 0 := by
  have h17 : (17 : ℕ) • tateOrigin b c = 0 := by
    simpa [hord] using addOrderOf_nsmul_eq_zero (tateOrigin b c)
  have hPsiSq : ((W b c).ΨSq (17 : ℤ)).eval 0 = 0 :=
    (nsmul_eq_zero_iff_PsiSq_eval (W b c)
      (tate_origin_nonsingular b c)).mp h17
  have hpre : ((W b c).preΨ' 17).eval 0 = 0 := by
    change ((W b c).ΨSq (17 : ℕ)).eval 0 = 0 at hPsiSq
    rw [(W b c).ΨSq_ofNat 17] at hPsiSq
    simpa [show ¬ Even (17 : ℕ) by decide] using hPsiSq
  rw [prePsi_seventeen_eval_tate_origin] at hpre
  exact (mul_eq_zero.mp hpre).resolve_left (pow_ne_zero 96 hb)




end

end MazurProof.TateOrder17

end

-- ===== FLT.Assumptions.MazurProof.VeluTwoIsogeny =====
section
/-!
# Vélu 2-isogeny construction

Explicit Vélu formulas for degree-2 isogenies of elliptic curves over ℚ,
replacing `exists_rational_two_isogeny_quotient`.

## Strategy

Work in short Weierstrass form y² = x³ + Ax + B with 2-torsion Q = (r, 0).
Vélu formulas:
- E' : y² = x³ + A'x + B', A' = A - 5t, B' = B - 7rt, t = 3r² + A
- φ(x,y) = (x + t/(x-r), y·((x-r)²-t)/(x-r)²)
- η = (-2r, 0) ∈ E'[2]

For general Weierstrass, reduce to short form via `VariableChangePointAddEquiv`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.VeluTwoIsogeny

noncomputable section

open WeierstrassCurve.Affine (Equation Nonsingular Point equation_iff_nonsingular
  equation_iff negY slope addX addY)

/-! ## Short Weierstrass definitions -/

@[reducible] def shortWS (A B : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0; a₂ := 0; a₃ := 0; a₄ := A; a₆ := B

def veluT (A r : ℚ) : ℚ := 3 * r ^ 2 + A


/-! ## Equation lemmas -/



/-! ## Well-definedness -/


/-! ## IsElliptic instances -/





/-! ## The Vélu point map -/



/-! ## Kernel -/






/-! ## Homomorphism via the standard two-isogeny

Translate the rational 2-torsion point to `(0, 0)`.  The Vélu map then becomes
the standard degree-two map on `y² = x(x² + ax + b)`.  Its additivity is proved
from the dual-composition doubling identity and the description of its fibres as
cosets of the kernel; the final bridge is an additive change of variables.
-/


namespace StandardTwoIsogeny

open WeierstrassCurve.Affine

/-! ### The standard model and its two maps -/

@[reducible] def curve (a b : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := a
  a₃ := 0
  a₄ := b
  a₆ := 0

lemma curve_equation {a b x y : ℚ} :
    Equation (curve a b) x y ↔ y ^ 2 = x * (x ^ 2 + a * x + b) := by
  rw [equation_iff]
  simp only [curve]
  constructor <;> intro h <;> nlinarith















@[simp] lemma curve_negY (a b x y : ℚ) :
    negY (curve a b) x y = -y := by
  simp [negY, curve]







/-! ### Dual composition and doubling -/




/-! ### Kernel translations and fibres -/

def kernelPoint (a b : ℚ) [hE : (curve a b).IsElliptic] :
    Point (curve a b) :=
  .some 0 0 (equation_iff_nonsingular.mp (curve_equation.mpr (by ring)))
















/-! ### The generic secant calculation

The two `secant_*_identity` lemmas package the only coordinate calculation.
They are low-degree consequences of the two curve equations and the equation of
the secant line; all exceptional configurations have already been classified as
kernel cosets.
-/




/-! ### Additivity on the standard model -/













/-! ### Conjugating the Vélu formula to the standard model -/



def sourceChange (r : ℚ) : WeierstrassCurve.VariableChange ℚ where
  u := 1
  r := r
  s := 0
  t := 0


lemma sourceChange_eq {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    sourceChange r • shortWS A B = curve (3 * r) (veluT A r) := by
  rw [WeierstrassCurve.variableChange_def]
  ext <;> simp [sourceChange, shortWS, curve, veluT] <;> nlinarith





















end StandardTwoIsogeny



/-! ## η = (-2r, 0) on E' -/







/-! ## Dual isogeny helpers -/













/-! ## Dual isogeny

The dual φ̂ : E' → E is the Vélu map from E' with kernel ⟨η⟩ = ⟨(-2r,0)⟩,
composed with the scaling isomorphism shortWS(16A,64B) ≃ shortWS(A,B). -/


/-! ## Properties -/







/-! ## General Weierstrass → Short WS reduction -/

section GeneralToShort

variable (E : WeierstrassCurve ℚ)



end GeneralToShort

/-! ## Bridge theorem helpers -/




/-! ## Main theorem -/


end
end MazurProof.VeluTwoIsogeny

end

-- ===== FLT.Assumptions.MazurProof.X017Model =====
section
/-!
# The explicit genus-one model used for X₀(17)

This file verifies concrete Weierstrass-curve algebra for the integral
genus-one equation

`y² + xy + y = x³ - x² - x - 14`.

It constructs an additive equivalence with the standard rational
two-isogeny model `Y² = X(X² + 30X + 289)` and proves that the visible point
`(17,136)` on the standard model has exact order four.  No modular
interpretation of the displayed curve is asserted here.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017Model


open WeierstrassCurve.Affine
open MazurProof.VeluTwoIsogeny


noncomputable section

/-- The integral genus-one equation used as the concrete `X₀(17)` model. -/
@[reducible] def X017 : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := -1
  a₃ := 1
  a₄ := -1
  a₆ := -14

/-- The affine equation of the integral model in ordinary coordinates. -/
@[simp] theorem X017_equation_iff (x y : ℚ) :
    Equation X017 x y ↔
      y ^ 2 + x * y + y = x ^ 3 - x ^ 2 - x - 14 := by
  rw [equation_iff]
  norm_num [X017]
  constructor <;> intro h <;> nlinarith

/-- The integral model has discriminant `-17^4`. -/
theorem X017_delta : X017.Δ = -(17 : ℚ) ^ 4 := by
  norm_num [X017, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

/-- The nonzero discriminant makes the integral model elliptic over `ℚ`. -/
instance X017_isElliptic : X017.IsElliptic := by
  constructor
  rw [X017_delta]
  norm_num

/-- Rational variable change whose affine coordinates are
`U = 4x - 1` and `V = 8y + 4x + 4`. -/
def toShortChange : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 (1 / 2 : ℚ) (by norm_num)
  r := 1 / 4
  s := -1 / 2
  t := -5 / 8



/-- The short Weierstrass model `V² = U³ - 11U - 890`. -/
@[reducible] def short : WeierstrassCurve ℚ :=
  shortWS (-11) (-890)

/-- The displayed variable change carries the integral model to `short`. -/
theorem toShortChange_curve :
    toShortChange • X017 = short := by
  rw [WeierstrassCurve.variableChange_def]
  ext <;> norm_num [toShortChange, X017, short, shortWS]

/-- The short model is elliptic because it is variable-change equivalent to
the nonsingular integral model. -/
instance short_isElliptic : short.IsElliptic := by
  rw [← toShortChange_curve]
  infer_instance

/-- The rational two-torsion root `U=10` on the short model. -/
theorem ten_is_root :
    (10 : ℚ) ^ 3 + (-11) * 10 + (-890) = 0 := by
  norm_num



/-- The linear coefficient `30` in the translated two-isogeny model. -/
abbrev a17 : ℚ :=
  3 * 10

/-- The constant coefficient `289` in the translated two-isogeny model. -/
abbrev b17 : ℚ :=
  veluT (-11) 10

/-- Translating the source two-torsion point to zero gives
`Y² = X(X² + 30X + 289)`.

The coefficients retain the expressions produced by the general Vélu API so
that its source equivalence is definitionally applicable. -/
@[reducible] def standard : WeierstrassCurve ℚ :=
  StandardTwoIsogeny.curve a17 b17


/-- The standard source change identifies `short` with `standard`. -/
theorem sourceChange_curve :
    StandardTwoIsogeny.sourceChange 10 • short = standard := by
  simpa only [short, standard, a17, b17] using
    StandardTwoIsogeny.sourceChange_eq ten_is_root


/-- The standard source model is elliptic. -/
instance standard_isElliptic : standard.IsElliptic := by
  rw [← sourceChange_curve]
  infer_instance





/-- The coordinates `(17,136)` satisfy the standard source equation and are
nonsingular. -/
private theorem T_nonsingular :
    Nonsingular standard 17 136 := by
  apply equation_iff_nonsingular.mp
  rw [StandardTwoIsogeny.curve_equation]
  norm_num [a17, b17, veluT]

/-- The visible standard-model point corresponding to `(7,13)` on the
integral equation. -/
noncomputable def T : Point standard :=
  Point.some 17 136 T_nonsingular

/-- The visible rational two-torsion point `(0,0)` on the standard source. -/
noncomputable def K : Point standard :=
  StandardTwoIsogeny.kernelPoint a17 b17









end

end MazurProof.X017Model

end

-- ===== shim: rational points of the standard X₀(17) model from the platform node =====
section
open WeierstrassCurve.Affine in
theorem MazurProof.X017RationalPoints.eq_zero_or_K_or_T_or_neg_T
    (P : WeierstrassCurve.Affine.Point MazurProof.X017Model.standard) :
    P = 0 ∨ P = MazurProof.X017Model.K ∨ P = MazurProof.X017Model.T ∨
      P = -MazurProof.X017Model.T := by
  rcases P with _ | ⟨X, Y, hns⟩
  · left; rfl
  right
  have heq : Y ^ 2 = X ^ 3 + 30 * X ^ 2 + 289 * X := by
    have h := hns.1
    rw [WeierstrassCurve.Affine.equation_iff] at h
    simp only [MazurProof.X017Model.standard, MazurProof.X017Model.a17,
      MazurProof.X017Model.b17, MazurProof.VeluTwoIsogeny.veluT] at h
    linear_combination h
  rcases MazurHuang.x0_seventeen_two_isogeny_model_points X Y heq with hX | hX
  · left
    subst hX
    have hY : Y = 0 := by
      have : Y ^ 2 = 0 := by linear_combination heq
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    subst hY
    rfl
  · right
    subst hX
    have hY : (Y - 136) * (Y + 136) = 0 := by linear_combination heq
    rcases mul_eq_zero.mp hY with hY | hY
    · left
      have : Y = 136 := by linarith
      subst this; rfl
    · right
      have : Y = -136 := by linarith
      subst this
      simp only [MazurProof.X017Model.T, WeierstrassCurve.Affine.Point.neg_some]
      simp [WeierstrassCurve.Affine.negY, MazurProof.X017Model.standard]
      all_goals norm_num
end

-- ===== FLT.Assumptions.MazurProof.TateOrder17Quotient =====
section
/-!
# An explicit map from the order-seventeen equation

This file gives the algebraic map from the Tate order-seventeen equation to
the integral model

`y² + xy + y = x³ - x² - x - 14`

used for `X₀(17)`.  The map factors through the elliptic curves

`E₇₂ : y² + xy + y = x³ - x² - x`

and

`E₃₆ : y² + xy + y = x³ - x² - 6x - 4`.

The three displayed maps are checked by polynomial identities.  The rational
point classification on the final curve leaves two possible affine fibres.
Their rational points are excluded by a quartic modulo three and by the
irrationality of `√17`.

Only this algebraic implication is used below.  No modular interpretation of
the displayed maps is needed or asserted.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOrder17Quotient


open WeierstrassCurve.Affine
open MazurProof.VeluTwoIsogeny
open MazurProof.X017Model

noncomputable section

/-! ## Normalized Tate coordinates -/

/-- After writing `b = c(d+1)`, the equation `F₁₇(b,c)=0` is
`c¹² H₁₇(d,c)=0`. -/
def H17 (d c : ℚ) : ℚ :=
    c ^ 7 * d + c ^ 7
      - c ^ 6 * d ^ 5 - 5 * c ^ 6 * d ^ 4
      - 10 * c ^ 6 * d ^ 3 - 12 * c ^ 6 * d ^ 2
      - 6 * c ^ 6 * d
      + 9 * c ^ 5 * d ^ 6 + 39 * c ^ 5 * d ^ 5
      + 60 * c ^ 5 * d ^ 4 + 45 * c ^ 5 * d ^ 3
      + 15 * c ^ 5 * d ^ 2
      - 31 * c ^ 4 * d ^ 7 - 112 * c ^ 4 * d ^ 6
      - 141 * c ^ 4 * d ^ 5 - 80 * c ^ 4 * d ^ 4
      - 20 * c ^ 4 * d ^ 3
      + 50 * c ^ 3 * d ^ 8 + 154 * c ^ 3 * d ^ 7
      + 163 * c ^ 3 * d ^ 6 + 75 * c ^ 3 * d ^ 5
      + 15 * c ^ 3 * d ^ 4
      - 39 * c ^ 2 * d ^ 9 - 102 * c ^ 2 * d ^ 8
      - 93 * c ^ 2 * d ^ 7 - 36 * c ^ 2 * d ^ 6
      - 6 * c ^ 2 * d ^ 5
      + 10 * c * d ^ 10 + 25 * c * d ^ 9
      + 21 * c * d ^ 8 + 7 * c * d ^ 7 + c * d ^ 6
      + d ^ 12 + 2 * d ^ 11 + d ^ 10

set_option maxHeartbeats 0 in
/-- The exact normalization identity for the Tate division factor. -/
theorem F17_normalized (d c : ℚ) :
    TateNFDivision.F17 (c * (d + 1)) c = c ^ 12 * H17 d c := by
  simp only [TateNFDivision.F17, H17]
  ring

/-- The normalized order-six factor: `F₆(c(d+1),c) = -c·r₆(d,c)`. -/
def r6 (d c : ℚ) : ℚ := c - d

/-- The normalized order-seven factor: `F₇(c(d+1),c) = c²·r₇(d,c)`. -/
def r7 (d c : ℚ) : ℚ := c - d ^ 2 - d

/-- The normalized order-eight factor: `F₈(c(d+1),c) = -c²·r₈(d,c)`. -/
def r8 (d c : ℚ) : ℚ := c * d + c - 2 * d ^ 2 - d

/-- The normalized order-nine factor satisfies
`F₉(c(d+1),c) = -c³·q(d,c)` and is the numerator of the horizontal
coordinate on `E₇₂`. -/
def q (d c : ℚ) : ℚ := c ^ 2 - c * d - d ^ 3

/-- Polynomial quotient in the division of `H₁₇` by `q`. -/
def quotientS (d c : ℚ) : ℚ :=
    c ^ 5 * (d + 1)
      + c ^ 4 * (-d ^ 5 - 5 * d ^ 4 - 10 * d ^ 3 - 11 * d ^ 2 - 5 * d)
      + c ^ 3 * (8 * d ^ 6 + 34 * d ^ 5 + 51 * d ^ 4 + 35 * d ^ 3
        + 10 * d ^ 2)
      + c ^ 2 * (-d ^ 8 - 28 * d ^ 7 - 88 * d ^ 6 - 101 * d ^ 5
        - 50 * d ^ 4 - 10 * d ^ 3)
      + c * (7 * d ^ 9 + 56 * d ^ 8 + 117 * d ^ 7 + 97 * d ^ 6
        + 35 * d ^ 5 + 5 * d ^ 4)
      - d ^ 11 - 21 * d ^ 10 - 71 * d ^ 9 - 86 * d ^ 8
      - 46 * d ^ 7 - 11 * d ^ 6 - d ^ 5

/-- The linear remainder after division of `H₁₇` by `q`. -/
def remainderL (d c : ℚ) : ℚ :=
    6 * c * d ^ 5 + 35 * c * d ^ 4 + 56 * c * d ^ 3
      + 36 * c * d ^ 2 + 10 * c * d + c
      - d ^ 7 - 21 * d ^ 6 - 70 * d ^ 5 - 84 * d ^ 4
      - 45 * d ^ 3 - 11 * d ^ 2 - d

/-- The normalized division identity used to exclude the cusp fibre. -/
theorem H17_division_identity (d c : ℚ) :
    H17 d c = q d c * quotientS d c + d ^ 7 * remainderL d c := by
  simp only [H17, q, quotientS, remainderL]
  ring

/-- First coefficient in the Bézout certificate for `q` and its remainder. -/
def bezoutA (d : ℚ) : ℚ :=
  (d + 1) ^ 2 * (2 * d + 1) ^ 2 * (3 * d + 1) ^ 2 *
    (d ^ 2 + 4 * d + 1) ^ 2

/-- Second coefficient in the Bézout certificate for `q` and its remainder. -/
def bezoutB (d c : ℚ) : ℚ :=
    -6 * c * d ^ 5 - 35 * c * d ^ 4 - 56 * c * d ^ 3
      - 36 * c * d ^ 2 - 10 * c * d - c
      - d ^ 7 - 15 * d ^ 6 - 35 * d ^ 5 - 28 * d ^ 4
      - 9 * d ^ 3 - d ^ 2

/-- A compact Bézout identity proving that `q=0` and the remainder cannot
occur when `d ≠ 0`. -/
theorem q_remainder_bezout (d c : ℚ) :
    bezoutA d * q d c + bezoutB d c * remainderL d c = d ^ 14 := by
  simp only [bezoutA, bezoutB, q, remainderL]
  ring

/-- The specialization `d=0` of the normalized order-seventeen equation. -/
@[simp] theorem H17_zero (c : ℚ) : H17 0 c = c ^ 7 := by
  simp [H17]

/-- The order-six denominator specialization. -/
theorem H17_r6_zero (d : ℚ) : H17 d d = d ^ 12 := by
  simp only [H17]
  ring

/-- The order-seven denominator specialization. -/
theorem H17_r7_zero (d : ℚ) :
    H17 d (d ^ 2 + d) = -d ^ 15 * (d + 1) ^ 2 := by
  simp only [H17]
  ring

/-- The order-eight denominator specialization. -/
theorem H17_r8_zero (d : ℚ) (hd1 : d + 1 ≠ 0) :
    H17 d (d * (2 * d + 1) / (d + 1)) =
      d ^ 18 / (d + 1) ^ 6 := by
  simp only [H17]
  field_simp [hd1]
  ring

/-- The normalized order-seventeen equation excludes the order-six
denominator. -/
theorem r6_ne_zero {d c : ℚ} (hd : d ≠ 0) (hH : H17 d c = 0) :
    r6 d c ≠ 0 := by
  intro hr6
  have hc : c = d := by
    simpa [r6] using sub_eq_zero.mp hr6
  rw [hc, H17_r6_zero] at hH
  exact hd (eq_zero_of_pow_eq_zero hH)

/-- The normalized order-seventeen equation excludes the order-seven
denominator. -/
theorem r7_ne_zero {d c : ℚ} (hd : d ≠ 0) (hd1 : d + 1 ≠ 0)
    (hH : H17 d c = 0) : r7 d c ≠ 0 := by
  intro hr7
  have hc : c = d ^ 2 + d := by
    simp only [r7] at hr7
    linarith
  rw [hc, H17_r7_zero] at hH
  exact (mul_ne_zero
    (neg_ne_zero.mpr (pow_ne_zero 15 hd))
    (pow_ne_zero 2 hd1)) hH

/-- The normalized order-seventeen equation excludes the order-eight
denominator. -/
theorem r8_ne_zero {d c : ℚ} (hd : d ≠ 0) (hd1 : d + 1 ≠ 0)
    (hH : H17 d c = 0) : r8 d c ≠ 0 := by
  intro hr8
  have hc : c = d * (2 * d + 1) / (d + 1) := by
    apply (eq_div_iff hd1).2
    simp only [r8] at hr8
    linarith
  rw [hc, H17_r8_zero d hd1] at hH
  have hd18 : d ^ 18 = 0 := by
    simpa [pow_ne_zero 6 hd1] using hH
  exact hd (eq_zero_of_pow_eq_zero hd18)

/-- The numerator `q` does not vanish on the normalized
order-seventeen locus. -/
theorem q_ne_zero {d c : ℚ} (hd : d ≠ 0) (hH : H17 d c = 0) :
    q d c ≠ 0 := by
  intro hq
  have hdL : d ^ 7 * remainderL d c = 0 := by
    calc
      d ^ 7 * remainderL d c =
          H17 d c - q d c * quotientS d c := by
            rw [H17_division_identity]
            ring
      _ = 0 := by rw [hH, hq]; ring
  have hL : remainderL d c = 0 :=
    (mul_eq_zero.mp hdL).resolve_left (pow_ne_zero 7 hd)
  have hd14 : d ^ 14 = 0 := by
    calc
      d ^ 14 = bezoutA d * q d c + bezoutB d c * remainderL d c :=
        (q_remainder_bezout d c).symm
      _ = 0 := by rw [hq, hL]; ring
  exact hd (eq_zero_of_pow_eq_zero hd14)

/-! ## The quotient through `E₇₂` and `E₃₆` -/

/-- Numerator of the vertical coordinate on `E₇₂`. -/
def e72YNumerator (d c : ℚ) : ℚ :=
    c ^ 4 * d + 2 * c ^ 4
      - 5 * c ^ 3 * d ^ 2 - 7 * c ^ 3 * d - c ^ 3
      + 9 * c ^ 2 * d ^ 3 + 13 * c ^ 2 * d ^ 2 + 3 * c ^ 2 * d
      - c * d ^ 5 - 12 * c * d ^ 4 - 13 * c * d ^ 3 - 3 * c * d ^ 2
      + 3 * d ^ 6 + 7 * d ^ 5 + 5 * d ^ 4 + d ^ 3

/-- Horizontal coordinate of the normalized point on `E₇₂`. -/
def e72X (d c : ℚ) : ℚ := q d c / (d * r8 d c)

/-- Vertical coordinate of the normalized point on `E₇₂`. -/
def e72Y (d c : ℚ) : ℚ :=
  e72YNumerator d c / (r7 d c * r8 d c ^ 2)

/-- Residual of the affine equation of `E₇₂`. -/
def E72Residual (x y : ℚ) : ℚ :=
  y ^ 2 + x * y + y - x ^ 3 + x ^ 2 + x

set_option maxHeartbeats 0 in
/-- The explicit quotient coordinates satisfy `E₇₂` when `H₁₇=0`. -/
theorem e72_residual_identity {d c : ℚ}
    (hd : d ≠ 0) (hr7 : r7 d c ≠ 0) (hr8 : r8 d c ≠ 0) :
    E72Residual (e72X d c) (e72Y d c) =
      -(q d c) * H17 d c /
        (d ^ 3 * r7 d c ^ 2 * r8 d c ^ 4) := by
  simp only [E72Residual, e72X, e72Y]
  field_simp [hd, hr7, hr8]
  simp only [e72YNumerator, H17, q, r7, r8]
  ring

/-- The first degree-two quotient horizontal coordinate. -/
def e36X (x : ℚ) : ℚ :=
  (x ^ 3 - 2 * x ^ 2 + 2 * x - 1) / (x - 1) ^ 2

/-- The first degree-two quotient vertical coordinate. -/
def e36Y (x y : ℚ) : ℚ :=
  (y * x ^ 3 + (-3 * y - 1) * x ^ 2 + (2 * y + 1) * x) /
    (x - 1) ^ 3

/-- Residual of the affine equation of `E₃₆`. -/
def E36Residual (x y : ℚ) : ℚ :=
  y ^ 2 + x * y + y - x ^ 3 + x ^ 2 + 6 * x + 4

/-- The first degree-two map preserves the Weierstrass equations. -/
theorem e36_residual_identity {x y : ℚ} (hx : x ≠ 1) :
    E36Residual (e36X x) (e36Y x y) =
      x ^ 2 * (x - 2) ^ 2 / (x - 1) ^ 4 * E72Residual x y := by
  have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  simp only [E36Residual, E72Residual, e36X, e36Y]
  field_simp [hx']
  ring

/-- The second degree-two quotient horizontal coordinate. -/
def x017X (x : ℚ) : ℚ :=
  (x ^ 3 + 2 * x ^ 2 - 1) / (x + 1) ^ 2

/-- The second degree-two quotient vertical coordinate. -/
def x017Y (x y : ℚ) : ℚ :=
  (y * x ^ 3 + (3 * y + 1) * x ^ 2 + (4 * y + 2) * x +
      (2 * y + 1)) / (x + 1) ^ 3

/-- Residual of the integral `X₀(17)` equation. -/
def X017Residual (x y : ℚ) : ℚ :=
  y ^ 2 + x * y + y - x ^ 3 + x ^ 2 + x + 14

/-- The second degree-two map preserves the Weierstrass equations. -/
theorem x017_residual_identity {x y : ℚ} (hx : x ≠ -1) :
    X017Residual (x017X x) (x017Y x y) =
      (x ^ 2 + 2 * x + 2) ^ 2 / (x + 1) ^ 4 *
        E36Residual x y := by
  have hx' : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  simp only [X017Residual, E36Residual, x017X, x017Y]
  field_simp [hx']
  ring

/-- The first quotient horizontal coordinate satisfies a useful kernel
identity. -/
theorem e36X_add_one {x : ℚ} (hx : x ≠ 1) :
    e36X x + 1 = x ^ 2 / (x - 1) := by
  simp only [e36X]
  field_simp [sub_ne_zero.mpr hx]
  ring

/-- The composite horizontal coordinate, written only in terms of the
`E₇₂` horizontal coordinate. -/
def compositeX (x : ℚ) : ℚ :=
  (x ^ 4 - x ^ 3 + 2 * x - 1) / (x ^ 2 * (x - 1))

/-- The two degree-two maps have the displayed composite horizontal
coordinate. -/
theorem x017X_e36X {x : ℚ} (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    x017X (e36X x) = compositeX x := by
  have hu : e36X x + 1 ≠ 0 := by
    rw [e36X_add_one hx1]
    exact div_ne_zero (pow_ne_zero 2 hx0) (sub_ne_zero.mpr hx1)
  have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  simp only [x017X, compositeX]
  field_simp [hx0, hx', hu]
  simp only [e36X]
  field_simp [hx']
  ring

/-! ## The two remaining affine fibres -/

/-- The polynomial forced by the affine fibre with integral
horizontal coordinate `7`. -/
def sevenFiber : Polynomial ℤ :=
  X ^ 4 - C 8 * X ^ 3 + C 7 * X ^ 2 + C 2 * X - C 1

/-- The fibre polynomial is monic over the integers. -/
theorem sevenFiber_monic : sevenFiber.Monic := by
  unfold sevenFiber
  monicity!

/-- The fibre polynomial has no root modulo three. -/
theorem sevenFiber_no_root_mod3 (z : ZMod 3) :
    aeval z sevenFiber ≠ 0 := by
  have h : aeval z sevenFiber = z ^ 4 - 8 * z ^ 3 + 7 * z ^ 2 + 2 * z - 1 := by
    simp only [sevenFiber, map_sub, map_add, map_mul, map_pow, aeval_X, map_ofNat, map_one,
      eq_intCast, Int.cast_ofNat, Int.cast_one]
  rw [h]
  fin_cases z <;> decide

/-- Hence the fibre polynomial has no rational root. -/
theorem sevenFiber_no_rational_root (x : ℚ) :
    aeval x sevenFiber ≠ 0 := by
  intro hx
  obtain ⟨z, hz, _⟩ :=
    exists_integer_of_is_root_of_monic sevenFiber_monic hx
  have hint : aeval z sevenFiber = 0 := by
    have h : aeval (algebraMap ℤ ℚ z) sevenFiber = 0 := hz ▸ hx
    rw [aeval_algebraMap_apply] at h
    exact (IsFractionRing.injective ℤ ℚ) (h.trans (map_zero _).symm)
  have hmod : aeval (algebraMap ℤ (ZMod 3) z) sevenFiber = 0 := by
    rw [aeval_algebraMap_apply, hint, map_zero]
  exact sevenFiber_no_root_mod3 _ hmod

/-- Seventeen is not a square in the rational numbers. -/
theorem sq_ne_seventeen (x : ℚ) : x ^ 2 ≠ 17 := by
  intro hx
  let p : Polynomial ℤ := X ^ 2 - C 17
  have hp : p.Monic := by
    dsimp [p]
    monicity!
  have hroot : aeval x p = 0 := by
    simp [p, aeval_def]
    linarith
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic hp hroot
  have hzsq : z ^ 2 = (17 : ℤ) := by
    rw [hz] at hx
    apply Int.cast_injective (α := ℚ)
    simpa using hx
  have hzlt : z < 5 := by
    nlinarith [sq_nonneg (z - 5)]
  have hzgt : -5 < z := by
    nlinarith [sq_nonneg (z + 5)]
  interval_cases z <;> norm_num at hzsq

/-- The fibre `x=7` gives the monic quartic `sevenFiber`. -/
theorem compositeX_eq_seven {x : ℚ} (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (h : compositeX x = 7) :
    x ^ 4 - 8 * x ^ 3 + 7 * x ^ 2 + 2 * x - 1 = 0 := by
  simp only [compositeX] at h
  field_simp [hx0, sub_ne_zero.mpr hx1] at h
  linarith

/-- The fibre `x=11/4` splits into a double linear factor and a quadratic
of discriminant seventeen. -/
theorem compositeX_eq_eleven_fourths {x : ℚ}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (h : compositeX x = 11 / 4) :
    (x - 2) ^ 2 * (4 * x ^ 2 + x - 1) = 0 := by
  simp only [compositeX] at h
  field_simp [hx0, sub_ne_zero.mpr hx1] at h
  nlinarith

/-! ## Assembly -/

/-- The integral-to-standard coordinate change carries the integral residual
to sixty-four times itself. -/
theorem standard_residual_identity (x y : ℚ) :
    (8 * y + 4 * x + 4) ^ 2 -
        (4 * x - 11) * ((4 * x - 11) ^ 2 +
          30 * (4 * x - 11) + 289) =
      64 * X017Residual x y := by
  simp only [X017Residual]
  ring

set_option maxHeartbeats 0 in
/-- The explicit quotient of a nondegenerate Tate solution gives an affine
point on the standard `X₀(17)` model whose integral horizontal coordinate is
one of the two possible affine values. -/
theorem quotient_integral_x_eq
    {d c : ℚ} (hd : d ≠ 0) (hd1 : d + 1 ≠ 0)
    (hH : H17 d c = 0) :
    let ex := e72X d c
    let ux := e36X ex
    let vx := x017X ux
    vx = 7 ∨ vx = 11 / 4 := by
  have hr6 := r6_ne_zero hd hH
  have hr7 := r7_ne_zero hd hd1 hH
  have hr8 := r8_ne_zero hd hd1 hH
  have hq := q_ne_zero hd hH
  let ex := e72X d c
  let ey := e72Y d c
  have hex0 : ex ≠ 0 := by
    exact div_ne_zero hq (mul_ne_zero hd hr8)
  have hex1 : ex ≠ 1 := by
    intro hex
    have hnum : q d c = d * r8 d c := by
      dsimp [ex, e72X] at hex
      field_simp [hd, hr8] at hex
      exact hex
    have hprod : r6 d c * r7 d c = 0 := by
      simp only [q, r6, r7, r8] at hnum ⊢
      linear_combination hnum
    exact (mul_ne_zero hr6 hr7) hprod
  have hE72 : E72Residual ex ey = 0 := by
    rw [e72_residual_identity hd hr7 hr8, hH]
    ring
  let ux := e36X ex
  let uy := e36Y ex ey
  have hE36 : E36Residual ux uy = 0 := by
    dsimp [ux, uy]
    rw [e36_residual_identity hex1, hE72]
    ring
  have hux1 : ux ≠ -1 := by
    have hplus : ux + 1 ≠ 0 := by
      dsimp [ux]
      rw [e36X_add_one hex1]
      exact div_ne_zero (pow_ne_zero 2 hex0) (sub_ne_zero.mpr hex1)
    exact fun h => hplus (by rw [h]; norm_num)
  let vx := x017X ux
  let vy := x017Y ux uy
  have hX017 : X017Residual vx vy = 0 := by
    dsimp [vx, vy]
    rw [x017_residual_identity hux1, hE36]
    ring
  let Xs : ℚ := 4 * vx - 11
  let Ys : ℚ := 8 * vy + 4 * vx + 4
  have hstandard : Ys ^ 2 = Xs * (Xs ^ 2 + 30 * Xs + 289) := by
    have h := standard_residual_identity vx vy
    rw [hX017, mul_zero] at h
    dsimp [Xs, Ys]
    linarith
  have hns : Nonsingular standard Xs Ys := by
    apply equation_iff_nonsingular.mp
    rw [StandardTwoIsogeny.curve_equation]
    norm_num [a17, b17, veluT]
    exact hstandard
  let P : Point standard := Point.some Xs Ys hns
  rcases X017RationalPoints.eq_zero_or_K_or_T_or_neg_T P with
      hP | hP | hP | hP
  · exact False.elim ((Point.some_ne_zero hns) hP)
  · right
    dsimp [P] at hP
    unfold K StandardTwoIsogeny.kernelPoint at hP
    rw [Point.some.injEq] at hP
    dsimp [Xs] at hP
    linarith [hP.1]
  · left
    dsimp [P] at hP
    unfold T at hP
    rw [Point.some.injEq] at hP
    dsimp [Xs] at hP
    linarith [hP.1]
  · left
    dsimp [P] at hP
    unfold T at hP
    rw [Point.neg_some, Point.some.injEq] at hP
    dsimp [Xs] at hP
    linarith [hP.1]

set_option maxHeartbeats 0 in
/-- The Tate residual `F₁₇` has no rational solution with `b ≠ 0`. -/
theorem no_F17_rational_solution
    (b c : ℚ) (hb : b ≠ 0) :
    TateNFDivision.F17 b c ≠ 0 := by
  intro hF17
  have hc : c ≠ 0 := by
    intro hc
    subst c
    norm_num [TateNFDivision.F17] at hF17
    exact hb hF17
  let d : ℚ := b / c - 1
  have hbcoord : b = c * (d + 1) := by
    dsimp [d]
    field_simp [hc]
    ring
  have hH : H17 d c = 0 := by
    rw [hbcoord, F17_normalized] at hF17
    exact (mul_eq_zero.mp hF17).resolve_left (pow_ne_zero 12 hc)
  have hd : d ≠ 0 := by
    intro hd
    rw [hd, H17_zero] at hH
    exact hc (eq_zero_of_pow_eq_zero hH)
  have hd1 : d + 1 ≠ 0 := by
    intro hd1
    rw [hd1, mul_zero] at hbcoord
    exact hb hbcoord
  have hxcase := quotient_integral_x_eq hd hd1 hH
  let ex := e72X d c
  let ey := e72Y d c
  let ux := e36X ex
  let uy := e36Y ex ey
  let vx := x017X ux
  have hr6 := r6_ne_zero hd hH
  have hr7 := r7_ne_zero hd hd1 hH
  have hr8 := r8_ne_zero hd hd1 hH
  have hq := q_ne_zero hd hH
  have hex0 : ex ≠ 0 :=
    div_ne_zero hq (mul_ne_zero hd hr8)
  have hex1 : ex ≠ 1 := by
    intro hex
    have hnum : q d c = d * r8 d c := by
      dsimp [ex, e72X] at hex
      field_simp [hd, hr8] at hex
      exact hex
    have hprod : r6 d c * r7 d c = 0 := by
      simp only [q, r6, r7, r8] at hnum ⊢
      linear_combination hnum
    exact (mul_ne_zero hr6 hr7) hprod
  have hcomposite : vx = compositeX ex := by
    dsimp [vx, ux]
    exact x017X_e36X hex0 hex1
  rcases hxcase with hx7 | hx11
  · have hroot :
        ex ^ 4 - 8 * ex ^ 3 + 7 * ex ^ 2 + 2 * ex - 1 = 0 :=
      compositeX_eq_seven hex0 hex1 (by
        rw [← hcomposite]
        simpa only [vx, ux, ex] using hx7)
    apply sevenFiber_no_rational_root ex
    simp [sevenFiber, aeval_def]
    exact hroot
  · have hfactor :
        (ex - 2) ^ 2 * (4 * ex ^ 2 + ex - 1) = 0 :=
      compositeX_eq_eleven_fourths hex0 hex1
        (by
          rw [← hcomposite]
          simpa only [vx, ux, ex] using hx11)
    rcases mul_eq_zero.mp hfactor with hex2 | hquad
    · have hex2' : ex = 2 :=
        sub_eq_zero.mp (eq_zero_of_pow_eq_zero hex2)
      have hE72 : E72Residual ex ey = 0 := by
        rw [e72_residual_identity hd hr7 hr8, hH]
        ring
      have hsquare : (2 * ey + 3) ^ 2 = 17 := by
        rw [hex2'] at hE72
        simp only [E72Residual] at hE72
        nlinarith
      exact sq_ne_seventeen (2 * ey + 3) hsquare
    · have hsquare : (8 * ex + 1) ^ 2 = 17 := by
        nlinarith
      exact sq_ne_seventeen (8 * ex + 1) hsquare

end

end MazurProof.TateOrder17Quotient

end


open scoped WeierstrassCurve.Affine in
theorem solution (b c : ℚ) (hb : b ≠ 0)
    [({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).IsElliptic]
    (h : ({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).toAffine.Nonsingular 0 0) :
    addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) ≠ 17 := by
  intro hord
  have : (Scratch.TateZ2xZ10Reduction.tateNormalFormCurve b c).IsElliptic := ‹_›
  have hF := MazurProof.TateOrder17.F17_eq_zero_of_tateOrigin_order_seventeen b c hb hord
  exact MazurProof.TateOrder17Quotient.no_F17_rational_solution b c hb hF
