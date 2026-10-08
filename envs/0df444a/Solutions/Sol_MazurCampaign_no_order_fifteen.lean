-- Prove2me | solution 1 for MazurCampaign.no_order_fifteen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T09:40:36.986024+00:00
-- url     : https://prove2.me/submissions/b7fa8f05-9ffc-4708-9141-ee2856966732

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurCampaign_good_reduction_card_bound


/- Source module: MazurTorsion.Foundations.ThreeTorsion. Original headers retained. -/
section
/-
Copyright (c) 2026 Victor Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Aguiar
-/



/-!
# The full rational three-torsion obstruction

This file proves that the rational points of a Weierstrass curve over `ℚ`
cannot contain a subgroup isomorphic to `ZMod 3 × ZMod 3`. The proof derives
the three-division polynomial from the tangent formulas and uses its four
hypothetical rational roots to contradict the Weierstrass coefficient
relation.
-/

namespace MazurTorsion.ThreeTorsion

open WeierstrassCurve

lemma tangent_forces_three_division
    {a₁ a₂ a₃ a₄ a₆ x y slope : ℚ}
    (hcurve :
      y ^ 2 + a₁ * x * y + a₃ * y =
        x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hslope :
      slope * (2 * y + a₁ * x + a₃) =
        3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)
    (hx : slope ^ 2 + a₁ * slope - a₂ - 3 * x = 0) :
    3 * x ^ 4 + (a₁ ^ 2 + 4 * a₂) * x ^ 3 +
      3 * (a₁ * a₃ + 2 * a₄) * x ^ 2 +
      3 * (a₃ ^ 2 + 4 * a₆) * x +
      (a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ +
        a₂ * a₃ ^ 2 - a₄ ^ 2) = 0 := by
  linear_combination
    -(2 * y + a₁ * x + a₃) ^ 2 * hx +
    ((3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) +
      slope * (2 * y + a₁ * x + a₃) +
      a₁ * (2 * y + a₁ * x + a₃)) * hslope -
    (a₁ ^ 2 + 4 * a₂ + 12 * x) * hcurve

/-- The exact algebraic identity behind the three-division polynomial:
on the curve, the value of `Ψ₃` is the negative square of the tangent
denominator times the difference between the doubled and original
x-coordinates. -/
lemma three_division_tangent_identity
    {a₁ a₂ a₃ a₄ a₆ x y slope : ℚ}
    (hcurve :
      y ^ 2 + a₁ * x * y + a₃ * y =
        x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hslope :
      slope * (2 * y + a₁ * x + a₃) =
        3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) :
    3 * x ^ 4 + (a₁ ^ 2 + 4 * a₂) * x ^ 3 +
        3 * (a₁ * a₃ + 2 * a₄) * x ^ 2 +
        3 * (a₃ ^ 2 + 4 * a₆) * x +
        (a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ +
          a₂ * a₃ ^ 2 - a₄ ^ 2) =
      -(2 * y + a₁ * x + a₃) ^ 2 *
        (slope ^ 2 + a₁ * slope - a₂ - 3 * x) := by
  linear_combination
    ((3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) +
      slope * (2 * y + a₁ * x + a₃) +
      a₁ * (2 * y + a₁ * x + a₃)) * hslope -
    (a₁ ^ 2 + 4 * a₂ + 12 * x) * hcurve

open scoped WeierstrassCurve.Affine

lemma nonzero_three_torsion_abscissa
    (W : WeierstrassCurve.Affine ℚ) (P : W.Point)
    (hthree : (3 : ℕ) • P = 0) (hne : P ≠ 0) :
    ∃ x y, ∃ hP : W.Nonsingular x y,
      P = .some x y hP ∧ Polynomial.eval x W.Ψ₃ = 0 := by
  cases P with
  | zero => exact (hne rfl).elim
  | some x y hP =>
      have hthree' :
          (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP +
            WeierstrassCurve.Affine.Point.some x y hP = 0 := by
        simpa [three_nsmul, two_nsmul, add_assoc] using hthree
      have hdouble :
          (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
            -WeierstrassCurve.Affine.Point.some x y hP := by
        rw [← add_eq_zero_iff_eq_neg]
        exact hthree'
      have hy : y ≠ W.negY x y := by
        intro hy
        have htwo :
            (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 := by
          rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
        have : WeierstrassCurve.Affine.Point.some x y hP = 0 := by
          rw [htwo, zero_add] at hthree'
          exact hthree'
        exact hne this
      let slope := W.slope x x y y
      have hadd :=
        WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hP) hy
      have hxcoord : W.addX x x slope = x := by
        have hsum :
            WeierstrassCurve.Affine.Point.some x y hP +
                WeierstrassCurve.Affine.Point.some x y hP =
              -WeierstrassCurve.Affine.Point.some x y hP := by
          simpa [two_nsmul] using hdouble
        have hsome := hadd.symm.trans hsum
        exact (WeierstrassCurve.Affine.Point.some.inj hsome).1
      have hslope :
          slope * (2 * y + W.a₁ * x + W.a₃) =
            3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
        have hden : y - W.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
          simp only [WeierstrassCurve.Affine.negY]
          ring
        dsimp [slope]
        rw [← hden, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,
          div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
      have hx : slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x = 0 := by
        have := hxcoord
        simp only [WeierstrassCurve.Affine.addX] at this
        linarith
      have hcurve := hP.1
      rw [WeierstrassCurve.Affine.equation_iff] at hcurve
      have hψ := tangent_forces_three_division hcurve hslope hx
      refine ⟨x, y, hP, rfl, ?_⟩
      simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_ofNat, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring_nf at hψ ⊢
      exact hψ

/-- For a nonsingular affine point over `ℚ`, vanishing of the
three-division polynomial is equivalent to the point being killed by `3`. -/
theorem three_nsmul_some_eq_zero_iff
    (W : WeierstrassCurve.Affine ℚ) {x y : ℚ}
    (hP : W.Nonsingular x y) :
    (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 ↔
      Polynomial.eval x W.Ψ₃ = 0 := by
  constructor
  · intro hthree
    obtain ⟨x', y', hP', heq, hψ⟩ :=
      nonzero_three_torsion_abscissa W
        (WeierstrassCurve.Affine.Point.some x y hP) hthree
        (WeierstrassCurve.Affine.Point.some_ne_zero hP)
    have hcoords := WeierstrassCurve.Affine.Point.some.inj heq
    simpa [hcoords.1] using hψ
  · intro hψ
    have hcurve := hP.1
    rw [WeierstrassCurve.Affine.equation_iff] at hcurve
    simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_ofNat, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈] at hψ
    let D := 2 * y + W.a₁ * x + W.a₃
    let N := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
    have hD : D ≠ 0 := by
      intro hD0
      have hN2 : N ^ 2 = 0 := by
        dsimp [D, N] at hD0 ⊢
        linear_combination
          -hψ - (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * hcurve -
          (W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) -
            (W.a₂ + 3 * x) * (2 * y + W.a₁ * x + W.a₃)) * hD0
      have hN : N = 0 := sq_eq_zero_iff.mp hN2
      rw [WeierstrassCurve.Affine.nonsingular_iff'] at hP
      rcases hP.2 with hX | hY
      · apply hX
        dsimp [N] at hN
        linarith
      · exact hY (by simpa [D] using hD0)
    let slope := W.slope x x y y
    have hy : y ≠ W.negY x y := by
      intro hy
      apply hD
      dsimp [D]
      simp only [WeierstrassCurve.Affine.negY] at hy
      linarith
    have hslope :
        slope * D = N := by
      have hden : y - W.negY x y = D := by
        dsimp [D]
        ring
      dsimp [slope]
      rw [← hden, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,
        div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
    have hidentity :=
      three_division_tangent_identity hcurve hslope
    have hx : slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x = 0 := by
      have hmul : D ^ 2 *
          (slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x) = 0 := by
        dsimp [D, N] at hidentity ⊢
        linear_combination hidentity - hψ
      exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 2 hD)
    have hadd :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hP) hy
    have hxcoord : W.addX x x slope = x := by
      simp only [WeierstrassCurve.Affine.addX]
      linarith
    change W.addX x x (W.slope x x y y) = x at hxcoord
    have hxrep :
        ((2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP).xRep =
          (WeierstrassCurve.Affine.Point.some x y hP).xRep := by
      rw [two_nsmul, hadd]
      simp only [WeierstrassCurve.Affine.Point.xRep_some, hxcoord]
    rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxrep
      with hdouble | hdouble
    · have hzero : WeierstrassCurve.Affine.Point.some x y hP = 0 := by
        have hsum :
            WeierstrassCurve.Affine.Point.some x y hP +
                WeierstrassCurve.Affine.Point.some x y hP =
              WeierstrassCurve.Affine.Point.some x y hP + 0 := by
          rw [add_zero]
          rw [two_nsmul] at hdouble
          exact hdouble
        exact add_left_cancel hsum
      exact (WeierstrassCurve.Affine.Point.some_ne_zero hP hzero).elim
    · rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul,
        hdouble, neg_add_cancel]















end MazurTorsion.ThreeTorsion

end


/- Source module: MazurTorsion.EllipticCurve.VariableChange. Original headers retained. -/
section
/-
Copyright (c) 2026 Kevin Buzzard, Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude, Vasily Ilin
-/


/-!
# Isomorphism of point groups induced by a change of variables

This file is ported from Michael Stoll's Apache-2.0 `EllipticCurves` project at commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.

The derivative-transport and singular-cubic nonsingular-locus equivalence are local extensions.
They generalize the ported point equivalence beyond elliptic equations while retaining the
original admissible change-of-variables formulas and attribution.

Mathlib's affine `Point` API provides the group homomorphism induced by a change of the base
field for a fixed Weierstrass curve, but not the isomorphism of Mordell--Weil groups induced by
an admissible change of variables between two different curves. For
`C : WeierstrassCurve.VariableChange F`, the admissible change

`(x, y) ↦ (u²x + r, u³y + u²sx + t)`

gives the group isomorphism
`WeierstrassCurve.Affine.Point.equivVariableChange : (C • W).Point ≃+ W.Point`.
Its inverse is the explicit change of variables `C⁻¹`.
-/

section

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

/-! ### Transformation of the group-law formulae under a change of variables -/

lemma variableChange_negY (x y : F) :
    W.toAffine.negY ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) ^ 3 * (C • W).toAffine.negY x y + (C.u : F) ^ 2 * C.s * x + C.t := by
  simp [negY, variableChange_a₁, variableChange_a₃]
  field

/-- The image of a pair of points under the change of variables satisfies the `y₁ = -y₂`
degeneracy condition only if the original pair does. -/
lemma variableChange_negY_ne {x₁ x₂ y₁ y₂ : F}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    ¬((C.u : F) ^ 2 * x₁ + C.r = (C.u : F) ^ 2 * x₂ + C.r ∧
      (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t = W.toAffine.negY
        ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  intro ⟨hX, hY⟩
  have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
  subst hx
  rw [variableChange_negY] at hY
  exact hxy ⟨rfl, mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY)⟩

lemma variableChange_addX (x₁ x₂ ℓ : F) :
    W.toAffine.addX ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  simp [addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_negAddY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.negAddY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.negAddY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp [negAddY, addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_addY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.addY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [addY, variableChange_negAddY, variableChange_addX, variableChange_negY]

lemma variableChange_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : (C • W).toAffine.Equation x₁ y₁) (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rcases eq_or_ne x₁ x₂ with rfl | hx
  · have hy : y₁ ≠ (C • W).toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    obtain rfl := Y_eq_of_Y_ne h₁ h₂ rfl hy
    have hΦy : (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t
        ≠ W.toAffine.negY ((C.u : F) ^ 2 * x₁ + C.r)
            ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) := by
      rw [variableChange_negY]
      exact fun h ↦ hy (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination h))
    rw [W.toAffine.slope_of_Y_ne rfl hΦy, (C • W).toAffine.slope_of_Y_ne rfl hy,
      ← mul_div_assoc, div_add' _ _ _ (sub_ne_zero.mpr hy),
      div_eq_div_iff (sub_ne_zero.mpr hΦy) (sub_ne_zero.mpr hy)]
    simp [negY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]
    field
  · have hΦx : (C.u : F) ^ 2 * x₁ + C.r ≠ (C.u : F) ^ 2 * x₂ + C.r := by
      simpa [mul_right_inj' (pow_ne_zero 2 hu)] using hx
    rw [W.toAffine.slope_of_X_ne hΦx, (C • W).toAffine.slope_of_X_ne hx]
    have h1 := sub_ne_zero.mpr hΦx
    have h2 := sub_ne_zero.mpr hx
    field

/-- A point `(x, y)` lies on `C • W` if and only if `(u²x + r, u³y + u²sx + t)` lies on `W`. -/
lemma variableChange_equation (x y : F) :
    W.toAffine.Equation ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Equation x y := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [equation_iff', variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val, field]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> linear_combination h

/-- The `Y`-derivative of a Weierstrass equation under an admissible change of variables.
This formula does not require either equation to be elliptic. -/
lemma variableChange_polynomialY (x y : F) :
    W.toAffine.polynomialY.evalEval ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) =
      (C.u : F) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y := by
  simp only [Affine.evalEval_polynomialY, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field

/-- The `X`-derivative of a Weierstrass equation under an admissible change of variables.
The correction term is the chain-rule contribution from the `sx` term in the new `Y` coordinate.
This formula does not require either equation to be elliptic. -/
lemma variableChange_polynomialX (x y : F) :
    W.toAffine.polynomialX.evalEval ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) =
      (C.u : F) ^ 4 * (C • W).toAffine.polynomialX.evalEval x y -
        C.s * ((C.u : F) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y) := by
  simp only [Affine.evalEval_polynomialX, Affine.evalEval_polynomialY, variableChange_a₁,
    variableChange_a₂, variableChange_a₃, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field

/-- An admissible change of variables identifies the nonsingular loci even when the common
Weierstrass cubic is singular. -/
lemma variableChange_nonsingular (x y : F) :
    W.toAffine.Nonsingular ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) ↔
      (C • W).toAffine.Nonsingular x y := by
  rw [Affine.Nonsingular, Affine.Nonsingular, variableChange_equation W C,
    variableChange_polynomialX W C, variableChange_polynomialY W C]
  apply and_congr_right
  intro _
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  constructor
  · rintro (hx | hy)
    · by_cases hY : (C • W).toAffine.polynomialY.evalEval x y = 0
      · left
        intro hX
        apply hx
        rw [hY, mul_zero, mul_zero, sub_zero, hX, mul_zero]
      · exact Or.inr hY
    · exact Or.inr fun hY ↦ hy (mul_eq_zero.mpr <| Or.inr hY)
  · rintro (hx | hy)
    · by_cases hY : (C • W).toAffine.polynomialY.evalEval x y = 0
      · left
        rw [hY, mul_zero, mul_zero, sub_zero]
        exact mul_ne_zero (pow_ne_zero 4 hu) hx
      · exact Or.inr (mul_ne_zero (pow_ne_zero 3 hu) hY)
    · exact Or.inr (mul_ne_zero (pow_ne_zero 3 hu) hy)

/-! ### The induced isomorphism of point groups -/

namespace Point

/-- The underlying point map of the change of variables, sending `0` to `0`. -/
def mapVariableChangeFun : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .some ((C.u : F) ^ 2 * x + C.r)
      ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ((variableChange_nonsingular W C x y).mpr h)

@[simp] lemma mapVariableChangeFun_zero : mapVariableChangeFun W C 0 = 0 := rfl

lemma mapVariableChangeFun_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    mapVariableChangeFun W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) := rfl

lemma some_eq_some (W : WeierstrassCurve F) {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂} :
    (some x₁ y₁ h₁ : W.toAffine.Point) = some x₂ y₂ h₂ := by
  subst hx hy
  rfl

lemma mapVariableChangeFun_injective :
    Function.Injective (mapVariableChangeFun W C) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · simp [mapVariableChangeFun] at h
  · simp [mapVariableChangeFun] at h
  · rw [mapVariableChangeFun_some, mapVariableChangeFun_some] at h
    injection h with hX hY
    have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
    exact some_eq_some (C • W) hx
      (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY - (C.u : F) ^ 2 * C.s * hx))

variable [DecidableEq F]

/-- Transport of the affine point group along an equality of Weierstrass curves. -/
def equivOfEq {V V' : WeierstrassCurve F} (h : V = V') :
    V.toAffine.Point ≃+ V'.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

@[simp] lemma equivOfEq_some {V V' : WeierstrassCurve F} (h : V = V') {x y : F}
    (hns : V.toAffine.Nonsingular x y) :
    equivOfEq h (some x y hns) = some x y (h ▸ hns) := by
  subst h
  rfl

/-- The group homomorphism induced by the admissible change of variables. -/
def mapVariableChange : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := mapVariableChangeFun W C
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    simp only [mapVariableChangeFun_some]
    have e₁ : (C • W).toAffine.Equation x₁ y₁ := h₁.left
    have e₂ : (C • W).toAffine.Equation x₂ y₂ := h₂.left
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2, mapVariableChangeFun_zero]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, mapVariableChangeFun_some, add_some (variableChange_negY_ne W C hxy)]
      simp only [variableChange_slope W C e₁ e₂ hxy, variableChange_addX, variableChange_addY]

/-- The point-group isomorphism induced by the admissible change of variables. -/
def equivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  have hright : ∀ P, mapVariableChangeFun W C
      (mapVariableChangeFun (C • W) C⁻¹ (equivOfEq (inv_smul_smul C W).symm P)) = P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨X, Y, h⟩)
    · simp [← zero_def]
    · rw [equivOfEq_some, mapVariableChangeFun_some, mapVariableChangeFun_some]
      refine some_eq_some W ?_ ?_ <;>
        (simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]; field)
  { toFun := mapVariableChangeFun W C
    invFun := fun P ↦ mapVariableChangeFun (C • W) C⁻¹ (equivOfEq (inv_smul_smul C W).symm P)
    left_inv := Function.RightInverse.leftInverse_of_injective hright
      (mapVariableChangeFun_injective W C)
    right_inv := hright
    map_add' := (mapVariableChange W C).map_add' }

lemma equivVariableChange_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    equivVariableChange W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) := rfl

end Point

end WeierstrassCurve.Affine

end

end


/- Source module: MazurTorsion.Kubert.TateNormalForm. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Tate normal form

Reusable foundations for the Tate normal form

`y² + (1-c)xy - by = x³ - bx²`

with marked point `P = (0,0)`. This file provides the normalization theorem retaining
the discriminant scale and kernel-checked low-multiple coordinate formulas. It does not
state an order classification theorem.
-/
section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- Tate normal form
`y² + (1-c)xy - by = x³ - bx²`, with marked point `(0,0)`. -/
def tateNormalCurve (b c : ℚ) : WeierstrassCurve ℚ :=
  ⟨1 - c, -b, -b, 0, 0⟩

@[simp] lemma tateNormalCurve_a₁ (b c : ℚ) : (tateNormalCurve b c).a₁ = 1 - c := rfl
@[simp] lemma tateNormalCurve_a₂ (b c : ℚ) : (tateNormalCurve b c).a₂ = -b := rfl
@[simp] lemma tateNormalCurve_a₃ (b c : ℚ) : (tateNormalCurve b c).a₃ = -b := rfl
@[simp] lemma tateNormalCurve_a₄ (b c : ℚ) : (tateNormalCurve b c).a₄ = 0 := rfl
@[simp] lemma tateNormalCurve_a₆ (b c : ℚ) : (tateNormalCurve b c).a₆ = 0 := rfl















/-- If the tangent at the origin has triple contact, then the origin is killed by three.
This is the small group-law fact used during Tate normalization. -/
lemma three_nsmul_origin_eq_zero
    (W : WeierstrassCurve ℚ) (ha₂ : W.a₂ = 0) (ha₄ : W.a₄ = 0)
    (ha₃ : W.a₃ ≠ 0) (h00 : W.toAffine.Nonsingular 0 0) :
    WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 = 0 := by
  have hvertical : (0 : ℚ) ≠ W.toAffine.negY 0 0 := by
    simp only [WeierstrassCurve.Affine.negY]
    intro h
    apply ha₃
    linarith
  have hslope : W.toAffine.slope 0 0 0 0 = 0 := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hvertical]
    simp only [WeierstrassCurve.Affine.negY, ha₂, ha₄]
    ring_nf
  have hdouble :
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        -WeierstrassCurve.Affine.Point.some 0 0 h00 := by
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne' hvertical]
    congr 1
    refine WeierstrassCurve.Affine.Point.some_eq_some W ?_ ?_
    · simp only [WeierstrassCurve.Affine.addX, hslope, ha₂]
      ring
    · simp only [WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.addX, hslope, ha₂]
      ring
  rw [hdouble, neg_add_cancel]

/-- Tate normalization retaining the discriminant and `c₄` scaling
parameters. -/
theorem exists_tateNormalCurve_scaled
    (W : WeierstrassCurve ℚ)
    (P : W.toAffine.Point) (hP2 : P + P ≠ 0) (hP3 : P + P + P ≠ 0) :
    ∃ (b c u : ℚ) (_ : u ≠ 0) (_ : b ≠ 0)
      (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
      (e : W.toAffine.Point ≃+ (tateNormalCurve b c).toAffine.Point),
      e P = WeierstrassCurve.Affine.Point.some 0 0 h00 ∧
        u ^ 12 * W.Δ = (tateNormalCurve b c).Δ ∧
        u ^ 4 * W.c₄ = (tateNormalCurve b c).c₄ ∧
        u ^ 6 * W.c₆ = (tateNormalCurve b c).c₆ := by
  obtain ⟨X, Y, hns, hPxy⟩ :
      ∃ (X Y : ℚ) (h : W.toAffine.Nonsingular X Y),
        P = WeierstrassCurve.Affine.Point.some X Y h := by
    rcases hcase : P with _ | ⟨X, Y, h⟩
    · exfalso
      apply hP2
      rw [hcase]
      simp [← WeierstrassCurve.Affine.Point.zero_def]
    · exact ⟨X, Y, h, rfl⟩
  have hnotvertical : Y ≠ W.toAffine.negY X Y := fun h =>
    hP2 (by
      rw [hPxy]
      exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq h)
  have htangentDenom : W.a₃ + X * W.a₁ + 2 * Y ≠ 0 := by
    intro h
    apply hnotvertical
    rw [WeierstrassCurve.Affine.negY]
    linarith
  set s : ℚ :=
    (W.a₄ + 2 * X * W.a₂ - Y * W.a₁ + 3 * X ^ 2) /
      (W.a₃ + X * W.a₁ + 2 * Y) with hs
  set C₁ : WeierstrassCurve.VariableChange ℚ := ⟨1, X, s, Y⟩ with hC₁
  have hC₁a₃ : (C₁ • W).a₃ = W.a₃ + X * W.a₁ + 2 * Y := by
    rw [WeierstrassCurve.variableChange_a₃, hC₁]
    simp
  have hC₁a₄ : (C₁ • W).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    rw [hs]
    field_simp
    ring
  have hC₁a₆ : (C₁ • W).a₆ = 0 := by
    have heq := hns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    rw [WeierstrassCurve.variableChange_a₆, hC₁]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  have h00₁ : (C₁ • W).toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.nonsingular_zero.mpr
      ⟨hC₁a₆, Or.inl (by rw [hC₁a₃]; exact htangentDenom)⟩
  have hmap₁ :
      WeierstrassCurve.Affine.Point.equivVariableChange W C₁
          (WeierstrassCurve.Affine.Point.some 0 0 h00₁) = P := by
    rw [WeierstrassCurve.Affine.Point.equivVariableChange_some, hPxy]
    exact WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp [hC₁]) (by simp [hC₁])
  have hC₁a₂ : (C₁ • W).a₂ ≠ 0 := by
    intro hzero
    apply hP3
    have htriple :
        WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
            WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
            WeierstrassCurve.Affine.Point.some 0 0 h00₁ = 0 :=
      three_nsmul_origin_eq_zero (C₁ • W) hzero hC₁a₄
        (by rw [hC₁a₃]; exact htangentDenom) h00₁
    have himage :=
      congrArg (WeierstrassCurve.Affine.Point.equivVariableChange W C₁) htriple
    rwa [map_add, map_add, map_zero, hmap₁] at himage
  set scale : ℚˣ :=
    Units.mk0 ((C₁ • W).a₃ / (C₁ • W).a₂)
      (div_ne_zero (by rw [hC₁a₃]; exact htangentDenom) hC₁a₂)
  set C₂ : WeierstrassCurve.VariableChange ℚ := ⟨scale, 0, 0, 0⟩ with hC₂
  have hscale : (scale : ℚ) = (C₁ • W).a₃ / (C₁ • W).a₂ := rfl
  have hscale0 : (scale : ℚ) ≠ 0 := scale.ne_zero
  set b : ℚ := -(C₂ • (C₁ • W)).a₂ with hb
  set c : ℚ := 1 - (C₂ • (C₁ • W)).a₁ with hc
  have hC₂a₄ : (C₂ • (C₁ • W)).a₄ = 0 := by
    rw [WeierstrassCurve.variableChange_a₄, hC₂]
    simp [hC₁a₄]
  have hC₂a₆ : (C₂ • (C₁ • W)).a₆ = 0 := by
    rw [WeierstrassCurve.variableChange_a₆, hC₂]
    simp [hC₁a₆]
  have hC₂a₂a₃ : (C₂ • (C₁ • W)).a₃ = (C₂ • (C₁ • W)).a₂ := by
    rw [WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₂, hC₂]
    simp only [Units.val_inv_eq_inv_val]
    field_simp [hscale]
    rw [hscale]
    field_simp
    ring
  have hC₂a₂ :
      (C₂ • (C₁ • W)).a₂ = ((scale : ℚ))⁻¹ ^ 2 * (C₁ • W).a₂ := by
    rw [WeierstrassCurve.variableChange_a₂, hC₂]
    simp
  have hC₂a₂ne : (C₂ • (C₁ • W)).a₂ ≠ 0 := by
    rw [hC₂a₂]
    exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hscale0)) hC₁a₂
  have hb0 : b ≠ 0 := by
    rw [hb, neg_ne_zero]
    exact hC₂a₂ne
  have hcurve :
      C₂ • (C₁ • W) = tateNormalCurve b c := by
    ext <;> simp [tateNormalCurve, hb, hc, hC₂a₄, hC₂a₆, hC₂a₂a₃]
  have h00₂ : (C₂ • (C₁ • W)).toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.nonsingular_zero.mpr
      ⟨hC₂a₆, Or.inl (by rw [hC₂a₂a₃]; exact hC₂a₂ne)⟩
  have hdisc :
      ((scale : ℚ))⁻¹ ^ 12 * W.Δ = (C₂ • (C₁ • W)).Δ := by
    rw [WeierstrassCurve.variableChange_Δ,
      WeierstrassCurve.variableChange_Δ, hC₁, hC₂]
    simp
  refine ⟨b, c, ((scale : ℚ))⁻¹, inv_ne_zero hscale0, hb0,
    hcurve ▸ h00₂,
    (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm.trans
      ((WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂).symm.trans
        (WeierstrassCurve.Affine.Point.equivOfEq hcurve)), ?_, ?_, ?_, ?_⟩
  · have hfirst :
        (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm P =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [← hmap₁]
      exact (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm_apply_apply _
    have hsecond :
        WeierstrassCurve.Affine.Point.equivVariableChange (C₁ • W) C₂
            (WeierstrassCurve.Affine.Point.some 0 0 h00₂) =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [WeierstrassCurve.Affine.Point.equivVariableChange_some]
      exact WeierstrassCurve.Affine.Point.some_eq_some _
        (by simp [hC₂]) (by simp [hC₂])
    simp only [AddEquiv.trans_apply, hfirst, ← hsecond,
      AddEquiv.symm_apply_apply, WeierstrassCurve.Affine.Point.equivOfEq_some]
  · rw [hdisc, hcurve]
  · have hc₄ :
        ((scale : ℚ))⁻¹ ^ 4 * W.c₄ = (C₂ • (C₁ • W)).c₄ := by
      rw [WeierstrassCurve.variableChange_c₄,
        WeierstrassCurve.variableChange_c₄, hC₁, hC₂]
      simp
    rw [hc₄, hcurve]
  · have hc₆ :
        ((scale : ℚ))⁻¹ ^ 6 * W.c₆ = (C₂ • (C₁ • W)).c₆ := by
      rw [WeierstrassCurve.variableChange_c₆,
        WeierstrassCurve.variableChange_c₆, hC₁, hC₂]
      simp
    rw [hc₆, hcurve]

/-- The marked point `P = (0,0)` doubles to `(b,bc)` on Tate normal form. -/
theorem two_mul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₂ : (tateNormalCurve b c).toAffine.Nonsingular b (b * c),
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some b (b * c) h₂ := by
  let W := tateNormalCurve b c
  have hneg : W.toAffine.negY 0 0 = b := by
    simp [W, tateNormalCurve, WeierstrassCurve.Affine.negY]
  have hnotvertical : (0 : ℚ) ≠ W.toAffine.negY 0 0 := by
    rw [hneg]
    exact fun h => hb h.symm
  have hslope : W.toAffine.slope 0 0 0 0 = 0 := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hnotvertical]
    simp [W, tateNormalCurve]
  have hx :
      W.toAffine.addX 0 0 (W.toAffine.slope 0 0 0 0) = b := by
    rw [hslope]
    simp [W, tateNormalCurve]
  have hy :
      W.toAffine.addY 0 0 0 (W.toAffine.slope 0 0 0 0) = b * c := by
    rw [hslope]
    simp [W, tateNormalCurve, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY]
    ring
  have h₂ : W.toAffine.Nonsingular b (b * c) := by
    have h :=
      WeierstrassCurve.Affine.nonsingular_add h00 h00
        (fun hxy => hnotvertical hxy.right)
    rwa [hx, hy] at h
  refine ⟨h₂, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hnotvertical]
  exact WeierstrassCurve.Affine.Point.some_eq_some W hx hy

/-- The marked point `P = (0,0)` triples to `(c,b-c)` on Tate normal form. -/
theorem three_mul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₃ : (tateNormalCurve b c).toAffine.Nonsingular c (b - c),
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
            WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some c (b - c) h₃ := by
  let W := tateNormalCurve b c
  obtain ⟨h₂, hdouble⟩ := two_mul_origin_coordinates b c hb h00
  have hslope : W.toAffine.slope b 0 (b * c) 0 = c := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hb]
    field_simp
    ring
  have hx :
      W.toAffine.addX b 0 (W.toAffine.slope b 0 (b * c) 0) = c := by
    rw [hslope]
    simp [W, tateNormalCurve]
    ring
  have hy :
      W.toAffine.addY b 0 (b * c) (W.toAffine.slope b 0 (b * c) 0) =
        b - c := by
    rw [hslope]
    simp [W, tateNormalCurve, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY]
    ring
  have h₃ : W.toAffine.Nonsingular c (b - c) := by
    have h :=
      WeierstrassCurve.Affine.nonsingular_add h₂ h00
        (fun hxy => hb hxy.left)
    rwa [hx, hy] at h
  refine ⟨h₃, ?_⟩
  rw [hdouble]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hb]
  exact WeierstrassCurve.Affine.Point.some_eq_some W hx hy

/-- In scalar-multiplication notation, `2P = (b,bc)` for the marked Tate point. -/
theorem two_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₂ : (tateNormalCurve b c).toAffine.Nonsingular b (b * c),
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some b (b * c) h₂ := by
  simpa [two_nsmul] using two_mul_origin_coordinates b c hb h00

/-- In scalar-multiplication notation, `3P = (c,b-c)` for the marked Tate point. -/
theorem three_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₃ : (tateNormalCurve b c).toAffine.Nonsingular c (b - c),
      (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some c (b - c) h₃ := by
  obtain ⟨h₃, htriple⟩ := three_mul_origin_coordinates b c hb h00
  refine ⟨h₃, ?_⟩
  rw [show (3 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
  exact htriple

/-- If also `c ≠ 0`, then `4P` has the displayed rational coordinates. -/
theorem four_mul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₄ : (tateNormalCurve b c).toAffine.Nonsingular
        (b * (b - c) / c ^ 2) (b ^ 2 * (c ^ 2 + c - b) / c ^ 3),
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
              WeierstrassCurve.Affine.Point.some 0 0 h00 +
            WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some
          (b * (b - c) / c ^ 2) (b ^ 2 * (c ^ 2 + c - b) / c ^ 3) h₄ := by
  let W := tateNormalCurve b c
  obtain ⟨h₃, htriple⟩ := three_mul_origin_coordinates b c hb h00
  have hslope : W.toAffine.slope c 0 (b - c) 0 = (b - c) / c := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hc]
    ring
  have hx :
      W.toAffine.addX c 0 (W.toAffine.slope c 0 (b - c) 0) =
        b * (b - c) / c ^ 2 := by
    rw [hslope]
    simp [W, tateNormalCurve]
    field_simp [hc]
    ring
  have hy :
      W.toAffine.addY c 0 (b - c) (W.toAffine.slope c 0 (b - c) 0) =
        b ^ 2 * (c ^ 2 + c - b) / c ^ 3 := by
    rw [hslope]
    simp [W, tateNormalCurve, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY]
    field_simp [hc]
    ring
  have h₄ : W.toAffine.Nonsingular
      (b * (b - c) / c ^ 2) (b ^ 2 * (c ^ 2 + c - b) / c ^ 3) := by
    have h :=
      WeierstrassCurve.Affine.nonsingular_add h₃ h00
        (fun hxy => hc hxy.left)
    rwa [hx, hy] at h
  refine ⟨h₄, ?_⟩
  rw [htriple]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hc]
  exact WeierstrassCurve.Affine.Point.some_eq_some W hx hy


end MazurTorsion.Kubert

namespace MazurTorsion.ExceptionalTwoTen

export MazurTorsion.Kubert
  (tateNormalCurve three_nsmul_origin_eq_zero exists_tateNormalCurve_scaled
    two_mul_origin_coordinates three_mul_origin_coordinates
    two_nsmul_origin_coordinates three_nsmul_origin_coordinates
    four_mul_origin_coordinates)

end MazurTorsion.ExceptionalTwoTen

end
end


/- Source module: MazurTorsion.Kubert.TateNormalFormMultiples. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Further multiples on Tate normal form

This file extends the kernel-checked low-multiple calculations for the marked point
`P = (0, 0)` on

`y² + (1-c)xy - by = x³ - bx²`.

The central lemma is a small recurrence: if `Q = (x, y)` and `x ≠ 0`, it computes `Q + P`.
The formulas for `5P` and `6P` are then consequences of the already checked formula for `4P`.
Every denominator used below has a corresponding explicit nonvanishing hypothesis.
-/
section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The `X`-coordinate obtained by adding the marked Tate point `(0, 0)` to `(x, y)`. -/
def tateNextX (b c x y : ℚ) : ℚ :=
  (y / x) ^ 2 + (1 - c) * (y / x) + b - x

/-- The `Y`-coordinate obtained by adding the marked Tate point `(0, 0)` to `(x, y)`. -/
def tateNextY (b c x y : ℚ) : ℚ :=
  -((y / x) * (tateNextX b c x y - x) + y) -
      (1 - c) * tateNextX b c x y + b

/-- Kernel-checked recurrence for adding the marked point to an affine Tate-normal-form point.
The sole denominator introduced by the secant formula is recorded as `hx`. -/
theorem add_origin_coordinates
    (b c x y : ℚ) (hx : x ≠ 0)
    (hxy : (tateNormalCurve b c).toAffine.Nonsingular x y)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ hnext : (tateNormalCurve b c).toAffine.Nonsingular
        (tateNextX b c x y) (tateNextY b c x y),
      WeierstrassCurve.Affine.Point.some x y hxy +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some
          (tateNextX b c x y) (tateNextY b c x y) hnext := by
  let W := tateNormalCurve b c
  have hslope : W.toAffine.slope x 0 y 0 = y / x := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
    ring
  have hxnext :
      W.toAffine.addX x 0 (W.toAffine.slope x 0 y 0) =
        tateNextX b c x y := by
    rw [hslope]
    simp [W, tateNormalCurve, tateNextX]
  have hynext :
      W.toAffine.addY x 0 y (W.toAffine.slope x 0 y 0) =
        tateNextY b c x y := by
    rw [hslope]
    simp [W, tateNormalCurve, tateNextX, tateNextY,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY]
  have hnext :
      W.toAffine.Nonsingular (tateNextX b c x y) (tateNextY b c x y) := by
    have h :=
      WeierstrassCurve.Affine.nonsingular_add hxy h00
        (fun hpair => hx hpair.left)
    rwa [hxnext, hynext] at h
  refine ⟨hnext, ?_⟩
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
  exact WeierstrassCurve.Affine.Point.some_eq_some W hxnext hynext

/-- Successive affine coordinates obtained by starting at `2P = (b, bc)` and
repeatedly adding the marked Tate point `P = (0, 0)`.  Index `n` is intended
to represent `(n + 2)P`; the accompanying theorem records exactly the
nonzero abscissas needed for this rational recurrence to agree with the group
law. -/
def tateSuccessiveCoordinates (b c : ℚ) : ℕ → ℚ × ℚ
  | 0 => (b, b * c)
  | n + 1 =>
      let Q := tateSuccessiveCoordinates b c n
      (tateNextX b c Q.1 Q.2, tateNextY b c Q.1 Q.2)

/-- The recurrence-defined abscissa of `(n + 2)P`. -/
def tateSuccessiveX (b c : ℚ) (n : ℕ) : ℚ :=
  (tateSuccessiveCoordinates b c n).1

/-- The recurrence-defined ordinate of `(n + 2)P`. -/
def tateSuccessiveY (b c : ℚ) (n : ℕ) : ℚ :=
  (tateSuccessiveCoordinates b c n).2

@[simp] lemma tateSuccessiveX_zero (b c : ℚ) :
    tateSuccessiveX b c 0 = b := rfl

@[simp] lemma tateSuccessiveY_zero (b c : ℚ) :
    tateSuccessiveY b c 0 = b * c := rfl

@[simp] lemma tateSuccessiveX_succ (b c : ℚ) (n : ℕ) :
    tateSuccessiveX b c (n + 1) =
      tateNextX b c (tateSuccessiveX b c n) (tateSuccessiveY b c n) := by
  rfl

@[simp] lemma tateSuccessiveY_succ (b c : ℚ) (n : ℕ) :
    tateSuccessiveY b c (n + 1) =
      tateNextY b c (tateSuccessiveX b c n) (tateSuccessiveY b c n) := by
  rfl



/-- Fraction-free numerator and denominator data for one pair of Tate
recurrence coordinates. -/
structure TateClearedCoordinateDatum where
  /-- Numerator of the x-coordinate. -/ xNum : ℚ
  /-- Denominator of the x-coordinate. -/ xDen : ℚ
  /-- Numerator of the y-coordinate. -/ yNum : ℚ
  /-- Denominator of the y-coordinate. -/ yDen : ℚ









/-- The `X`-coordinate of `5P` in Tate normal form. -/
def tateFiveX (b c : ℚ) : ℚ :=
  b * c * (c ^ 2 + c - b) / (b - c) ^ 2

/-- The `Y`-coordinate of `5P` in Tate normal form. -/
def tateFiveY (b c : ℚ) : ℚ :=
  b * c ^ 2 * (b ^ 2 - b * c - c ^ 3) / (b - c) ^ 3

/-- Provided `b`, `c`, and `b-c` are nonzero, the marked point has the displayed fifth
multiple. These are exactly the denominators used in the calculation. -/
theorem five_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₅ : (tateNormalCurve b c).toAffine.Nonsingular
        (tateFiveX b c) (tateFiveY b c),
      (5 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some (tateFiveX b c) (tateFiveY b c) h₅ := by
  let x₄ : ℚ := b * (b - c) / c ^ 2
  let y₄ : ℚ := b ^ 2 * (c ^ 2 + c - b) / c ^ 3
  obtain ⟨h₄, hfour⟩ := four_mul_origin_coordinates b c hb hc h00
  have hx₄ : x₄ ≠ 0 := by
    exact div_ne_zero (mul_ne_zero hb (sub_ne_zero.mpr hbc))
      (pow_ne_zero 2 hc)
  obtain ⟨h₅, hfive⟩ := add_origin_coordinates b c x₄ y₄ hx₄ h₄ h00
  have hx :
      tateNextX b c x₄ y₄ = tateFiveX b c := by
    simp only [x₄, y₄, tateNextX, tateFiveX]
    field_simp [hc, sub_ne_zero.mpr hbc]
    ring
  have hy :
      tateNextY b c x₄ y₄ = tateFiveY b c := by
    simp only [x₄, y₄, tateNextY, tateNextX, tateFiveY]
    field_simp [hc, sub_ne_zero.mpr hbc]
    ring
  refine ⟨hx ▸ hy ▸ h₅, ?_⟩
  rw [show (5 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      (WeierstrassCurve.Affine.Point.some 0 0 h00 +
              WeierstrassCurve.Affine.Point.some 0 0 h00 +
            WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00) +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
  rw [hfour, hfive]
  exact WeierstrassCurve.Affine.Point.some_eq_some _ hx hy







end MazurTorsion.Kubert

end
end


/- Source module: MazurTorsion.Kubert.OrderFifteenReduction. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Reduction of a point of order fifteen

An exact rational point of order `15` can be put in Tate normal form. Its fifth multiple then
has exact order `3`, so the `X`-coordinate of that multiple is a root of the third division
polynomial. Clearing the two honest Tate denominators produces the polynomial
`orderFifteenPolynomial` below.

This file proves only the forward modular reduction. In particular, it makes no assertion about
the rational points of the resulting affine parameter curve.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- A compact polynomial equation for the Tate-parameter image of `X₁(15)`.

Writing `A = c² + c - b` and `d = b - c`, this is the third division polynomial
at `x(5P) = bcA/d²`, after multiplication by `d⁸` and removal of the nonzero factor `b³`. -/
def orderFifteenPolynomial (b c : ℚ) : ℚ :=
  let A := c ^ 2 + c - b
  let d := b - c
  3 * b * (c * A) ^ 4 +
    ((1 - c) ^ 2 - 4 * b) * (c * A) ^ 3 * d ^ 2 +
    3 * (c - 1) * (c * A) ^ 2 * d ^ 4 +
    3 * (c * A) * d ^ 6 -
    d ^ 8

/-- The discriminant of the two-parameter Tate normal form, in a factored presentation useful
for retaining the twelfth-power scale supplied by Tate normalization. -/
def tateNormalDiscriminant (b c : ℚ) : ℚ :=
  b ^ 3 *
    (16 * b ^ 2 - 8 * b * c ^ 2 - 20 * b * c + b +
      c ^ 4 - 3 * c ^ 3 + 3 * c ^ 2 - c)

lemma tateNormalCurve_discriminant (b c : ℚ) :
    (tateNormalCurve b c).Δ = tateNormalDiscriminant b c := by
  simp only [tateNormalCurve, tateNormalDiscriminant, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

private lemma c_ne_zero_of_marked_order_fifteen
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 15) :
    c ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfourNe : (4 : ℕ) • P ≠ 0 := by
    intro hfour
    have hdvd : addOrderOf P ∣ 4 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hfour
    rw [horder] at hdvd
    norm_num at hdvd
  intro hc
  subst c
  obtain ⟨h₃, hthree⟩ := three_nsmul_origin_coordinates b 0 hb h00
  have hneg :
      WeierstrassCurve.Affine.Point.some 0 (b - 0) h₃ = -P := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp) (by simp [W, tateNormalCurve, WeierstrassCurve.Affine.negY])
  apply hfourNe
  rw [show (4 : ℕ) • P = (3 : ℕ) • P + P by abel]
  rw [hthree, hneg, neg_add_cancel]

private lemma parameters_ne_of_marked_order_fifteen
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 15) :
    b ≠ c := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfiveNe : (5 : ℕ) • P ≠ 0 := by
    intro hfive
    have hdvd : addOrderOf P ∣ 5 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr hfive
    rw [horder] at hdvd
    norm_num at hdvd
  intro hbc
  subst c
  obtain ⟨h₂, htwo⟩ := two_nsmul_origin_coordinates b b hb h00
  obtain ⟨h₃, hthree⟩ := three_nsmul_origin_coordinates b b hb h00
  have hneg :
      WeierstrassCurve.Affine.Point.some b (b * b) h₂ =
        -WeierstrassCurve.Affine.Point.some b (b - b) h₃ := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp) (by simp [tateNormalCurve, WeierstrassCurve.Affine.negY]; ring)
  apply hfiveNe
  rw [show (5 : ℕ) • P = (2 : ℕ) • P + (3 : ℕ) • P by abel]
  rw [htwo, hthree, hneg, neg_add_cancel]

private lemma orderFifteenPolynomial_eq_zero_of_three_division
    (b c : ℚ) (hb : b ≠ 0) (hbc : b ≠ c)
    (hψ :
      Polynomial.eval (tateFiveX b c)
        (tateNormalCurve b c).toAffine.Ψ₃ = 0) :
    orderFifteenPolynomial b c = 0 := by
  simp only [tateFiveX, tateNormalCurve, WeierstrassCurve.Ψ₃,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈] at hψ
  field_simp [sub_ne_zero.mpr hbc] at hψ
  have hscaled :
      b ^ 3 * orderFifteenPolynomial b c = 0 := by
    simp only [orderFifteenPolynomial]
    ring_nf at hψ ⊢
    exact hψ
  exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 3 hb)

/-- Exact order `15` of the marked Tate point forces the compact parameter polynomial to vanish.
The proof records the fifth multiple explicitly and uses its exact order `3`. -/
theorem orderFifteenPolynomial_eq_zero_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 15) :
    orderFifteenPolynomial b c = 0 := by
  let P : (tateNormalCurve b c).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hc := c_ne_zero_of_marked_order_fifteen b c hb h00 horder
  have hbc := parameters_ne_of_marked_order_fifteen b c hb h00 horder
  obtain ⟨h₅, hfive⟩ :=
    five_nsmul_origin_coordinates b c hb hc hbc h00
  have hfiveOrder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some
          (tateFiveX b c) (tateFiveY b c) h₅) = 3 := by
    rw [← hfive]
    change addOrderOf ((5 : ℕ) • P) = 3
    rw [addOrderOf_nsmul' P (by norm_num), horder]
    norm_num
  have hthree :
      (3 : ℕ) •
          WeierstrassCurve.Affine.Point.some
            (tateFiveX b c) (tateFiveY b c) h₅ = 0 := by
    rw [← hfiveOrder]
    exact addOrderOf_nsmul_eq_zero _
  exact orderFifteenPolynomial_eq_zero_of_three_division b c hb hbc <|
    (MazurTorsion.ThreeTorsion.three_nsmul_some_eq_zero_iff
      (tateNormalCurve b c).toAffine h₅).mp hthree

/-- A rational point of exact order `15` produces a point on the explicit Tate-parameter
curve, with every denominator condition and the original discriminant scale retained.

The additional condition `c²+c-b ≠ 0` follows from the displayed polynomial and `b-c ≠ 0`;
it is useful when continuing the checked multiple recurrence from `5P` to `6P`. -/
theorem exists_tateOrderFifteen_certificate
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 15) :
    ∃ b c u : ℚ,
      u ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧
      c ^ 2 + c - b ≠ 0 ∧
      orderFifteenPolynomial b c = 0 ∧
      u ^ 12 * E.Δ = tateNormalDiscriminant b c := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  have hQ2 : Q + Q ≠ 0 := by
    intro h
    have hdvd : addOrderOf Q ∣ 2 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [two_nsmul]
        exact h)
    rw [hQ] at hdvd
    norm_num at hdvd
  have hQ3 : Q + Q + Q ≠ 0 := by
    intro h
    have hdvd : addOrderOf Q ∣ 3 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [show (3 : ℕ) • Q = Q + Q + Q by abel]
        exact h)
    rw [hQ] at hdvd
    norm_num at hdvd
  obtain ⟨b, c, u, hu, hb, h00, e, heQ, hdisc, -, -⟩ :=
    exists_tateNormalCurve_scaled (E⁄ℚ) Q hQ2 hQ3
  have hmarked :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 15 := by
    rw [← heQ, AddEquiv.addOrderOf_eq]
    exact hQ
  have hc := c_ne_zero_of_marked_order_fifteen b c hb h00 hmarked
  have hbc := parameters_ne_of_marked_order_fifteen b c hb h00 hmarked
  have hpoly :=
    orderFifteenPolynomial_eq_zero_of_marked_order b c hb h00 hmarked
  have hnumerator : c ^ 2 + c - b ≠ 0 := by
    intro hzero
    have hd : b - c ≠ 0 := sub_ne_zero.mpr hbc
    have hpow : -(b - c) ^ 8 = 0 := by
      simpa [orderFifteenPolynomial, hzero] using hpoly
    exact pow_ne_zero 8 hd (neg_eq_zero.mp hpow)
  refine ⟨b, c, u, hu, hb, hc, hbc, hnumerator, hpoly, ?_⟩
  have hbase : (E⁄ℚ).Δ = E.Δ := by
    simp [WeierstrassCurve.baseChange]
  rw [← hbase, hdisc, tateNormalCurve_discriminant]

end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.Foundations.NaiveHeightDescent. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Vasily Ilin
-/



/-!
# Naïve-height descent for rational elliptic curves

This file is a narrow port of the height part of Michael Stoll's
`EllipticCurves/MordellWeil.lean`, commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.

It proves the approximate parallelogram law for the naïve logarithmic
height on affine Weierstrass points. Combined with Northcott and finite
index of multiplication by two or three, this gives finite generation by
the descent theorems in `Mathlib.GroupTheory.Descent`.

The much larger weak Mordell--Weil and Selmer-group layers are deliberately
not imported: callers may establish the required finite index by a
curve-specific descent.
-/

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R]
  {W' : WeierstrassCurve R}

open MvPolynomial Nat

lemma den_duplication_eq {x y : R} (h : W'.toAffine.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ =
      (2 * y + W'.a₁ * x + W'.a₃) ^ 2 := by
  have heq := (W'.toAffine.equation_iff x y).mp h
  simp only [b₂, b₄, b₆]
  linear_combination -4 * heq

lemma den_duplication_eq_zero_iff [IsReduced R] {x y : R}
    (h : W'.toAffine.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = 0 ↔
      y = W'.toAffine.negY x y := by
  rw [den_duplication_eq h, sq_eq_zero_iff,
    WeierstrassCurve.Affine.negY]
  grind only

variable {F : Type*} [Field F]
  {W : WeierstrassCurve F}

lemma den_duplication_ne_zero_or_num_duplication_ne_zero
    {x y : F} (h : W.toAffine.Nonsingular x y) :
    4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ≠ 0 ∨
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ ≠ 0 := by
  have ⟨h₁, h₂⟩ := (W.toAffine.nonsingular_iff x y).mp h
  rw [W.toAffine.equation_iff x y] at h₁
  by_cases hzero : 2 * y + W.a₁ * x + W.a₃ = 0
  · right
    replace h₂ : W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
      grind
    contrapose! h₂
    rw [b₄, b₆, b₈] at h₂
    grobner
  · left
    clear h₂
    contrapose! hzero
    rw [b₂, b₄, b₆] at hzero
    grobner

section Decidable

variable [DecidableEq F]

lemma addX_self_of_Y_ne {x y : F} (h : W.toAffine.Equation x y)
    (hn : y ≠ W.toAffine.negY x y) :
    W.toAffine.addX x x (W.toAffine.slope x x y y) =
      (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  have aux {a b c : F} (ha : a ≠ 0) :
      a ^ 2 * (b * (c / a)) = a * b * c := by
    field
  have hn' := (den_duplication_eq_zero_iff h).not.mpr hn
  refine mul_left_cancel₀ hn' ?_
  have hn'' : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [den_duplication_eq h] at hn'
    grind
  rw [mul_div_cancel₀ _ hn', WeierstrassCurve.Affine.addX,
    sub_sub, sub_sub, mul_sub, mul_add]
  simp only [WeierstrassCurve.Affine.slope, ↓reduceIte, hn]
  rw [WeierstrassCurve.Affine.negY,
    show y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ by ring,
    div_pow]
  nth_rewrite 1 2 [den_duplication_eq h]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hn'', aux hn'', b₂, b₄, b₆, b₈]
  linear_combination -W.a₁ ^ 2 * (W.toAffine.equation_iff x y).mp h

lemma addX_of_X_ne {xP yP xQ yQ : F} (hn : xP ≠ xQ) :
    W.toAffine.addX xP xQ (W.toAffine.slope xP xQ yP yQ) =
      ((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) -
          (W.a₂ + xP + xQ) * (xP - xQ) ^ 2) /
        (xP - xQ) ^ 2 := by
  have hxPQ : xP - xQ ≠ 0 := by
    grind only
  simp [WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.slope, hn, div_pow]
  field

lemma Point.xRep_add_self_of_Y_ne {x y : F}
    (h : W.toAffine.Nonsingular x y)
    (hn : y ≠ W.toAffine.negY x y) :
    (some x y h + some x y h).xRep =
      ![(x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
          (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆), 1] := by
  simp only [add_self_of_Y_ne hn, ← addX_self_of_Y_ne h.1 hn, xRep_some]



lemma Point.xRep_add_of_X_ne {xP yP xQ yQ : F}
    (hP : W.toAffine.Nonsingular xP yP)
    (hQ : W.toAffine.Nonsingular xQ yQ)
    (hn : xP ≠ xQ) :
    (some xP yP hP + some xQ yQ hQ).xRep =
      ![((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) -
            (W.a₂ + xP + xQ) * (xP - xQ) ^ 2) /
          (xP - xQ) ^ 2, 1] := by
  simp only [add_of_X_ne (h₁ := hP) (h₂ := hQ) hn, xRep_some,
    addX_of_X_ne hn]

lemma Point.xRep_sub_of_X_ne {xP yP xQ yQ : F}
    (hP : W.toAffine.Nonsingular xP yP)
    (hQ : W.toAffine.Nonsingular xQ yQ)
    (hn : xP ≠ xQ) :
    (some xP yP hP - some xQ yQ hQ).xRep =
      ![((yP + yQ + W.a₁ * xQ + W.a₃) ^ 2 +
            W.a₁ * (yP + yQ + W.a₁ * xQ + W.a₃) * (xP - xQ) -
            (W.a₂ + xP + xQ) * (xP - xQ) ^ 2) /
          (xP - xQ) ^ 2, 1] := by
  simp only [sub_eq_add_neg (some ..), neg_some hQ,
    add_of_X_ne (h₁ := hP) (h₂ := (nonsingular_neg ..).mpr hQ) hn,
    xRep_some, addX_of_X_ne hn]
  grind only [negY]

end Decidable

lemma finite_preimage_xRep (x : F) :
    {P : W.toAffine.Point | P.xRep = ![x, 1]}.Finite := by
  rcases Set.eq_empty_or_nonempty
      {P : W.toAffine.Point | P.xRep = ![x, 1]} with h | h
  · exact h ▸ Set.finite_empty
  choose Q hQ using h
  simp only [Set.mem_setOf_eq] at hQ
  rw [show {P | P.xRep = ![x, 1]} = {Q, -Q} by
    ext
    simp [← hQ, Point.xRep_eq_xRep_iff]]
  simp

lemma finite_preimage_xRep0 (x : F) :
    {P : W.toAffine.Point | P.xRep 0 = x}.Finite := by
  have hsubset :
      {P : W.toAffine.Point | P.xRep 0 = x} ⊆
        {P | P.xRep = ![x, 1]} ∪ {0} := by
    intro P hP
    match P with
    | 0 => simp
    | .some x' y h => simp_all [Point.xRep_some]
  exact (finite_preimage_xRep x).union (Set.finite_singleton 0) |>.subset hsubset

lemma Point.sym2x_eq (P Q : W.toAffine.Point) :
    P.sym2x Q =
      ![P.xRep 0 * Q.xRep 0,
        P.xRep 0 * Q.xRep 1 + P.xRep 1 * Q.xRep 0,
        P.xRep 1 * Q.xRep 1] :=
  rfl

private lemma Point.sym2x_P_P_eq_addSubMap (P : W.toAffine.Point) :
    Point.sym2x P P =
      fun i ↦ (addSubMap W i).eval <| P.sym2x 0 := by
  match P with
  | 0 =>
    simp only [Point.sym2x_zero_zero, succ_eq_add_one, reduceAdd,
      addSubMap, Fin.isValue]
    ext i
    fin_cases i <;> simp
  | some .. =>
    simp only [Point.sym2x_some_some, succ_eq_add_one, reduceAdd,
      Point.sym2x_some_zero, addSubMap, Fin.isValue]
    ext i
    fin_cases i <;> simp [pow_two, two_mul]

section Decidable

variable [DecidableEq F]

private lemma Point.sym2x_P_add_P_zero (P : W.toAffine.Point) :
    ∃ t : F, t ≠ 0 ∧
      t • Point.sym2x (P + P) 0 =
        fun i ↦ (addSubMap W i).eval <| P.sym2x P := by
  match P with
  | 0 =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [add_zero, Point.sym2x_zero_zero, one_smul, addSubMap]
    ext i
    fin_cases i <;> simp
  | some x y h =>
    have heq := (W.toAffine.equation_iff x y).mp h.1
    have hrs :
        (fun i ↦ (addSubMap W i).eval <|
          (some x y h).sym2x (some x y h)) =
          ![x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈,
            4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆, 0] := by
      ext i
      fin_cases i <;> simp [addSubMap] <;> ring
    rw [hrs]
    by_cases hvertical : y = W.toAffine.negY x y
    · have hden := (den_duplication_eq_zero_iff h.1).mpr hvertical
      rw [hden, add_self_of_Y_eq hvertical, Point.sym2x_zero_zero]
      refine ⟨_,
        den_duplication_ne_zero_or_num_duplication_ne_zero h
          |>.neg_resolve_left hden, ?_⟩
      simp
    · have hden := (den_duplication_eq_zero_iff h.1).not.mpr hvertical
      refine ⟨_, hden, ?_⟩
      simp [Point.sym2x_eq, Point.xRep_add_self_of_Y_ne h hvertical,
        mul_div_cancel₀ _ hden]

theorem Point.sym2x_add_sub_eq_addSubMap_sym2x
    (P Q : W.toAffine.Point) :
    ∃ t : F, t ≠ 0 ∧
      t • Point.sym2x (P + Q) (P - Q) =
        fun i ↦ (addSubMap W i).eval <| Point.sym2x P Q := by
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using P.sym2x_P_add_P_zero
  rcases eq_or_ne Q (-P) with rfl | hPQ'
  · simpa [Point.sym2x_neg_right, Point.sym2x_comm 0] using
      P.sym2x_P_add_P_zero
  match P, Q with
  | P, 0 =>
    exact ⟨1, one_ne_zero, by simpa using P.sym2x_P_P_eq_addSubMap⟩
  | 0, Q =>
    refine ⟨1, one_ne_zero, ?_⟩
    simpa [Point.sym2x_neg_right, Point.sym2x_comm _ Q] using
      Q.sym2x_P_P_eq_addSubMap
  | some xP yP hP, some xQ yQ hQ =>
    have hxPQ : xP ≠ xQ := fun heq ↦ by
      grind only [X_eq_iff.mp heq]
    have hrs :
        (fun i ↦ (addSubMap W i).eval <|
          (some xP yP hP).sym2x (some xQ yQ hQ)) =
          ![(xP * xQ) ^ 2 - W.b₄ * (xP * xQ) -
              W.b₆ * (xP + xQ) - W.b₈,
            2 * (xP + xQ) * (xP * xQ) +
              W.b₂ * (xP * xQ) + W.b₄ * (xP + xQ) + W.b₆,
            (xP - xQ) ^ 2] := by
      ext i
      fin_cases i <;> simp [addSubMap]
      ring
    have hsub : xP - xQ ≠ 0 := sub_ne_zero_of_ne hxPQ
    refine ⟨(xP - xQ) ^ 2, pow_ne_zero 2 hsub, ?_⟩
    have heqP := (W.toAffine.equation_iff xP yP).mp hP.1
    have heqQ := (W.toAffine.equation_iff xQ yQ).mp hQ.1
    rw [hrs, Point.sym2x_eq, Point.xRep_add_of_X_ne hP hQ hxPQ,
      Point.xRep_sub_of_X_ne hP hQ hxPQ, b₂, b₄, b₆, b₈]
    ext i
    fin_cases i <;> simp [field] <;> grobner

end Decidable

section Height

open Height

variable [AdmissibleAbsValues F]

/-- The logarithmic projective height of an affine point's `x`-coordinates. -/
noncomputable def Point.naiveHeight (P : W.toAffine.Point) : ℝ :=
  logHeight P.xRep

lemma Point.naiveHeight_eq_logHeight (P : W.toAffine.Point) :
    P.naiveHeight = logHeight P.xRep :=
  rfl

lemma Point.naiveHeight_eq_logHeight₁ {P : W.toAffine.Point} :
    P.naiveHeight = logHeight₁ (P.xRep 0) := by
  match P with
  | 0 => simp [naiveHeight, xRep]
  | some .. =>
    simpa [naiveHeight] using (logHeight₁_eq_logHeight _).symm

variable (W)

lemma abs_logHeight_sym2x_sub_le :
    ∃ C, ∀ P Q : W.toAffine.Point,
      |logHeight (P.sym2x Q) - (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight_sym2_sub_le F
  refine ⟨C, fun P Q ↦ ?_⟩
  rw [P.naiveHeight_eq_logHeight, Q.naiveHeight_eq_logHeight,
    Point.sym2x_eq]
  have hmul := logHeight_fun_mul_eq P.xRep_ne_zero Q.xRep_ne_zero
  have hvec (v : Fin 2 → F) : ![v 0, v 1] = v := by
    ext i
    fin_cases i <;> simp
  have hzero (P : W.toAffine.Point) : ![P.xRep 0, P.xRep 1] ≠ 0 :=
    hvec P.xRep ▸ P.xRep_ne_zero
  specialize hC (hzero P) (hzero Q)
  rw [hvec P.xRep, hvec Q.xRep] at *
  grind only [= abs.eq_1, = max_def]

variable [W.toAffine.IsElliptic]

theorem approx_parallelogram_law [DecidableEq F] :
    ∃ C, ∀ P Q : W.toAffine.Point,
      |(P + Q).naiveHeight + (P - Q).naiveHeight -
          2 * (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := abs_logHeight_sym2x_sub_le W
  obtain ⟨C₂, hC₂⟩ :=
    WeierstrassCurve.abs_logHeight_addSubMap_sub_two_mul_logHeight_le W
  refine ⟨3 * C₁ + C₂, fun P Q ↦ ?_⟩
  obtain ⟨t, ht₀, ht⟩ :=
    Point.sym2x_add_sub_eq_addSubMap_sym2x P Q
  replace ht := congrArg logHeight ht
  rw [Height.logHeight_smul_eq_logHeight _ ht₀] at ht
  have hPQ := hC₁ P Q
  have haddsub := hC₁ (P + Q) (P - Q)
  have hC := ht ▸ hC₂ (P.sym2x Q)
  generalize (P + Q).naiveHeight + (P - Q).naiveHeight = A at haddsub ⊢
  generalize logHeight ((P + Q).sym2x (P - Q)) = B at hC haddsub
  generalize logHeight (P.sym2x Q) = B' at hPQ hC
  generalize P.naiveHeight + Q.naiveHeight = A' at hPQ ⊢
  grind only [= abs.eq_1, = max_def]

instance [Northcott (logHeight₁ (K := F))] :
    Northcott (Point.naiveHeight (F := F) (W := W)) := by
  eta_expand
  simp only [Point.naiveHeight_eq_logHeight₁]
  rw [← Function.comp_def]
  letI : Filter.TendstoCofinite (fun P : W.toAffine.Point ↦ P.xRep 0) :=
    (Filter.tendstoCofinite_iff_finite_preimage_singleton _).2 fun x ↦ by
      simpa only [Set.preimage, Set.mem_singleton_iff] using
        (finite_preimage_xRep0 (W := W) x)
  exact Northcott.comp_of_finite_fibers
    (h := fun P : W.toAffine.Point ↦ P.xRep 0)
    (h' := logHeight₁)

variable [Northcott (logHeight₁ (K := F))]
variable [DecidableEq F]

theorem fg_point_of_finiteIndex_two
    (hindex :
      (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range.FiniteIndex) :
    AddGroup.FG W.toAffine.Point := by
  have hnonneg (P : W.toAffine.Point) : 0 ≤ P.naiveHeight := by
    rw [Point.naiveHeight_eq_logHeight P]
    positivity
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.fg_of_descent' hindex hnonneg hC



end Height

end WeierstrassCurve.Affine

end


/- Source module: MazurTorsion.Foundations.TwoTorsion. Original headers retained. -/
section
/-
Copyright (c) 2026 Victor Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Aguiar
-/



/-!
# Rational two-torsion bounds

This file bounds the two-torsion of a Weierstrass curve in characteristic
different from two and excludes an elementary abelian subgroup of order eight.
These are elementary structural inputs to the torsion classification in
Mazur's theorem.
-/

namespace MazurTorsion

open scoped WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [NeZero (2 : F)]

noncomputable section

private noncomputable def twoTorsionRootMap :
    {P : (E⁄F).Point // (2 : ℕ) • P = 0} →
      Option (E.twoTorsionPolynomial.toPoly.rootSet F)
  | ⟨0, _⟩ => none
  | ⟨WeierstrassCurve.Affine.Point.some x y h, htwo⟩ => some ⟨x, by
      rw [Polynomial.mem_rootSet_of_ne]
      · simp only [Polynomial.aeval_def]
        rw [Algebra.algebraMap_self, Polynomial.eval₂_id]
        have hneg : WeierstrassCurve.Affine.Point.some x y h =
            -WeierstrassCurve.Affine.Point.some x y h := by
          rw [← add_eq_zero_iff_eq_neg]
          simpa [two_nsmul] using htwo
        have hy : y = (E⁄F).negY x y := by
          simpa only [WeierstrassCurve.Affine.Point.neg_some,
            WeierstrassCurve.Affine.Point.some.injEq, true_and] using hneg
        have heq := h.1
        rw [WeierstrassCurve.Affine.equation_iff] at heq
        simp only [WeierstrassCurve.Affine.negY] at hy
        change y = -y - E.a₁ * x - E.a₃ at hy
        change y ^ 2 + E.a₁ * x * y + E.a₃ * y =
          x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ at heq
        have hlin : 2 * y + E.a₁ * x + E.a₃ = 0 := by
          linear_combination hy
        simp only [Cubic.toPoly, WeierstrassCurve.twoTorsionPolynomial,
          Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X]
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆]
        linear_combination -4 * heq +
          (2 * y + E.a₁ * x + E.a₃) * hlin
      · intro hp
        have hdeg :
            E.twoTorsionPolynomial.toPoly.natDegree = 3 :=
          Cubic.natDegree_of_a_ne_zero' (by
            rw [show (4 : F) = 2 ^ 2 by norm_num]
            exact pow_ne_zero 2 (NeZero.ne (2 : F)))
        rw [hp, Polynomial.natDegree_zero] at hdeg
        omega⟩

private theorem twoTorsionRootMap_injective :
    Function.Injective (twoTorsionRootMap E) := by
  rintro ⟨P, hP⟩ ⟨Q, hQ⟩ h
  apply Subtype.ext
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | some x y hxy => simp [twoTorsionRootMap] at h
  | some x y hxy =>
      cases Q with
      | zero => simp [twoTorsionRootMap] at h
      | some x' y' hxy' =>
          simp only [twoTorsionRootMap, Option.some.injEq,
            Subtype.mk.injEq] at h
          have hxrep :
              (WeierstrassCurve.Affine.Point.some x y hxy).xRep =
                (WeierstrassCurve.Affine.Point.some x' y' hxy').xRep := by
            simp [h]
          rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxrep
            with heq | heq
          · exact heq
          · have hself :
                WeierstrassCurve.Affine.Point.some x' y' hxy' =
                  -WeierstrassCurve.Affine.Point.some x' y' hxy' := by
              rw [← add_eq_zero_iff_eq_neg]
              simpa [two_nsmul] using hQ
            rw [hself.symm] at heq
            exact heq

/-- The points killed by `2` form a finite type in characteristic different
from two. -/
theorem finite_two_torsion :
    Finite {P : (E⁄F).Point // (2 : ℕ) • P = 0} :=
  Finite.of_injective (twoTorsionRootMap E)
    (twoTorsionRootMap_injective E)



















end

end MazurTorsion

end


/- Source module: MazurTorsion.GroupTheory.IndexNSmulFG. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/



/-!
# The index of multiplication on a finitely generated abelian group

This file is a narrow port of the finitely-generated-abelian-group part of
Michael Stoll's `EllipticCurves/Mathlib/SelmerGroup.lean`, commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.

It extends `AddSubgroup.index_range_nsmul`, which treats a finite free
`ℤ`-module, to a finitely generated commutative group with torsion.  The
result will let a curve-specific two-descent turn a bound on
`E(ℚ) / 2 E(ℚ)` into a bound on the Mordell--Weil rank.
-/

/-- First-isomorphism counting: the cardinality of an additive group is the
cardinality of the kernel times the cardinality of the range of a homomorphism. -/
theorem AddMonoidHom.card_ker_mul_card_range {G H : Type*}
    [AddGroup G] [AddGroup H] (φ : G →+ H) :
    Nat.card φ.ker * Nat.card φ.range = Nat.card G := by
  rw [Nat.card_congr
      (QuotientAddGroup.quotientKerEquivRange φ).toEquiv.symm,
    mul_comm]
  exact
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker).symm

/-- On a finite additive group, the index of the range of an endomorphism
equals the cardinality of its kernel. -/
theorem AddMonoidHom.index_range_eq_card_ker {G : Type*}
    [AddGroup G] [Finite G] (φ : G →+ G) :
    φ.range.index = Nat.card φ.ker := by
  have h1 : φ.range.index * Nat.card φ.range = Nat.card G :=
    φ.range.index_mul_card
  exact
    Nat.eq_of_mul_eq_mul_right Nat.card_pos
      (h1.trans φ.card_ker_mul_card_range.symm)

/-- An additive equivalence maps the kernel of multiplication by `n` onto
the corresponding kernel. -/
lemma AddEquiv.map_ker_nsmulAddMonoidHom {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) (n : ℕ) :
    ((nsmulAddMonoidHom (α := M) n).ker).map e.toAddMonoidHom =
      (nsmulAddMonoidHom (α := N) n).ker := by
  ext x
  rw [AddSubgroup.mem_map_equiv]
  simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
  rw [← map_nsmul, EmbeddingLike.map_eq_zero_iff]

/-- Multiplication by `n` on a product has the product of the two ranges as
its range. -/
lemma nsmulAddMonoidHom_range_prod (A B : Type*)
    [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    (nsmulAddMonoidHom (α := A × B) n).range =
      ((nsmulAddMonoidHom (α := A) n).range).prod
        (nsmulAddMonoidHom (α := B) n).range := by
  ext x
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply,
    AddSubgroup.mem_prod]
  exact
    ⟨fun ⟨y, hy⟩ ↦
        ⟨⟨y.1, congrArg Prod.fst hy⟩, ⟨y.2, congrArg Prod.snd hy⟩⟩,
      fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ ⟨(a, b), Prod.ext ha hb⟩⟩

/-- Multiplication by `n` on a product has the product of the two kernels as
its kernel. -/
lemma nsmulAddMonoidHom_ker_prod (A B : Type*)
    [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    (nsmulAddMonoidHom (α := A × B) n).ker =
      ((nsmulAddMonoidHom (α := A) n).ker).prod
        (nsmulAddMonoidHom (α := B) n).ker := by
  ext x
  simp [AddMonoidHom.mem_ker, AddSubgroup.mem_prod, Prod.ext_iff]

/-- A finite module over a characteristic-zero ring has rank zero. -/
lemma Module.rank_eq_zero_of_finite (R M : Type*) [Ring R] [CharZero R]
    [AddCommGroup M] [Module R M] [Finite M] :
    Module.rank R M = 0 :=
  rank_eq_zero_iff.mpr fun x ↦
    ⟨addOrderOf x, Nat.cast_ne_zero.mpr (addOrderOf_pos x).ne',
      by
        rw [Nat.cast_smul_eq_nsmul]
        exact addOrderOf_nsmul_eq_zero x⟩

open scoped DirectSum in
open Module in
/-- The index of `nG` in a finitely generated commutative group `G` is
`n ^ rank(G)` times the cardinality of its `n`-torsion subgroup. -/
theorem AddSubgroup.index_range_nsmul_of_fg
    (G : Type*) [AddCommGroup G] [AddGroup.FG G]
    {n : ℕ} (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := G) n).range.index =
      n ^ finrank ℤ G *
        Nat.card (nsmulAddMonoidHom (α := G) n).ker := by
  obtain ⟨r, ι, fι, p, hp, e, ⟨eqv⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod G
  have hne (i : ι) : NeZero (p i ^ e i) :=
    ⟨pow_ne_zero _ (hp i).pos.ne'⟩
  have hTfin : Finite (⨁ i, ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have hidx :
      (nsmulAddMonoidHom (α := G) n).range.index =
        (nsmulAddMonoidHom
          (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).range.index := by
    simpa [AddEquiv.map_range_nsmulAddMonoidHom]
      using
        (AddSubgroup.index_map_equiv
          (nsmulAddMonoidHom (α := G) n).range eqv).symm
  have hker :
      Nat.card (nsmulAddMonoidHom (α := G) n).ker =
        Nat.card
          (nsmulAddMonoidHom
            (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).ker := by
    rw [← eqv.map_ker_nsmulAddMonoidHom n]
    exact
      Nat.card_congr
        (AddSubgroup.equivMapOfInjective _
          eqv.toAddMonoidHom eqv.injective).toEquiv
  have hrk : finrank ℤ G = r := by
    have h1 :
        Module.rank ℤ ((Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) = r := by
      set π :=
        LinearMap.fst ℤ (Fin r →₀ ℤ) (⨁ i, ZMod (p i ^ e i))
        with hπ
      have h0 : Module.rank ℤ (LinearMap.ker π) = 0 := by
        have e2 :
            LinearMap.ker π ≃ₗ[ℤ] ⨁ i, ZMod (p i ^ e i) :=
          { toFun := fun x ↦ x.1.2
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl
            invFun := fun t ↦ ⟨(0, t), rfl⟩
            left_inv := fun x ↦
              Subtype.ext (Prod.ext (x.2 : x.1.1 = 0).symm rfl)
            right_inv := fun _ ↦ rfl }
        rw [e2.rank_eq]
        exact Module.rank_eq_zero_of_finite ℤ _
      rw [← π.rank_range_add_rank_ker,
        LinearMap.range_eq_top.mpr Prod.fst_surjective, rank_top,
        rank_finsupp_self', Cardinal.mk_fin, h0, add_zero]
    have h2 :
        finrank ℤ ((Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) = r := by
      simp [Module.finrank, h1]
    rw [eqv.toIntLinearEquiv.finrank_eq]
    convert h2 using 2
  have hkerF : (nsmulAddMonoidHom (α := Fin r →₀ ℤ) n).ker = ⊥ :=
    (AddMonoidHom.ker_eq_bot_iff _).mpr
      (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hn)
  rw [hidx, hker, hrk, nsmulAddMonoidHom_range_prod,
    AddSubgroup.index_prod, AddSubgroup.index_range_nsmul,
    AddMonoidHom.index_range_eq_card_ker,
    nsmulAddMonoidHom_ker_prod,
    Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv,
    Nat.card_prod, hkerF]
  simp

end


/- Source module: MazurTorsion.NumberTheory.RatNorthcott. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Northcott's property for the rational logarithmic height

The logarithmic height of a rational number is the logarithm of the maximum of the absolute
value of its normalized numerator and its positive denominator. Consequently, a height bound
places the numerator and denominator in finite integer intervals. This file records that elementary
rational specialization of Northcott's theorem.
-/

section

namespace MazurTorsion

open Height

/-- The rational numbers of logarithmic height at most `B` form a finite set. -/
theorem finite_rat_logHeight₁_le (B : ℝ) :
    {q : ℚ | logHeight₁ q ≤ B}.Finite := by
  let N := Nat.ceil (Real.exp B)
  let encode : ℚ → ℤ × ℕ := fun q => (q.num, q.den)
  let box : Set (ℤ × ℕ) :=
    Set.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Set.Icc 0 N
  have hbox : box.Finite := by
    exact (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).prod (Set.finite_Icc 0 N)
  have himage : encode '' {q : ℚ | logHeight₁ q ≤ B} ⊆ box := by
    rintro p ⟨q, hq, rfl⟩
    have hmax_real : (max q.num.natAbs q.den : ℝ) ≤ Real.exp B := by
      apply Real.le_exp_of_log_le
      simpa only [Set.mem_setOf_eq, Rat.logHeight₁_eq_log_max, Nat.cast_max] using hq
    have hmax_cast : (max q.num.natAbs q.den : ℝ) ≤ (N : ℝ) :=
      hmax_real.trans (Nat.le_ceil (Real.exp B))
    have hmax : max q.num.natAbs q.den ≤ N := by
      exact_mod_cast hmax_cast
    have hnum : q.num.natAbs ≤ N := le_trans (le_max_left _ _) hmax
    have hden : q.den ≤ N := le_trans (le_max_right _ _) hmax
    have hnum_upper : q.num ≤ (N : ℤ) := by
      exact Int.le_natAbs.trans (Int.ofNat_le.mpr hnum)
    have hnum_lower : -(N : ℤ) ≤ q.num := by
      have hneg : -q.num ≤ (N : ℤ) :=
        Int.le_natAbs.trans (by simpa only [Int.natAbs_neg] using Int.ofNat_le.mpr hnum)
      omega
    exact ⟨⟨hnum_lower, hnum_upper⟩, ⟨Nat.zero_le _, hden⟩⟩
  refine Set.Finite.of_finite_image (hbox.subset himage) ?_
  intro q _ r _ h
  exact Rat.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- The usual logarithmic height on `ℚ` has Northcott's property. -/
instance rationalLogHeightNorthcott : Northcott (logHeight₁ (K := ℚ)) where
  finite_le := finite_rat_logHeight₁_le

end MazurTorsion

end
end


/- Source module: EllipticCurves.Mathlib.EllipticCurvePoint. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


/-!
# Points of Weierstrass curves over finite fields: decidability and finiteness

Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
Exact-pin changes are documented in `PORTING.md`.

This file provides `Decidable` instances for the predicates `WeierstrassCurve.Affine.Equation`
and `WeierstrassCurve.Affine.Nonsingular` (over any commutative ring with decidable equality),
and deduces `Finite` and `Fintype` instances for the type `WeierstrassCurve.Affine.Point` of
nonsingular points of a Weierstrass curve over a finite ring, via Mathlib's
`WeierstrassCurve.Affine.nonsingularPointEquiv`.

The decision procedure goes through `equation_iff`/`nonsingular_iff`, so it evaluates the
Weierstrass polynomials directly in the base ring, with no `Polynomial` arithmetic involved.
Consequently, for a concrete curve over `ZMod p` the number of points is computable by `decide`:
`Fintype.card W.Point` enumerates the pairs in `ZMod p × ZMod p` and filters by the (decidable)
nonsingularity condition.

We also provide `WeierstrassCurve.Affine.Point.mapEquiv`, the group *isomorphism* on points
induced by an isomorphism of base fields (the equiv version of
`WeierstrassCurve.Affine.Point.map`); it transports point counts along residue-field
identifications such as `ℤ ⧸ (p) ≃+* ZMod p`.
-/

section

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {W' : Affine R}

instance instDecidableEquationOfDecidableEq [DecidableEq R] (x y : R) :
    Decidable (W'.Equation x y) :=
  decidable_of_iff _ (W'.equation_iff x y).symm

instance instDecidableNonsingularOfDecidableEq [DecidableEq R] (x y : R) :
    Decidable (W'.Nonsingular x y) :=
  decidable_of_iff _ (W'.nonsingular_iff x y).symm

instance instFinitePoint [Finite R] : Finite W'.Point :=
  .of_equiv (Option {xy : R × R // W'.Nonsingular xy.1 xy.2}) (nonsingularPointEquiv W').symm

instance instFintypePointOfDecidableEq [Fintype R] [DecidableEq R] : Fintype W'.Point :=
  .ofEquiv (Option {xy : R × R // W'.Nonsingular xy.1 xy.2}) (nonsingularPointEquiv W').symm

section PointMap

variable {K : Type*} [Field K] (W : Affine K)



variable [DecidableEq K]

/-- Transport of points along an equality of Weierstrass curves. -/
def Point.congr {W₁ W₂ : Affine K} (h : W₁ = W₂) : W₁.Point ≃+ W₂.Point := by
  subst h
  exact AddEquiv.refl _





variable (L : Type*) [Field L] [Algebra K L] [DecidableEq L]











end PointMap

namespace Point

variable {S F K : Type*} [CommRing S] [Field F] [Field K] [DecidableEq F] [DecidableEq K]
  [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] (σ : F ≃ₐ[S] K)

/-- The group isomorphism on nonsingular points induced by an algebra isomorphism
`σ : F ≃ₐ[S] K`, where `W` is defined over a subring of a ring `S`, and `F` and `K` are field
extensions of `S`; the equiv version of `WeierstrassCurve.Affine.Point.map`. -/
noncomputable def mapEquiv : (W'⁄F).Point ≃+ (W'⁄K).Point where
  toFun := map (σ : F →ₐ[S] K)
  invFun := map (σ.symm : K →ₐ[S] F)
  map_add' := map_add _
  left_inv P := by
    cases P with
    | zero => rfl
    | some x y h =>
        rw [map_some, map_some, Point.some.injEq]
        exact ⟨σ.symm_apply_apply x, σ.symm_apply_apply y⟩
  right_inv P := by
    cases P with
    | zero => rfl
    | some x y h =>
        rw [map_some, map_some, Point.some.injEq]
        exact ⟨σ.apply_symm_apply x, σ.apply_symm_apply y⟩

@[simp] lemma coe_mapEquiv : ⇑(mapEquiv (W' := W') σ) = ⇑(map (W' := W') (σ : F →ₐ[S] K)) :=
  rfl

end Point

end WeierstrassCurve.Affine

end

end


/- Source module: MazurTransfer.FinitePointReduction. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


open scoped WeierstrassCurve.Affine
namespace MazurTransfer

/-- Boundary: identify a finite rational point group with its full torsion
subgroup. Downstream consumers: the X_1(14), X_1(15), and X_0(21) point counts. -/
noncomputable def finitePointTorsionEquiv (E : WeierstrassCurve ℚ)
    [Finite (E⁄ℚ).Point] : (E⁄ℚ).Point ≃+ MazurCampaign.RationalTorsion E :=
  (AddEquiv.ofBijective (AddCommGroup.torsion (E⁄ℚ).Point).subtype
    ⟨Subtype.val_injective, fun P => ⟨⟨P, isOfFinAddOrder_of_finite P⟩, rfl⟩⟩).symm

lemma finite_point_card_dvd (W : WeierstrassCurve ℤ)
    (p : ℕ) [Fact p.Prime]
    [(W.map (Int.castRingHom ℚ)).IsElliptic]
    [Finite ((W.map (Int.castRingHom ℚ))⁄ℚ).Point]
    (hp : 2 < p) (hgood : ¬ (p : ℤ) ∣ W.Δ) :
    Nat.card ((W.map (Int.castRingHom ℚ))⁄ℚ).Point ∣
      Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point := by
  rw [Nat.card_congr (finitePointTorsionEquiv (W.map (Int.castRingHom ℚ))).toEquiv]
  exact (MazurCampaign.good_reduction_card_bound W p hp hgood).2

lemma finite_toAffine_card_dvd (W : WeierstrassCurve ℤ)
    (p : ℕ) [Fact p.Prime]
    [(W.map (Int.castRingHom ℚ)).IsElliptic]
    [Finite (W.map (Int.castRingHom ℚ)).toAffine.Point]
    (hp : 2 < p) (hgood : ¬ (p : ℤ) ∣ W.Δ) :
    Nat.card (W.map (Int.castRingHom ℚ)).toAffine.Point ∣
      Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point := by
  let E := W.map (Int.castRingHom ℚ)
  let e : (E⁄ℚ).Point ≃+ E.toAffine.Point :=
    WeierstrassCurve.Affine.Point.congr (by
      ext <;> simp [E, WeierstrassCurve.Affine.baseChange, WeierstrassCurve.map])
  letI : Finite (E⁄ℚ).Point := Finite.of_equiv E.toAffine.Point e.symm.toEquiv
  rw [← Nat.card_congr e.toEquiv]
  exact finite_point_card_dvd W p hp hgood

end MazurTransfer
#print axioms MazurTransfer.finite_point_card_dvd

end


/- Source module: MazurTorsion.NumberTheory.XOneFifteenDescent. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Two-isogeny descent for `X₁(15)`

The genus-one equation

`s² + s t + s = t³ + t²`

is carried by

`U = 4(t+1)`, `V = 4(2s+t+1)`

to the Weierstrass equation

`V² = U(U² - 7U + 16)`.

The associated two-isogenous curve is

`W² = Z(Z² + 14Z - 15)`.

On the original curve, positivity and a gcd-divides-`16` calculation leave
the squareclasses `1` and `2`; the latter is excluded by a primitive
quartic modulo sixteen.  On the dual curve, the eight initial squareclasses
are `±1`, `±3`, `±5`, and `±15`.  Four primitive quartic obstructions leave
the visible classes `1`, `-15`, `5`, and `-3`.

An explicit reverse-doubling calculation handles the first two dual
classes.  Translation by the visible point `(4,4)` exchanges the remaining
two with the first two.  Consequently the rational point group has at most
two cosets modulo doubling.  Naïve-height descent supplies finite
generation, and the exact rational two-torsion cardinality then gives
Mordell--Weil rank zero and finiteness.
-/

namespace MazurTorsion.XOneFifteen

/-- The short Weierstrass model obtained from the standard affine model of
`X₁(15)`. -/
def curve : WeierstrassCurve ℚ :=
  ⟨0, -7, 0, 16, 0⟩

/-- The curve two-isogenous to `curve`. -/
def dualCurve : WeierstrassCurve ℚ :=
  ⟨0, 14, 0, -15, 0⟩

private instance curve_isElliptic : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private instance dualCurve_isElliptic : dualCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [dualCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The affine modular equation is exactly the displayed Weierstrass
equation after the denominator-safe integral change of variables. -/
theorem modular_equation_iff_curve_equation (s t : ℚ) :
    s ^ 2 + s * t + s = t ^ 3 + t ^ 2 ↔
      (4 * (2 * s + t + 1)) ^ 2 =
        (4 * (t + 1)) *
          ((4 * (t + 1)) ^ 2 - 7 * (4 * (t + 1)) + 16) := by
  constructor
  · intro h
    linear_combination 64 * h
  · intro h
    linear_combination (1 / 64 : ℚ) * h

/-- Forward form of the integral change of variables from the affine
`X₁(15)` equation to `curve`. -/
theorem to_curve_equation
    {s t : ℚ} (h : s ^ 2 + s * t + s = t ^ 3 + t ^ 2) :
    (4 * (2 * s + t + 1)) ^ 2 =
      (4 * (t + 1)) *
        ((4 * (t + 1)) ^ 2 - 7 * (4 * (t + 1)) + 16) :=
  (modular_equation_iff_curve_equation s t).mp h

private abbrev redTwo : ZMod 16 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 16) (ZMod 2)

private lemma curve_two_mod_sixteen_obstruction :
    ∀ m n w : ZMod 16,
      (redTwo m ≠ 0 ∨ redTwo n ≠ 0) →
        w ^ 2 ≠
          2 * m ^ 4 - 7 * m ^ 2 * n ^ 2 + 8 * n ^ 4 := by
  decide

private lemma dual_neg_one_mod_sixteen_obstruction :
    ∀ m n w : ZMod 16,
      (redTwo m ≠ 0 ∨ redTwo n ≠ 0) →
        w ^ 2 ≠
          -m ^ 4 + 14 * m ^ 2 * n ^ 2 + 15 * n ^ 4 := by
  decide

private lemma dual_three_mod_sixteen_obstruction :
    ∀ m n w : ZMod 16,
      (redTwo m ≠ 0 ∨ redTwo n ≠ 0) →
        w ^ 2 ≠
          3 * m ^ 4 + 14 * m ^ 2 * n ^ 2 - 5 * n ^ 4 := by
  decide

private lemma dual_neg_five_mod_sixteen_obstruction :
    ∀ m n w : ZMod 16,
      (redTwo m ≠ 0 ∨ redTwo n ≠ 0) →
        w ^ 2 ≠
          -5 * m ^ 4 + 14 * m ^ 2 * n ^ 2 + 3 * n ^ 4 := by
  decide

private lemma dual_fifteen_mod_sixteen_obstruction :
    ∀ m n w : ZMod 16,
      (redTwo m ≠ 0 ∨ redTwo n ≠ 0) →
        w ^ 2 ≠
          15 * m ^ 4 + 14 * m ^ 2 * n ^ 2 - n ^ 4 := by
  decide

private lemma primitive_not_both_even
    {m n : ℤ} (hcoprime : IsCoprime m n) :
    redTwo (m : ZMod 16) ≠ 0 ∨ redTwo (n : ZMod 16) ≠ 0 := by
  by_contra hboth
  simp only [not_or, not_not] at hboth
  have hmeven : Even m := by
    rw [← ZMod.intCast_eq_zero_iff_even]
    simpa [redTwo] using hboth.1
  have hneven : Even n := by
    rw [← ZMod.intCast_eq_zero_iff_even]
    simpa [redTwo] using hboth.2
  have hunit : IsUnit (2 : ℤ) :=
    hcoprime.isUnit_of_dvd'
      (even_iff_two_dvd.mp hmeven) (even_iff_two_dvd.mp hneven)
  norm_num [Int.isUnit_iff] at hunit

/-- The primitive quartic attached to squareclass `2` on `curve` has no
integer point. -/
theorem no_curve_two_class
    (m n w : ℤ) (hcoprime : IsCoprime m n) :
    w ^ 2 ≠ 2 * m ^ 4 - 7 * m ^ 2 * n ^ 2 + 8 * n ^ 4 := by
  intro h
  apply curve_two_mod_sixteen_obstruction
    (m : ZMod 16) (n : ZMod 16) (w : ZMod 16)
    (primitive_not_both_even hcoprime)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) h

/-- The primitive quartic attached to squareclass `-1` on `dualCurve` has
no integer point. -/
theorem no_dual_neg_one_class
    (m n w : ℤ) (hcoprime : IsCoprime m n) :
    w ^ 2 ≠ -m ^ 4 + 14 * m ^ 2 * n ^ 2 + 15 * n ^ 4 := by
  intro h
  apply dual_neg_one_mod_sixteen_obstruction
    (m : ZMod 16) (n : ZMod 16) (w : ZMod 16)
    (primitive_not_both_even hcoprime)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) h

/-- The primitive quartic attached to squareclass `3` on `dualCurve` has
no integer point. -/
theorem no_dual_three_class
    (m n w : ℤ) (hcoprime : IsCoprime m n) :
    w ^ 2 ≠ 3 * m ^ 4 + 14 * m ^ 2 * n ^ 2 - 5 * n ^ 4 := by
  intro h
  apply dual_three_mod_sixteen_obstruction
    (m : ZMod 16) (n : ZMod 16) (w : ZMod 16)
    (primitive_not_both_even hcoprime)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) h

/-- The primitive quartic attached to squareclass `-5` on `dualCurve` has
no integer point. -/
theorem no_dual_neg_five_class
    (m n w : ℤ) (hcoprime : IsCoprime m n) :
    w ^ 2 ≠ -5 * m ^ 4 + 14 * m ^ 2 * n ^ 2 + 3 * n ^ 4 := by
  intro h
  apply dual_neg_five_mod_sixteen_obstruction
    (m : ZMod 16) (n : ZMod 16) (w : ZMod 16)
    (primitive_not_both_even hcoprime)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) h

/-- The primitive quartic attached to squareclass `15` on `dualCurve` has
no integer point. -/
theorem no_dual_fifteen_class
    (m n w : ℤ) (hcoprime : IsCoprime m n) :
    w ^ 2 ≠ 15 * m ^ 4 + 14 * m ^ 2 * n ^ 2 - n ^ 4 := by
  intro h
  apply dual_fifteen_mod_sixteen_obstruction
    (m : ZMod 16) (n : ZMod 16) (w : ZMod 16)
    (primitive_not_both_even hcoprime)
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) h

private lemma no_quartic_rat_of_no_int
    (a b c : ℤ)
    (hno :
      ∀ m n w : ℤ, IsCoprime m n →
        w ^ 2 ≠ a * m ^ 4 + b * m ^ 2 * n ^ 2 + c * n ^ 4)
    (z q : ℚ) :
    q ^ 2 ≠ (a : ℚ) * z ^ 4 + (b : ℚ) * z ^ 2 + c := by
  intro h
  let m : ℤ := z.num
  let n : ℤ := z.den
  have hn : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast z.den_ne_zero
  have hz : z = (m : ℚ) / n :=
    z.num_div_den.symm
  have hscaled :
      (q * n ^ 2) ^ 2 =
        (((a * m ^ 4 + b * m ^ 2 * n ^ 2 + c * n ^ 4 : ℤ) : ℚ)) := by
    rw [hz] at h
    field_simp [hn] at h
    calc
      (q * n ^ 2) ^ 2 = q ^ 2 * n ^ 4 := by ring
      _ = (a : ℚ) * (m : ℚ) ^ 4 +
          (b : ℚ) * (m : ℚ) ^ 2 * n ^ 2 +
          (c : ℚ) * n ^ 4 := by nlinarith [h]
      _ =
          (((a * m ^ 4 + b * m ^ 2 * n ^ 2 + c * n ^ 4 : ℤ) : ℚ)) := by
        push_cast
        ring
  have hsquare :
      IsSquare
        (((a * m ^ 4 + b * m ^ 2 * n ^ 2 + c * n ^ 4 : ℤ) : ℚ)) :=
    ⟨q * n ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨w, hw⟩ := Rat.isSquare_intCast_iff.mp hsquare
  exact hno m n w
    (by simpa [m, n] using Rat.isCoprime_num_den z)
    (by simpa [pow_two] using hw.symm)

/-- Rational denominator-cleared form of `no_curve_two_class`. -/
theorem no_curve_two_class_rat (z q : ℚ) :
    q ^ 2 ≠ 2 * z ^ 4 - 7 * z ^ 2 + 8 := by
  convert
    no_quartic_rat_of_no_int 2 (-7) 8
      (fun m n w h ↦ by
        convert no_curve_two_class m n w h using 1
        all_goals ring) z q
      using 1
  all_goals ring

/-- Rational denominator-cleared form of `no_dual_neg_one_class`. -/
theorem no_dual_neg_one_class_rat (z q : ℚ) :
    q ^ 2 ≠ -z ^ 4 + 14 * z ^ 2 + 15 := by
  convert
    no_quartic_rat_of_no_int (-1) 14 15
      (fun m n w h ↦ by
        convert no_dual_neg_one_class m n w h using 1
        all_goals ring) z q
      using 1
  all_goals ring

/-- Rational denominator-cleared form of `no_dual_three_class`. -/
theorem no_dual_three_class_rat (z q : ℚ) :
    q ^ 2 ≠ 3 * z ^ 4 + 14 * z ^ 2 - 5 := by
  convert
    no_quartic_rat_of_no_int 3 14 (-5)
      (fun m n w h ↦ by
        convert no_dual_three_class m n w h using 1
        all_goals ring) z q
      using 1
  all_goals ring

/-- Rational denominator-cleared form of `no_dual_neg_five_class`. -/
theorem no_dual_neg_five_class_rat (z q : ℚ) :
    q ^ 2 ≠ -5 * z ^ 4 + 14 * z ^ 2 + 3 := by
  simpa using
    no_quartic_rat_of_no_int (-5) 14 3 no_dual_neg_five_class z q

/-- Rational denominator-cleared form of `no_dual_fifteen_class`. -/
theorem no_dual_fifteen_class_rat (z q : ℚ) :
    q ^ 2 ≠ 15 * z ^ 4 + 14 * z ^ 2 - 1 := by
  convert
    no_quartic_rat_of_no_int 15 14 (-1)
      (fun m n w h ↦ by
        convert no_dual_fifteen_class m n w h using 1
        all_goals ring) z q
      using 1
  all_goals ring

private lemma common_divisor_dual_dvd_fifteen
    {m n d : ℤ} (hcoprime : IsCoprime m n)
    (hA : d ∣ m * n)
    (hB : d ∣ m ^ 2 + 14 * m * n - 15 * n ^ 2) :
    d ∣ 15 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hm3 : d ∣ m ^ 3 := by
    refine ⟨m * b - (14 * m - 15 * n) * a, ?_⟩
    linear_combination m * hb - (14 * m - 15 * n) * ha
  have h15n3 : d ∣ 15 * n ^ 3 := by
    refine ⟨(m + 14 * n) * a - n * b, ?_⟩
    linear_combination (m + 14 * n) * ha - n * hb
  have hcoprimePowers : IsCoprime (m ^ 3) (n ^ 3) :=
    hcoprime.pow
  have hcoprimeDN : IsCoprime d (n ^ 3) :=
    hcoprimePowers.of_isCoprime_of_dvd_left hm3
  exact hcoprimeDN.dvd_of_dvd_mul_right
    (by simpa [mul_comm] using h15n3)

private lemma squareclass_of_gcd_dvd_fifteen
    {A B C : ℤ} (hA0 : A ≠ 0) (hprod : A * B = C ^ 2)
    (hgcd : GCDMonoid.gcd A B ∣ (15 : ℤ)) :
    ∃ z : ℤ,
      A = z ^ 2 ∨ A = -z ^ 2 ∨
        A = 3 * z ^ 2 ∨ A = -3 * z ^ 2 ∨
          A = 5 * z ^ 2 ∨ A = -5 * z ^ 2 ∨
            A = 15 * z ^ 2 ∨ A = -15 * z ^ 2 := by
  let g : ℤ := GCDMonoid.gcd A B
  have hgA : g ∣ A := GCDMonoid.gcd_dvd_left A B
  have hgB : g ∣ B := GCDMonoid.gcd_dvd_right A B
  have hg0 : g ≠ 0 := by
    intro hg
    rw [hg] at hgA
    exact hA0 (zero_dvd_iff.mp hgA)
  have hgpos : 0 < g :=
    lt_of_le_of_ne (Int.gcd_nonneg A B) (Ne.symm hg0)
  have hgC : g ∣ C := by
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd
      (R := ℤ) (n := 2) (by norm_num)).mp
    simpa [pow_two, hprod] using mul_dvd_mul hgA hgB
  let a : ℤ := A / g
  let b : ℤ := B / g
  let c : ℤ := C / g
  have hga : g * a = A :=
    EuclideanDomain.mul_div_cancel' hg0 hgA
  have hgb : g * b = B :=
    EuclideanDomain.mul_div_cancel' hg0 hgB
  have hgc : g * c = C :=
    EuclideanDomain.mul_div_cancel' hg0 hgC
  have hab : a * b = c ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
    calc
      g ^ 2 * (a * b) = A * B := by rw [← hga, ← hgb]; ring
      _ = C ^ 2 := hprod
      _ = g ^ 2 * c ^ 2 := by rw [← hgc]; ring
  have habcoprime : IsCoprime a b :=
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0
  have hgabs : g.natAbs ∣ 15 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hgcd
  have hgleNat : g.natAbs ≤ 15 :=
    Nat.le_of_dvd (by norm_num) hgabs
  have hgle : g ≤ 15 := by
    have hgleCast : (g.natAbs : ℤ) ≤ 15 := by
      exact_mod_cast hgleNat
    simpa [Int.natCast_natAbs, abs_of_pos hgpos] using hgleCast
  have hgvals : g = 1 ∨ g = 3 ∨ g = 5 ∨ g = 15 := by
    interval_cases g <;> norm_num at hgabs
    all_goals simp
  obtain ⟨z, hz | hz⟩ := Int.sq_of_isCoprime habcoprime hab
  · have hAz : A = g * z ^ 2 := by rw [← hga, hz]
    rcases hgvals with hg | hg | hg | hg
    · rw [hg] at hAz
      exact ⟨z, Or.inl (by simpa using hAz)⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inl (by simpa using hAz)))⟩
    · rw [hg] at hAz
      exact
        ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl (by simpa using hAz)))))⟩
    · rw [hg] at hAz
      exact
        ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl (by simpa using hAz)))))))⟩
  · have hAz : A = -(g * z ^ 2) := by rw [← hga, hz]; ring
    rcases hgvals with hg | hg | hg | hg
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inl (by nlinarith [hAz]))⟩
    · rw [hg] at hAz
      exact
        ⟨z, Or.inr (Or.inr (Or.inr
          (Or.inl (by nlinarith [hAz]))))⟩
    · rw [hg] at hAz
      exact
        ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl (by nlinarith [hAz]))))))⟩
    · rw [hg] at hAz
      exact
        ⟨z, Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (by nlinarith [hAz])))))))⟩

/-- On the dual curve, every nonzero rational abscissa initially has one
of the eight squareclasses `±1`, `±3`, `±5`, and `±15`. -/
theorem dual_abscissa_squareclass
    {X Y : ℚ} (hX0 : X ≠ 0)
    (hcurve : Y ^ 2 = X * (X ^ 2 + 14 * X - 15)) :
    (∃ z : ℚ, X = z ^ 2) ∨
      (∃ z : ℚ, X = -z ^ 2) ∨
      (∃ z : ℚ, X = 3 * z ^ 2) ∨
      (∃ z : ℚ, X = -3 * z ^ 2) ∨
      (∃ z : ℚ, X = 5 * z ^ 2) ∨
      (∃ z : ℚ, X = -5 * z ^ 2) ∨
      (∃ z : ℚ, X = 15 * z ^ 2) ∨
      (∃ z : ℚ, X = -15 * z ^ 2) := by
  let m : ℤ := X.num
  let n : ℤ := X.den
  let A : ℤ := m * n
  let B : ℤ := m ^ 2 + 14 * m * n - 15 * n ^ 2
  have hn : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast X.den_ne_zero
  have hX : X = (m : ℚ) / n :=
    X.num_div_den.symm
  have hscaled :
      (Y * n ^ 2) ^ 2 = (((A * B : ℤ) : ℚ)) := by
    rw [hX] at hcurve
    field_simp [hn] at hcurve
    calc
      (Y * n ^ 2) ^ 2 = Y ^ 2 * n ^ 4 := by ring
      _ = (m : ℚ) * n *
          ((m : ℚ) ^ 2 + 14 * m * n - 15 * n ^ 2) := by
        linear_combination n * hcurve
      _ = (((A * B : ℤ) : ℚ)) := by
        dsimp [A, B]
        push_cast
        ring
  have hsquare : IsSquare (((A * B : ℤ) : ℚ)) :=
    ⟨Y * n ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨C, hC⟩ := Rat.isSquare_intCast_iff.mp hsquare
  have hprod : A * B = C ^ 2 := by
    simpa [pow_two] using hC
  have hA0 : A ≠ 0 := by
    apply mul_ne_zero
    · dsimp [m]
      exact Rat.num_ne_zero.mpr hX0
    · dsimp [n]
      exact_mod_cast X.den_ne_zero
  have hmnCoprime : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den X
  have hgcd : GCDMonoid.gcd A B ∣ (15 : ℤ) :=
    common_divisor_dual_dvd_fifteen hmnCoprime
      (GCDMonoid.gcd_dvd_left A B) (GCDMonoid.gcd_dvd_right A B)
  have lift_squareclass :
      ∀ {d z : ℤ}, A = d * z ^ 2 →
        X = (d : ℚ) * (((z : ℚ) / n) ^ 2) := by
    intro d z hd
    rw [hX]
    simp only [A] at hd
    field_simp [hn]
    exact_mod_cast hd
  obtain ⟨z, hA | hA | hA | hA | hA | hA | hA | hA⟩ :=
    squareclass_of_gcd_dvd_fifteen hA0 hprod hgcd
  · left
    refine ⟨(z : ℚ) / n, ?_⟩
    simpa using lift_squareclass (d := 1) (by simpa using hA)
  · right; left
    refine ⟨(z : ℚ) / n, ?_⟩
    simpa using lift_squareclass (d := -1) (by nlinarith [hA])
  · right; right; left
    exact ⟨(z : ℚ) / n, lift_squareclass hA⟩
  · right; right; right; left
    refine ⟨(z : ℚ) / n, ?_⟩
    simpa using lift_squareclass (d := -3) (by nlinarith [hA])
  · right; right; right; right; left
    exact ⟨(z : ℚ) / n, lift_squareclass hA⟩
  · right; right; right; right; right; left
    refine ⟨(z : ℚ) / n, ?_⟩
    simpa using lift_squareclass (d := -5) (by nlinarith [hA])
  · right; right; right; right; right; right; left
    exact ⟨(z : ℚ) / n, lift_squareclass hA⟩
  · right; right; right; right; right; right; right
    refine ⟨(z : ℚ) / n, ?_⟩
    simpa using lift_squareclass (d := -15) (by nlinarith [hA])

/-- The four locally impossible dual squareclasses are removed.  Thus a
rational point on `dualCurve` has one of the four visible squareclasses
`1`, `-15`, `5`, and `-3`. -/
theorem dual_abscissa_visible_squareclasses
    {X Y : ℚ}
    (hcurve : Y ^ 2 = X * (X ^ 2 + 14 * X - 15)) :
    IsSquare X ∨
      (∃ z : ℚ, X = -15 * z ^ 2) ∨
      (∃ z : ℚ, X = 5 * z ^ 2) ∨
      (∃ z : ℚ, X = -3 * z ^ 2) := by
  rcases eq_or_ne X 0 with rfl | hX0
  · exact Or.inl IsSquare.zero
  rcases dual_abscissa_squareclass hX0 hcurve with
      ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩ |
      ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩
  · left
    exact ⟨z, by simpa [pow_two] using hz⟩
  · have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
      exact hX0 hz
    exfalso
    apply no_dual_neg_one_class_rat z (Y / z)
    rw [div_pow]
    field_simp [hz0]
    rw [hz] at hcurve
    nlinarith [hcurve]
  · have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
      exact hX0 hz
    exfalso
    apply no_dual_three_class_rat z (Y / (3 * z))
    rw [div_pow]
    field_simp [hz0]
    rw [hz] at hcurve
    nlinarith [hcurve]
  · right; right; right
    exact ⟨z, hz⟩
  · right; right; left
    exact ⟨z, hz⟩
  · have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
      exact hX0 hz
    exfalso
    apply no_dual_neg_five_class_rat z (Y / (5 * z))
    rw [div_pow]
    field_simp [hz0]
    rw [hz] at hcurve
    nlinarith [hcurve]
  · have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
      exact hX0 hz
    exfalso
    apply no_dual_fifteen_class_rat z (Y / (15 * z))
    rw [div_pow]
    field_simp [hz0]
    rw [hz] at hcurve
    nlinarith [hcurve]
  · right; left
    exact ⟨z, hz⟩

private lemma common_divisor_curve_dvd_sixteen
    {m n d : ℤ} (hcoprime : IsCoprime m n)
    (hA : d ∣ m * n)
    (hB : d ∣ m ^ 2 - 7 * m * n + 16 * n ^ 2) :
    d ∣ 16 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hm3 : d ∣ m ^ 3 := by
    refine ⟨m * b - (-7 * m + 16 * n) * a, ?_⟩
    linear_combination m * hb - (-7 * m + 16 * n) * ha
  have h16n3 : d ∣ 16 * n ^ 3 := by
    refine ⟨n * b - (m - 7 * n) * a, ?_⟩
    linear_combination n * hb - (m - 7 * n) * ha
  have hcoprimePowers : IsCoprime (m ^ 3) (n ^ 3) :=
    hcoprime.pow
  have hcoprimeDN : IsCoprime d (n ^ 3) :=
    hcoprimePowers.of_isCoprime_of_dvd_left hm3
  exact hcoprimeDN.dvd_of_dvd_mul_right
    (by simpa [mul_comm] using h16n3)

private lemma positive_squareclass_of_gcd_dvd_sixteen
    {A B C : ℤ} (hApos : 0 < A) (hprod : A * B = C ^ 2)
    (hgcd : GCDMonoid.gcd A B ∣ (16 : ℤ)) :
    ∃ z : ℤ, A = z ^ 2 ∨ A = 2 * z ^ 2 := by
  let g : ℤ := GCDMonoid.gcd A B
  have hgA : g ∣ A := GCDMonoid.gcd_dvd_left A B
  have hgB : g ∣ B := GCDMonoid.gcd_dvd_right A B
  have hg0 : g ≠ 0 := by
    intro hg
    rw [hg] at hgA
    exact hApos.ne' (zero_dvd_iff.mp hgA)
  have hgpos : 0 < g :=
    lt_of_le_of_ne (Int.gcd_nonneg A B) (Ne.symm hg0)
  have hgC : g ∣ C := by
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd
      (R := ℤ) (n := 2) (by norm_num)).mp
    simpa [pow_two, hprod] using mul_dvd_mul hgA hgB
  let a : ℤ := A / g
  let b : ℤ := B / g
  let c : ℤ := C / g
  have hga : g * a = A :=
    EuclideanDomain.mul_div_cancel' hg0 hgA
  have hgb : g * b = B :=
    EuclideanDomain.mul_div_cancel' hg0 hgB
  have hgc : g * c = C :=
    EuclideanDomain.mul_div_cancel' hg0 hgC
  have hab : a * b = c ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
    calc
      g ^ 2 * (a * b) = A * B := by rw [← hga, ← hgb]; ring
      _ = C ^ 2 := hprod
      _ = g ^ 2 * c ^ 2 := by rw [← hgc]; ring
  have habcoprime : IsCoprime a b :=
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0
  obtain ⟨z, hz | hz⟩ := Int.sq_of_isCoprime habcoprime hab
  · have hAz : A = g * z ^ 2 := by rw [← hga, hz]
    have hgabs : g.natAbs ∣ 16 := by
      simpa using Int.natAbs_dvd_natAbs.mpr hgcd
    have hgleNat : g.natAbs ≤ 16 :=
      Nat.le_of_dvd (by norm_num) hgabs
    have hgle : g ≤ 16 := by
      have hgleCast : (g.natAbs : ℤ) ≤ 16 := by
        exact_mod_cast hgleNat
      simpa [Int.natCast_natAbs, abs_of_pos hgpos] using hgleCast
    have hgvals :
        g = 1 ∨ g = 2 ∨ g = 4 ∨ g = 8 ∨ g = 16 := by
      interval_cases g <;> norm_num at hgabs
      all_goals simp
    rcases hgvals with hg | hg | hg | hg | hg
    · rw [hg] at hAz
      exact ⟨z, Or.inl (by simpa using hAz)⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (by simpa using hAz)⟩
    · rw [hg] at hAz
      exact ⟨2 * z, Or.inl (by nlinarith [hAz])⟩
    · rw [hg] at hAz
      exact ⟨2 * z, Or.inr (by nlinarith [hAz])⟩
    · rw [hg] at hAz
      exact ⟨4 * z, Or.inl (by nlinarith [hAz])⟩
  · have haNonpos : a ≤ 0 := by nlinarith [sq_nonneg z]
    have hAnonpos : A ≤ 0 := by
      rw [← hga]
      exact mul_nonpos_of_nonneg_of_nonpos hgpos.le haNonpos
    exact (not_lt_of_ge hAnonpos hApos).elim

/-- Before the local obstruction is applied, every nonzero abscissa on
`curve` has squareclass `1` or `2`. -/
theorem curve_abscissa_isSquare_or_two
    {U V : ℚ} (hU0 : U ≠ 0)
    (hcurve : V ^ 2 = U * (U ^ 2 - 7 * U + 16)) :
    IsSquare U ∨ ∃ z : ℚ, U = 2 * z ^ 2 := by
  have hquadratic : 0 < U ^ 2 - 7 * U + 16 := by
    nlinarith [sq_nonneg (2 * U - 7)]
  have hUpos : 0 < U := by
    by_contra! hUnonpos
    have hUneg : U < 0 := lt_of_le_of_ne hUnonpos hU0
    have hnegative : U * (U ^ 2 - 7 * U + 16) < 0 :=
      mul_neg_of_neg_of_pos hUneg hquadratic
    rw [← hcurve] at hnegative
    exact (not_lt_of_ge (sq_nonneg V)) hnegative
  let m : ℤ := U.num
  let n : ℤ := U.den
  let A : ℤ := m * n
  let B : ℤ := m ^ 2 - 7 * m * n + 16 * n ^ 2
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast U.den_pos
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hU : U = (m : ℚ) / n := U.num_div_den.symm
  have hscaled :
      (V * n ^ 2) ^ 2 = (((A * B : ℤ) : ℚ)) := by
    rw [hU] at hcurve
    field_simp [hn0] at hcurve
    calc
      (V * n ^ 2) ^ 2 = V ^ 2 * n ^ 4 := by ring
      _ = (m : ℚ) * n *
          ((m : ℚ) ^ 2 - 7 * m * n + 16 * n ^ 2) := by
        linear_combination n * hcurve
      _ = (((A * B : ℤ) : ℚ)) := by
        dsimp [A, B]
        push_cast
        ring
  have hsquareRat : IsSquare (((A * B : ℤ) : ℚ)) :=
    ⟨V * n ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨C, hC⟩ := Rat.isSquare_intCast_iff.mp hsquareRat
  have hprod : A * B = C ^ 2 := by
    simpa [pow_two] using hC
  have hApos : 0 < A := by
    have hmpos : 0 < m := by
      dsimp [m]
      exact Rat.num_pos.mpr hUpos
    exact mul_pos hmpos hnpos
  have hmnCoprime : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den U
  have hgcd : GCDMonoid.gcd A B ∣ (16 : ℤ) :=
    common_divisor_curve_dvd_sixteen hmnCoprime
      (GCDMonoid.gcd_dvd_left A B) (GCDMonoid.gcd_dvd_right A B)
  obtain ⟨z, hA | hA⟩ :=
    positive_squareclass_of_gcd_dvd_sixteen hApos hprod hgcd
  · left
    refine ⟨(z : ℚ) / n, ?_⟩
    rw [hU]
    simp only [A] at hA
    field_simp [hn0]
    exact_mod_cast hA
  · right
    refine ⟨(z : ℚ) / n, ?_⟩
    rw [hU]
    simp only [A] at hA
    field_simp [hn0]
    exact_mod_cast hA

/-- The nontrivial possible squareclass on the original curve is locally
impossible.  Consequently every rational abscissa on `curve` is a square. -/
theorem curve_abscissa_isSquare
    {U V : ℚ}
    (hcurve : V ^ 2 = U * (U ^ 2 - 7 * U + 16)) :
    IsSquare U := by
  rcases eq_or_ne U 0 with rfl | hU0
  · exact IsSquare.zero
  rcases curve_abscissa_isSquare_or_two hU0 hcurve with
      hUsquare | ⟨z, hU⟩
  · exact hUsquare
  · have hz0 : z ≠ 0 := by
      intro hz
      rw [hz] at hU
      norm_num at hU
      exact hU0 hU
    exfalso
    apply no_curve_two_class_rat z (V / (2 * z))
    rw [div_pow]
    field_simp [hz0]
    rw [hU] at hcurve
    nlinarith [hcurve]

private lemma y_linear_of_reverse_definition
    {X Y q v : ℚ} (hq0 : q ≠ 0)
    (hv : v = 7 / 2 + X / 2 - Y / (2 * q)) :
    Y = q * (X + 7 - 2 * v) := by
  field_simp [hq0] at hv
  linear_combination hv

private lemma y_formula_of_reverse_linear
    {X Y q v : ℚ} (hv0 : v ≠ 0)
    (hlinear : Y = q * (X + 7 - 2 * v))
    (hXv : X * v = v ^ 2 - 7 * v + 16) :
    Y = -q * (v ^ 2 - 16) / v := by
  rw [hlinear]
  field_simp [hv0]
  linear_combination q * hXv

private lemma y_formula_squared
    {Y q v : ℚ} (hv0 : v ≠ 0)
    (hY : Y = -q * (v ^ 2 - 16) / v) :
    Y ^ 2 * v ^ 2 = q ^ 2 * (v ^ 2 - 16) ^ 2 := by
  rw [hY]
  field_simp [hv0]

private theorem double_of_chosen_square_dual_abscissa
    {U V s τ X q : ℚ} (hU0 : U ≠ 0)
    (hP : curve.toAffine.Nonsingular U V)
    (hU : U = s ^ 2)
    (hτ : τ ^ 2 = U ^ 2 - 7 * U + 16)
    (hXdef : X = 2 * U - 7 - 2 * τ)
    (hX0 : X ≠ 0) (hXq : X = q ^ 2) :
    ∃ Q : curve.toAffine.Point,
      (2 : ℕ) • Q =
        WeierstrassCurve.Affine.Point.some U V hP := by
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at hU
    norm_num at hU
    exact hU0 hU
  let Y : ℚ := 2 * s * X
  have hfactor :
      X ^ 2 + 14 * X - 15 = 4 * U * X := by
    rw [hXdef]
    nlinarith [hτ]
  have hdual :
      Y ^ 2 = X * (X ^ 2 + 14 * X - 15) := by
    rw [hfactor]
    dsimp [Y]
    rw [hU]
    ring
  have hq0 : q ≠ 0 := by
    intro hq
    rw [hq] at hXq
    norm_num at hXq
    exact hX0 hXq
  have hYq :
      (Y / q) ^ 2 = X ^ 2 + 14 * X - 15 := by
    rw [div_pow]
    field_simp [hq0]
    nlinarith [hdual, hXq]
  let v : ℚ := 7 / 2 + X / 2 - Y / (2 * q)
  let w : ℚ := q * v
  have hvdef : v = 7 / 2 + X / 2 - Y / (2 * q) := rfl
  have hwdef : w = q * v := rfl
  have hXv : X * v = v ^ 2 - 7 * v + 16 := by
    dsimp [v]
    field_simp [hq0] at hYq ⊢
    nlinarith [hYq, hXq]
  have hv0 : v ≠ 0 := by
    intro hv
    rw [hv] at hXv
    norm_num at hXv
  have hw0 : w ≠ 0 :=
    mul_ne_zero hq0 hv0
  have hcurveQ : w ^ 2 = v * (v ^ 2 - 7 * v + 16) := by
    rw [hwdef, ← hXv, hXq]
    ring
  have hQ : curve.toAffine.Nonsingular v w := by
    apply curve.toAffine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [curve]
    linear_combination hcurveQ
  have hwneneg : w ≠ -w := by
    intro h
    apply hw0
    linarith
  have hneg : w ≠ curve.toAffine.negY v w := by
    simp only [WeierstrassCurve.Affine.negY]
    norm_num [curve]
    exact hwneneg
  let Q : curve.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some v w hQ
  have hdouble :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne
      (h₁ := hQ) hneg
  have hslope :
      curve.toAffine.slope v v w w =
        (3 * v ^ 2 - 14 * v + 16) / (2 * w) := by
    simp [WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, curve, hwneneg]
    ring
  have haddX :
      curve.toAffine.addX v v
          (curve.toAffine.slope v v w w) =
        (v ^ 2 - 16) ^ 2 / (4 * w ^ 2) := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [curve]
    field_simp [hw0]
    rw [hcurveQ]
    ring
  have hYformula :
      Y = -q * (v ^ 2 - 16) / v :=
    y_formula_of_reverse_linear hv0
      (y_linear_of_reverse_definition hq0 hvdef) hXv
  have haddXeq :
      curve.toAffine.addX v v
          (curve.toAffine.slope v v w w) = U := by
    rw [haddX]
    have hYsq : Y ^ 2 = 4 * U * X ^ 2 := by
      dsimp [Y]
      rw [hU]
      ring
    have hYformulaCleared :
        Y ^ 2 * v ^ 2 =
          q ^ 2 * (v ^ 2 - 16) ^ 2 :=
      y_formula_squared hv0 hYformula
    have hcancel :
        q ^ 2 * (v ^ 2 - 16) ^ 2 =
          q ^ 2 * (4 * U * q ^ 2 * v ^ 2) := by
      calc
        q ^ 2 * (v ^ 2 - 16) ^ 2 =
            Y ^ 2 * v ^ 2 := hYformulaCleared.symm
        _ = q ^ 2 * (4 * U * q ^ 2 * v ^ 2) := by
          rw [hYsq, hXq]
          ring
    have htarget :
        (v ^ 2 - 16) ^ 2 = 4 * w ^ 2 * U := by
      have hcancelled :=
        mul_left_cancel₀ (pow_ne_zero 2 hq0) hcancel
      calc
        (v ^ 2 - 16) ^ 2 =
            4 * U * q ^ 2 * v ^ 2 := hcancelled
        _ = 4 * w ^ 2 * U := by rw [hwdef]; ring
    rw [htarget]
    field_simp [hw0]
  have hXcoord :
      Q + Q =
          WeierstrassCurve.Affine.Point.some U V hP ∨
        Q + Q =
          -WeierstrassCurve.Affine.Point.some U V hP := by
    rw [hdouble]
    apply WeierstrassCurve.Affine.Point.X_eq_iff.mp
    exact haddXeq
  rcases hXcoord with hQQ | hQQ
  · exact ⟨Q, by simpa [two_nsmul] using hQQ⟩
  · refine ⟨-Q, ?_⟩
    simp only [two_nsmul]
    calc
      -Q + -Q = -(Q + Q) := by rw [neg_add]
      _ = -(-WeierstrassCurve.Affine.Point.some U V hP) := by
        rw [hQQ]
      _ = WeierstrassCurve.Affine.Point.some U V hP := neg_neg _

private theorem double_of_direct_auxiliary_class
    {U V s τ X : ℚ} (hU0 : U ≠ 0)
    (hP : curve.toAffine.Nonsingular U V)
    (hU : U = s ^ 2)
    (hτ : τ ^ 2 = U ^ 2 - 7 * U + 16)
    (hXdef : X = 2 * U - 7 - 2 * τ)
    (hX0 : X ≠ 0)
    (hclass : IsSquare X ∨ ∃ z : ℚ, X = -15 * z ^ 2) :
    ∃ Q : curve.toAffine.Point,
      (2 : ℕ) • Q =
        WeierstrassCurve.Affine.Point.some U V hP := by
  rcases hclass with hXsquare | ⟨z, hz⟩
  · obtain ⟨q, hq⟩ := hXsquare
    exact
      double_of_chosen_square_dual_abscissa hU0 hP hU hτ hXdef hX0
        (by simpa [pow_two] using hq)
  · have hz0 : z ≠ 0 := by
      intro hz0
      rw [hz0] at hz
      norm_num at hz
      exact hX0 hz
    let X₁ : ℚ := 2 * U - 7 + 2 * τ
    have hprod : X * X₁ = -15 := by
      rw [hXdef]
      dsimp [X₁]
      nlinarith [hτ]
    have hX₁square : X₁ = (1 / z) ^ 2 := by
      rw [hz] at hprod
      field_simp [hz0]
      nlinarith [hprod]
    have hX₁0 : X₁ ≠ 0 := by
      rw [hX₁square]
      exact pow_ne_zero 2 (div_ne_zero (by norm_num) hz0)
    apply
      double_of_chosen_square_dual_abscissa hU0 hP hU
        (τ := -τ) (X := X₁) (q := 1 / z)
    · nlinarith [hτ]
    · dsimp [X₁]
      ring
    · exact hX₁0
    · exact hX₁square

/-- For a nonzero affine point, the explicit reverse-doubling construction
either succeeds, or produces one of the two exceptional auxiliary dual
squareclasses `5` and `-3`.  These are precisely the two cases exchanged
by translation by the visible order-four point `(4,4)`. -/
theorem doubling_or_exceptional_auxiliary_squareclass
    {U V : ℚ} (hU0 : U ≠ 0)
    (hP : curve.toAffine.Nonsingular U V) :
    (∃ Q : curve.toAffine.Point,
      (2 : ℕ) • Q =
        WeierstrassCurve.Affine.Point.some U V hP) ∨
      ∃ s t X z : ℚ,
        U = s ^ 2 ∧ t = V / s ∧
          X = 2 * U - 7 - 2 * t ∧
            (X = 5 * z ^ 2 ∨ X = -3 * z ^ 2) := by
  have hcurve : V ^ 2 = U * (U ^ 2 - 7 * U + 16) := by
    have heq := hP.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    norm_num [curve] at heq
    nlinarith
  obtain ⟨s, hs⟩ := curve_abscissa_isSquare hcurve
  have hU : U = s ^ 2 := by
    simpa [pow_two] using hs
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at hU
    norm_num at hU
    exact hU0 hU
  let t : ℚ := V / s
  have ht : t ^ 2 = U ^ 2 - 7 * U + 16 := by
    dsimp [t]
    rw [div_pow]
    field_simp [hs0]
    nlinarith [hcurve, hU]
  let X₀ : ℚ := 2 * U - 7 - 2 * t
  let X₁ : ℚ := 2 * U - 7 + 2 * t
  have hXprod : X₀ * X₁ = -15 := by
    dsimp [X₀, X₁]
    nlinarith [ht]
  have hX₀0 : X₀ ≠ 0 := by
    intro h
    rw [h] at hXprod
    norm_num at hXprod
  let Y₀ : ℚ := 2 * s * X₀
  have hdualFactor :
      X₀ ^ 2 + 14 * X₀ - 15 = 4 * U * X₀ := by
    dsimp [X₀]
    nlinarith [ht]
  have hdual :
      Y₀ ^ 2 = X₀ * (X₀ ^ 2 + 14 * X₀ - 15) := by
    rw [hdualFactor]
    dsimp [Y₀]
    rw [hU]
    ring
  rcases dual_abscissa_visible_squareclasses hdual with
      hXsquare | ⟨z, hz⟩ | ⟨z, hz⟩ | ⟨z, hz⟩
  · obtain ⟨q, hq⟩ := hXsquare
    left
    exact
      double_of_chosen_square_dual_abscissa hU0 hP hU ht rfl hX₀0
        (by simpa [pow_two] using hq)
  · have hz0 : z ≠ 0 := by
      intro hz0
      rw [hz0] at hz
      norm_num at hz
      exact hX₀0 hz
    have hX₁square : X₁ = (1 / z) ^ 2 := by
      rw [hz] at hXprod
      field_simp [hz0]
      nlinarith [hXprod]
    have hX₁0 : X₁ ≠ 0 := by
      rw [hX₁square]
      exact pow_ne_zero 2 (div_ne_zero (by norm_num) hz0)
    left
    apply
      double_of_chosen_square_dual_abscissa hU0 hP hU
        (τ := -t) (X := X₁) (q := 1 / z)
    · nlinarith [ht]
    · dsimp [X₁]
      ring
    · exact hX₁0
    · exact hX₁square
  · right
    exact ⟨s, t, X₀, z, hU, rfl, rfl, Or.inl hz⟩
  · right
    exact ⟨s, t, X₀, z, hU, rfl, rfl, Or.inr hz⟩

private lemma nonsingular_zero_zero :
    curve.toAffine.Nonsingular 0 0 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_four_four :
    curve.toAffine.Nonsingular 4 4 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_four_neg_four :
    curve.toAffine.Nonsingular 4 (-4) := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

/-- The rational two-torsion point `(0,0)`. -/
def T : curve.toAffine.Point :=
  .some 0 0 nonsingular_zero_zero

/-- The visible order-four point `(4,4)`. -/
def G : curve.toAffine.Point :=
  .some 4 4 nonsingular_four_four

private lemma double_G : (2 : ℕ) • G = T := by
  simp only [two_nsmul, G]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne
    (by norm_num [WeierstrassCurve.Affine.negY, curve])]
  rw [T]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · norm_num [WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, curve]
  · norm_num [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.addX,
      WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, curve]

private lemma double_T : (2 : ℕ) • T = 0 := by
  simp only [two_nsmul]
  rw [T]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY, curve]

private lemma four_G : (4 : ℕ) • G = 0 := by
  calc
    (4 : ℕ) • G = (2 : ℕ) • ((2 : ℕ) • G) := by
      norm_num [← mul_nsmul]
    _ = (2 : ℕ) • T := by rw [double_G]
    _ = 0 := double_T

private lemma translated_x_identity
    {U V s t : ℚ} (hU : U = s ^ 2) (hV : V = s * t)
    (ht : t ^ 2 = U ^ 2 - 7 * U + 16)
    (hUfour : U ≠ 4) :
    ((V + 4) / (U - 4)) ^ 2 + 7 - U - 4 =
      (2 * (t + s) / (U - 4)) ^ 2 := by
  rw [hU] at ht hUfour ⊢
  rw [hV]
  field_simp [hUfour]
  linear_combination (s ^ 2 - 4) * ht

private lemma translated_y_identity
    {U V s t : ℚ} (hU : U = s ^ 2) (hV : V = s * t)
    (hUfour : U ≠ 4) :
    -((V + 4) / (U - 4) *
          ((2 * (t + s) / (U - 4)) ^ 2 - U) + V) =
      (2 * (t + s) / (U - 4)) *
        (2 *
          (s * (U - 4) ^ 2 - (s * t + 4) * (t + s)) /
            (U - 4) ^ 2) := by
  rw [hU] at hUfour ⊢
  rw [hV]
  field_simp [hUfour]
  ring

private lemma translated_t_square
    {U s t : ℚ} (hU : U = s ^ 2)
    (ht : t ^ 2 = U ^ 2 - 7 * U + 16)
    (hUfour : U ≠ 4) :
    (2 *
        (s * (U - 4) ^ 2 - (s * t + 4) * (t + s)) /
          (U - 4) ^ 2) ^ 2 =
      (2 * (t + s) / (U - 4)) ^ 4 -
        7 * (2 * (t + s) / (U - 4)) ^ 2 + 16 := by
  rw [hU] at ht hUfour ⊢
  field_simp [hUfour]
  linear_combination
    -4 * (s ^ 2 - s - t - 4) * (s ^ 2 + s + t - 4) *
      (s ^ 2 - 4) * ht

private lemma translated_auxiliary_identity
    {U s t : ℚ} (hU : U = s ^ 2)
    (ht : t ^ 2 = U ^ 2 - 7 * U + 16)
    (hUfour : U ≠ 4) :
    2 * (2 * (t + s) / (U - 4)) ^ 2 - 7 -
        2 *
          (2 *
            (s * (U - 4) ^ 2 - (s * t + 4) * (t + s)) /
              (U - 4) ^ 2) =
      (s ^ 2 + 4 * t + 4) / (s - 2) ^ 2 := by
  have hsminus : s - 2 ≠ 0 := by
    intro hs
    apply hUfour
    rw [hU]
    nlinarith
  rw [hU] at ht hUfour ⊢
  field_simp [hUfour, hsminus]
  linear_combination 4 * (s + 2) * (s - 2) ^ 2 * ht

private lemma translated_auxiliary_product
    {U s t X₁ : ℚ} (hU : U = s ^ 2)
    (ht : t ^ 2 = U ^ 2 - 7 * U + 16)
    (hX₁ : X₁ = 2 * U - 7 + 2 * t) :
    (s ^ 2 + 4 * t + 4) * X₁ =
      5 * (t + s ^ 2 - 2) ^ 2 := by
  rw [hU] at ht hX₁
  rw [hX₁]
  nlinarith [ht]

private theorem exceptional_auxiliary_translate_double
    {U V s t z : ℚ}
    (hP : curve.toAffine.Nonsingular U V)
    (hU : U = s ^ 2) (hV : V = s * t)
    (ht : t ^ 2 = U ^ 2 - 7 * U + 16)
    (hUfour : U ≠ 4)
    (hcase :
      2 * U - 7 - 2 * t = 5 * z ^ 2 ∨
        2 * U - 7 - 2 * t = -3 * z ^ 2) :
    ∃ Q : curve.toAffine.Point,
      WeierstrassCurve.Affine.Point.some U V hP =
        G + (2 : ℕ) • Q := by
  let sr : ℚ := 2 * (t + s) / (U - 4)
  let tr : ℚ :=
    2 * (s * (U - 4) ^ 2 - (s * t + 4) * (t + s)) /
      (U - 4) ^ 2
  let ur : ℚ := sr ^ 2
  let vr : ℚ := sr * tr
  have htr : tr ^ 2 = ur ^ 2 - 7 * ur + 16 := by
    dsimp [tr, ur, sr]
    convert translated_t_square hU ht hUfour using 1
    all_goals ring
  have hcurveR : vr ^ 2 = ur * (ur ^ 2 - 7 * ur + 16) := by
    calc
      vr ^ 2 = ur * tr ^ 2 := by dsimp [vr, ur]; ring
      _ = ur * (ur ^ 2 - 7 * ur + 16) := by rw [htr]
  have hR : curve.toAffine.Nonsingular ur vr := by
    apply curve.toAffine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [curve]
    linear_combination hcurveR
  let R : curve.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some ur vr hR
  have hslope :
      curve.toAffine.slope U 4 V (-4) = (V + 4) / (U - 4) := by
    simp [WeierstrassCurve.Affine.slope, hUfour]
  have haddX :
      curve.toAffine.addX U 4
          (curve.toAffine.slope U 4 V (-4)) = ur := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [curve]
    dsimp [ur, sr]
    exact translated_x_identity hU hV ht hUfour
  have haddY :
      curve.toAffine.addY U 4 V
          (curve.toAffine.slope U 4 V (-4)) = vr := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY]
    norm_num [curve]
    rw [translated_x_identity hU hV ht hUfour]
    dsimp [vr, sr, tr]
    convert translated_y_identity hU hV hUfour using 1
    all_goals ring
  have hnegG :
      -G =
        WeierstrassCurve.Affine.Point.some
          4 (-4) nonsingular_four_neg_four := by
    rw [G, WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    norm_num [WeierstrassCurve.Affine.negY, curve]
  let hsum : curve.toAffine.Nonsingular
      (curve.toAffine.addX U 4 (curve.toAffine.slope U 4 V (-4)))
      (curve.toAffine.addY U 4 V (curve.toAffine.slope U 4 V (-4))) :=
    WeierstrassCurve.Affine.nonsingular_add hP nonsingular_four_neg_four
      (fun h ↦ hUfour h.1)
  have point_some_eq_of_coordinates {x₁ y₁ x₂ y₂ : ℚ}
      (h₁ : curve.toAffine.Nonsingular x₁ y₁)
      (h₂ : curve.toAffine.Nonsingular x₂ y₂)
      (hx : x₁ = x₂) (hy : y₁ = y₂) :
      WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ =
        WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ := by
    subst x₂
    subst y₂
    rfl
  have hsub :
      WeierstrassCurve.Affine.Point.some U V hP - G = R := by
    calc
      WeierstrassCurve.Affine.Point.some U V hP - G =
          WeierstrassCurve.Affine.Point.some
            (curve.toAffine.addX U 4 (curve.toAffine.slope U 4 V (-4)))
            (curve.toAffine.addY U 4 V (curve.toAffine.slope U 4 V (-4))) hsum := by
        rw [sub_eq_add_neg, hnegG]
        exact WeierstrassCurve.Affine.Point.add_of_X_ne hUfour
      _ = R := by
        exact point_some_eq_of_coordinates hsum hR haddX haddY
  have hsum0 : t + s ≠ 0 := by
    intro hsum
    have htneg : t = -s := by linarith
    have hsquare : (s ^ 2 - 4) ^ 2 = 0 := by
      rw [htneg, hU] at ht
      nlinarith [ht]
    have hsvalue : s ^ 2 - 4 = 0 :=
      sq_eq_zero_iff.mp hsquare
    apply hUfour
    rw [hU]
    linarith
  have hsr0 : sr ≠ 0 := by
    dsimp [sr]
    exact div_ne_zero
      (mul_ne_zero (by norm_num) hsum0)
      (sub_ne_zero.mpr hUfour)
  have hur0 : ur ≠ 0 := by
    dsimp [ur]
    exact pow_ne_zero 2 hsr0
  let X₀ : ℚ := 2 * U - 7 - 2 * t
  let X₁ : ℚ := 2 * U - 7 + 2 * t
  have hXprod : X₀ * X₁ = -15 := by
    dsimp [X₀, X₁]
    nlinarith [ht]
  have hX₀0 : X₀ ≠ 0 := by
    intro h
    rw [h] at hXprod
    norm_num at hXprod
  have hsminus : s - 2 ≠ 0 := by
    intro hs
    apply hUfour
    rw [hU]
    nlinarith
  let Xr : ℚ := 2 * ur - 7 - 2 * tr
  let Xr₁ : ℚ := 2 * ur - 7 + 2 * tr
  have hXrprod : Xr * Xr₁ = -15 := by
    dsimp [Xr, Xr₁]
    nlinarith [htr]
  have hXr0 : Xr ≠ 0 := by
    intro h
    rw [h] at hXrprod
    norm_num at hXrprod
  have hXrformula :
      Xr = (s ^ 2 + 4 * t + 4) / (s - 2) ^ 2 := by
    dsimp [Xr, ur, sr, tr]
    exact translated_auxiliary_identity hU ht hUfour
  have hauxprod :
      (s ^ 2 + 4 * t + 4) * X₁ =
        5 * (t + s ^ 2 - 2) ^ 2 :=
    translated_auxiliary_product hU ht rfl
  have hdirect :
      IsSquare Xr ∨ ∃ q : ℚ, Xr = -15 * q ^ 2 := by
    rcases hcase with hfive | hnegthree
    · have hz0 : z ≠ 0 := by
        intro hz
        rw [hz] at hfive
        norm_num at hfive
        exact hX₀0 (by simpa [X₀] using hfive)
      have hX₁eq : X₁ = -3 / z ^ 2 := by
        rw [show X₀ = 5 * z ^ 2 by simpa [X₀] using hfive] at hXprod
        field_simp [hz0]
        linear_combination (1 / 5 : ℚ) * hXprod
      have hnumerator :
          3 * (s ^ 2 + 4 * t + 4) =
            -5 * z ^ 2 * (t + s ^ 2 - 2) ^ 2 := by
        rw [hX₁eq] at hauxprod
        field_simp [hz0] at hauxprod
        linear_combination -hauxprod
      right
      refine
        ⟨z * (t + s ^ 2 - 2) / (3 * (s - 2)), ?_⟩
      rw [hXrformula]
      field_simp [hsminus]
      linear_combination 3 * hnumerator
    · have hz0 : z ≠ 0 := by
        intro hz
        rw [hz] at hnegthree
        norm_num at hnegthree
        exact hX₀0 (by simpa [X₀] using hnegthree)
      have hX₁eq : X₁ = 5 / z ^ 2 := by
        rw [show X₀ = -3 * z ^ 2 by simpa [X₀] using hnegthree] at hXprod
        field_simp [hz0]
        linear_combination (-1 / 3 : ℚ) * hXprod
      have hnumerator :
          s ^ 2 + 4 * t + 4 =
            z ^ 2 * (t + s ^ 2 - 2) ^ 2 := by
        rw [hX₁eq] at hauxprod
        field_simp [hz0] at hauxprod
        linear_combination hauxprod
      left
      refine
        ⟨z * (t + s ^ 2 - 2) / (s - 2), ?_⟩
      rw [hXrformula]
      field_simp [hsminus]
      linear_combination hnumerator
  obtain ⟨Q, hQ⟩ :=
    double_of_direct_auxiliary_class hur0 hR rfl htr rfl hXr0 hdirect
  refine ⟨Q, ?_⟩
  calc
    WeierstrassCurve.Affine.Point.some U V hP =
        G + (WeierstrassCurve.Affine.Point.some U V hP - G) := by
          abel
    _ = G + R := by rw [hsub]
    _ = G + (2 : ℕ) • Q := by rw [hQ]

private lemma curve_equation_of_nonsingular
    {U V : ℚ} (hP : curve.toAffine.Nonsingular U V) :
    V ^ 2 = U * (U ^ 2 - 7 * U + 16) := by
  have heq := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  norm_num [curve] at heq
  nlinarith

/-- Every rational point lies in one of the two cosets represented by the
identity and the visible order-four point `(4,4)`, modulo doubling. -/
theorem two_doubling_cosets (P : curve.toAffine.Point) :
    (∃ Q : curve.toAffine.Point, P = (2 : ℕ) • Q) ∨
      (∃ Q : curve.toAffine.Point, P = G + (2 : ℕ) • Q) := by
  cases P with
  | zero =>
      left
      exact ⟨0, rfl⟩
  | some U V hP =>
      have hcurve := curve_equation_of_nonsingular hP
      rcases eq_or_ne U 0 with rfl | hU0
      · have hV : V = 0 := by
          norm_num at hcurve
          nlinarith [sq_nonneg V]
        subst V
        left
        refine ⟨G, ?_⟩
        simpa [T] using double_G.symm
      · rcases eq_or_ne U 4 with rfl | hUfour
        · have hVsquare : V ^ 2 = (4 : ℚ) ^ 2 := by
            norm_num at hcurve ⊢
            exact hcurve
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp hVsquare with hV | hV
          · subst V
            right
            exact ⟨0, by simp [G]⟩
          · have hV' : V = -4 := by simpa using hV
            subst V
            have hpointneg :
                WeierstrassCurve.Affine.Point.some 4 (-4) hP = -G := by
              rw [G, WeierstrassCurve.Affine.Point.neg_some]
              simp only [WeierstrassCurve.Affine.Point.some.injEq]
              norm_num [WeierstrassCurve.Affine.negY, curve]
            have hthree : G + (2 : ℕ) • G = -G := by
              rw [eq_neg_iff_add_eq_zero]
              calc
                G + (2 : ℕ) • G + G = (4 : ℕ) • G := by abel
                _ = 0 := four_G
            right
            exact ⟨G, hpointneg.trans hthree.symm⟩
        · rcases doubling_or_exceptional_auxiliary_squareclass hU0 hP with
            ⟨Q, hQ⟩ | ⟨s, t, X, z, hU, htdef, hXdef, hcase⟩
          · left
            exact ⟨Q, hQ.symm⟩
          · have hs0 : s ≠ 0 := by
              intro hs
              rw [hs] at hU
              norm_num at hU
              exact hU0 hU
            have hV : V = s * t := by
              rw [htdef]
              field_simp [hs0]
            have ht : t ^ 2 = U ^ 2 - 7 * U + 16 := by
              rw [htdef, div_pow]
              field_simp [hs0]
              nlinarith [hcurve, hU]
            have hcase' :
                2 * U - 7 - 2 * t = 5 * z ^ 2 ∨
                  2 * U - 7 - 2 * t = -3 * z ^ 2 := by
              rw [← hXdef]
              exact hcase
            right
            exact
              exceptional_auxiliary_translate_double hP hU hV ht hUfour hcase'

/-- The image of multiplication by two on the rational point group. -/
abbrev doublingRange : AddSubgroup curve.toAffine.Point :=
  (nsmulAddMonoidHom (α := curve.toAffine.Point) 2).range

private def doublingRepresentative : Fin 2 → curve.toAffine.Point
  | 0 => 0
  | 1 => G

private lemma doubling_quotient_surjective :
    Function.Surjective
      (fun i : Fin 2 ↦
        QuotientAddGroup.mk' doublingRange
          (doublingRepresentative i)) := by
  intro c
  obtain ⟨P, rfl⟩ :=
    QuotientAddGroup.mk'_surjective doublingRange c
  rcases two_doubling_cosets P with ⟨Q, hQ⟩ | ⟨Q, hQ⟩
  · refine
      ⟨0, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm
  · refine
      ⟨1, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm

/-- Multiplication by two has finite index on the rational point group. -/
theorem doubling_finiteIndex : doublingRange.FiniteIndex := by
  letI : Finite (curve.toAffine.Point ⧸ doublingRange) :=
    Finite.of_surjective _ doubling_quotient_surjective
  exact AddSubgroup.finiteIndex_of_finite_quotient

/-- The rational point group is finitely generated. -/
theorem point_fg : AddGroup.FG curve.toAffine.Point :=
  WeierstrassCurve.Affine.fg_point_of_finiteIndex_two curve
    doubling_finiteIndex

/-- The multiplication-by-two index is at most two. -/
theorem doubling_index_le_two : doublingRange.index ≤ 2 := by
  rw [AddSubgroup.index_eq_card]
  exact
    (Nat.card_le_card_of_surjective _
      doubling_quotient_surjective).trans_eq (by simp)

private def twoToTwoTorsion :
    Fin 2 → {P : curve.toAffine.Point // (2 : ℕ) • P = 0}
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨T, double_T⟩

private lemma twoToTwoTorsion_injective :
    Function.Injective twoToTwoTorsion := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [twoToTwoTorsion, T] at hij ⊢

private lemma twoToTwoTorsion_surjective :
    Function.Surjective twoToTwoTorsion := by
  rintro ⟨P, htwo⟩
  cases P with
  | zero =>
      exact ⟨0, rfl⟩
  | some U V hP =>
      have hself :
          WeierstrassCurve.Affine.Point.some U V hP =
            -WeierstrassCurve.Affine.Point.some U V hP := by
        rw [← add_eq_zero_iff_eq_neg]
        simpa [two_nsmul] using htwo
      have hV : V = 0 := by
        rw [WeierstrassCurve.Affine.Point.neg_some] at hself
        simp only [WeierstrassCurve.Affine.Point.some.injEq,
          true_and] at hself
        norm_num [WeierstrassCurve.Affine.negY, curve] at hself
        linarith
      have hcurve := curve_equation_of_nonsingular hP
      have hquadratic : 0 < U ^ 2 - 7 * U + 16 := by
        nlinarith [sq_nonneg (2 * U - 7)]
      have hU : U = 0 := by
        rw [hV] at hcurve
        norm_num at hcurve
        rcases hcurve with hU | hquad
        · exact hU
        · exact (ne_of_gt hquadratic hquad).elim
      subst U
      subst V
      refine ⟨1, ?_⟩
      apply Subtype.ext
      rfl

/-- The curve has exactly two rational points killed by two. -/
theorem two_torsion_card_eq_two :
    Nat.card
      {P : curve.toAffine.Point // (2 : ℕ) • P = 0} = 2 := by
  letI : Finite
      {P : curve.toAffine.Point // (2 : ℕ) • P = 0} :=
    MazurTorsion.finite_two_torsion curve
  simpa using
    (Nat.card_congr
      (Equiv.ofBijective twoToTwoTorsion
        ⟨twoToTwoTorsion_injective,
          twoToTwoTorsion_surjective⟩)).symm

/-- The rational point group has Mordell--Weil rank zero. -/
theorem point_rank_zero :
    Module.finrank ℤ curve.toAffine.Point = 0 := by
  letI : AddGroup.FG curve.toAffine.Point := point_fg
  have hker :
      Nat.card
          (nsmulAddMonoidHom
            (α := curve.toAffine.Point) 2).ker = 2 := by
    change Nat.card
      {P : curve.toAffine.Point // (2 : ℕ) • P = 0} = 2
    exact two_torsion_card_eq_two
  have hformula :=
    AddSubgroup.index_range_nsmul_of_fg curve.toAffine.Point
      (by norm_num : (2 : ℕ) ≠ 0)
  rw [hker] at hformula
  have hpow :
      2 ^ Module.finrank ℤ curve.toAffine.Point ≤ 1 := by
    have hindex := doubling_index_le_two
    change
      (nsmulAddMonoidHom
        (α := curve.toAffine.Point) 2).range.index ≤ 2
      at hindex
    omega
  have hpowequal :
      2 ^ Module.finrank ℤ curve.toAffine.Point = 1 :=
    le_antisymm hpow
      (Nat.one_le_pow _ _ (by norm_num))
  simpa using hpowequal

/-- All rational points are torsion; in particular, the rational point
group is finite. -/
theorem point_finite : Finite curve.toAffine.Point := by
  letI : AddGroup.FG curve.toAffine.Point := point_fg
  letI : Module.Finite ℤ curve.toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr point_fg
  have hmoduleTorsion :
      Module.IsTorsion ℤ curve.toAffine.Point :=
    (Module.finrank_eq_zero_iff_isTorsion (R := ℤ)).mp
      point_rank_zero
  exact AddCommGroup.finite_of_fg_torsion curve.toAffine.Point
    (AddMonoid.isTorsion_iff_isTorsion_int.mpr hmoduleTorsion)

end MazurTorsion.XOneFifteen

end


/- Source module: MazurTorsion.Kubert.OrderFifteenModel. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The order-fifteen Tate curve and `X₁(15)`

This file gives a denominator-safe birational bridge from the compact
Tate-parameter equation in `OrderFifteenReduction` to the standard plane
model

`s² + s t + s = t³ + t²`

and hence to the Weierstrass model

`V² = U(U² - 7U + 16)`.

Put `r = b/c` and `q = c²/(b-c)`.  Then `b = r c` and
`c = q(r-1)`, the usual raw Tate parameters.  Direct expansion gives

`orderFifteenPolynomial b c =
  -c³(b-c)⁵ orderFifteenRawPolynomial r q`.

The raw curve is transformed to the standard plane model by

`t = -(q²r+q²-3qr+r) / ((q-1)(qr-2r+1))`,

`s = -(q²-qr²-qr+3r²-3r+1) / (qr-2r+1)²`.

Every denominator is proved nonzero from the raw equation and the honest
Tate conditions.  The same calculation shows that the resulting
Weierstrass abscissa is neither `0` nor `4`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- Sutherland's raw affine equation for `X₁(15)`. -/
def orderFifteenRawPolynomial (r q : ℚ) : ℚ :=
  r ^ 3 -
    r ^ 2 * q ^ 5 + 7 * r ^ 2 * q ^ 4 -
    18 * r ^ 2 * q ^ 3 + 19 * r ^ 2 * q ^ 2 -
    10 * r ^ 2 * q - r * q ^ 5 + 4 * r * q ^ 4 -
    5 * r * q ^ 2 + 5 * r * q -
    q ^ 5 + q ^ 4 - q ^ 3 + q ^ 2 - q

/-- The raw Tate parameter `r = b/c`. -/
def orderFifteenRawR (b c : ℚ) : ℚ :=
  b / c

/-- The raw Tate parameter `q = c²/(b-c)`. -/
def orderFifteenRawQ (b c : ℚ) : ℚ :=
  c ^ 2 / (b - c)

/-- The standard-plane `t`-coordinate obtained from the raw model. -/
def orderFifteenPlaneTOfRaw (r q : ℚ) : ℚ :=
  -(q ^ 2 * r + q ^ 2 - 3 * q * r + r) /
    ((q - 1) * (q * r - 2 * r + 1))

/-- The standard-plane `s`-coordinate obtained from the raw model. -/
def orderFifteenPlaneSOfRaw (r q : ℚ) : ℚ :=
  -(q ^ 2 - q * r ^ 2 - q * r + 3 * r ^ 2 - 3 * r + 1) /
    (q * r - 2 * r + 1) ^ 2

/-- The standard-plane `t`-coordinate attached directly to Tate parameters. -/
def orderFifteenPlaneT (b c : ℚ) : ℚ :=
  orderFifteenPlaneTOfRaw
    (orderFifteenRawR b c) (orderFifteenRawQ b c)

/-- The standard-plane `s`-coordinate attached directly to Tate parameters. -/
def orderFifteenPlaneS (b c : ℚ) : ℚ :=
  orderFifteenPlaneSOfRaw
    (orderFifteenRawR b c) (orderFifteenRawQ b c)

/-- The `U`-coordinate on `XOneFifteen.curve`. -/
def orderFifteenModelU (b c : ℚ) : ℚ :=
  4 * (orderFifteenPlaneT b c + 1)

/-- The `V`-coordinate on `XOneFifteen.curve`. -/
def orderFifteenModelV (b c : ℚ) : ℚ :=
  4 *
    (2 * orderFifteenPlaneS b c +
      orderFifteenPlaneT b c + 1)

/-- The compact Tate polynomial is the raw `X₁(15)` polynomial after the
displayed denominator-safe substitution. -/
theorem orderFifteenRawPolynomial_eq_zero
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c)
    (hpoly : orderFifteenPolynomial b c = 0) :
    orderFifteenRawPolynomial
      (orderFifteenRawR b c) (orderFifteenRawQ b c) = 0 := by
  have hd : b - c ≠ 0 :=
    sub_ne_zero.mpr hbc
  dsimp [orderFifteenRawR, orderFifteenRawQ,
    orderFifteenRawPolynomial]
  simp only [orderFifteenPolynomial] at hpoly
  field_simp [hc, hd]
  linear_combination -hpoly



private lemma raw_middle_denominator_ne_zero
    {r q : ℚ} (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (hraw : orderFifteenRawPolynomial r q = 0) :
    q * r - 2 * r + 1 ≠ 0 := by
  intro hmiddle
  have hq : q = (2 * r - 1) / r := by
    field_simp [hr0]
    linarith
  have hid :
      orderFifteenRawPolynomial r ((2 * r - 1) / r) =
        (r - 1) ^ 8 / r ^ 5 := by
    simp only [orderFifteenRawPolynomial]
    field_simp [hr0]
    ring
  rw [hq, hid] at hraw
  field_simp [hr0] at hraw
  have hpower : (r - 1) ^ 8 = 0 := by
    simpa using hraw
  exact (pow_ne_zero 8 (sub_ne_zero.mpr hr1)) hpower

private lemma raw_zero_abscissa_factor_ne_zero
    {r q : ℚ} (hq1 : q ≠ 1)
    (hraw : orderFifteenRawPolynomial r q = 0) :
    q ^ 2 - q - r + 1 ≠ 0 := by
  intro hfactor
  have hr : r = q ^ 2 - q + 1 := by
    linarith
  have hid :
      orderFifteenRawPolynomial (q ^ 2 - q + 1) q =
        -(q - 1) ^ 9 := by
    simp only [orderFifteenRawPolynomial]
    ring
  rw [hr, hid] at hraw
  have hpower : (q - 1) ^ 9 = 0 :=
    neg_eq_zero.mp hraw
  exact (pow_ne_zero 9 (sub_ne_zero.mpr hq1)) hpower

private lemma raw_four_abscissa_factor_ne_zero
    {r q : ℚ} (hq0 : q ≠ 0) (hq1 : q ≠ 1)
    (hraw : orderFifteenRawPolynomial r q = 0) :
    q ^ 2 * r + q ^ 2 - 3 * q * r + r ≠ 0 := by
  intro hfactor
  have hcoefficient : q ^ 2 - 3 * q + 1 ≠ 0 := by
    intro hcoefficient
    have hqSq : q ^ 2 = 0 := by
      linear_combination hfactor - r * hcoefficient
    exact (pow_ne_zero 2 hq0) hqSq
  have hr :
      r = -q ^ 2 / (q ^ 2 - 3 * q + 1) := by
    apply (eq_div_iff hcoefficient).2
    linear_combination hfactor
  let m : ℚ := q ^ 2 - 3 * q + 1
  have hm : m = q ^ 2 - 3 * q + 1 :=
    rfl
  have hm0 : m ≠ 0 := by
    simpa [m] using hcoefficient
  have hid :
      orderFifteenRawPolynomial
          (-q ^ 2 / m) q =
        -q * (q - 1) ^ 10 /
          m ^ 3 := by
    simp only [orderFifteenRawPolynomial]
    field_simp [hm0]
    rw [hm]
    ring
  have hrm : r = -q ^ 2 / m := by
    simpa [m] using hr
  rw [hrm, hid] at hraw
  have hdenominator :
      m ^ 3 ≠ 0 :=
    pow_ne_zero 3 hm0
  have hnumerator :
      -q * (q - 1) ^ 10 = 0 :=
    (div_eq_zero_iff.mp hraw).resolve_right hdenominator
  have hnonzero :
      -q * (q - 1) ^ 10 ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr hq0)
      (pow_ne_zero 10 (sub_ne_zero.mpr hq1))
  exact hnonzero hnumerator

private lemma plane_equation_of_numerator
    {a n d l : ℚ} (ha : a ≠ 0) (hn : n ≠ 0)
    (hnum :
      a ^ 3 * l ^ 2 + a ^ 2 * n * l * d -
        a ^ 3 * n ^ 2 * l + n * d ^ 3 -
        a * n ^ 2 * d ^ 2 = 0) :
    (-l / n ^ 2) ^ 2 +
          (-l / n ^ 2) * (-d / (a * n)) +
          (-l / n ^ 2) =
        (-d / (a * n)) ^ 3 +
          (-d / (a * n)) ^ 2 := by
  field_simp [ha, hn]
  linear_combination hnum

private lemma four_neg_div_add_one
    {a n d k : ℚ} (ha : a ≠ 0) (hn : n ≠ 0)
    (hrelation : a * n - d = -k) :
    4 * ((-d) / (a * n) + 1) =
      -4 * k / (a * n) := by
  field_simp [ha, hn]
  linear_combination hrelation

/-- The raw birational formulas satisfy the standard plane equation whenever
their two denominators are nonzero. -/
theorem orderFifteenPlane_equation_of_raw
    {r q : ℚ} (hq1 : q ≠ 1)
    (hmiddle : q * r - 2 * r + 1 ≠ 0)
    (hraw : orderFifteenRawPolynomial r q = 0) :
    let t := orderFifteenPlaneTOfRaw r q
    let s := orderFifteenPlaneSOfRaw r q
    s ^ 2 + s * t + s = t ^ 3 + t ^ 2 := by
  have hqsub : q - 1 ≠ 0 :=
    sub_ne_zero.mpr hq1
  have hnumerator :
      (q - 1) ^ 3 *
            (q ^ 2 - q * r ^ 2 - q * r + 3 * r ^ 2 - 3 * r + 1) ^ 2 +
          (q - 1) ^ 2 * (q * r - 2 * r + 1) *
            (q ^ 2 - q * r ^ 2 - q * r + 3 * r ^ 2 - 3 * r + 1) *
            (q ^ 2 * r + q ^ 2 - 3 * q * r + r) -
          (q - 1) ^ 3 * (q * r - 2 * r + 1) ^ 2 *
            (q ^ 2 - q * r ^ 2 - q * r + 3 * r ^ 2 - 3 * r + 1) +
          (q * r - 2 * r + 1) *
            (q ^ 2 * r + q ^ 2 - 3 * q * r + r) ^ 3 -
          (q - 1) * (q * r - 2 * r + 1) ^ 2 *
            (q ^ 2 * r + q ^ 2 - 3 * q * r + r) ^ 2 =
        0 := by
    simp only [orderFifteenRawPolynomial] at hraw
    linear_combination
      -(q ^ 2 * r + q ^ 2 - 3 * q * r + r) * hraw
  simpa [orderFifteenPlaneTOfRaw, orderFifteenPlaneSOfRaw] using
    plane_equation_of_numerator hqsub hmiddle hnumerator

private lemma raw_r_ne_zero
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0) :
    orderFifteenRawR b c ≠ 0 := by
  exact div_ne_zero hb hc

private lemma raw_r_ne_one
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c) :
    orderFifteenRawR b c ≠ 1 := by
  intro hr
  simp only [orderFifteenRawR] at hr
  have hcleared := (div_eq_iff hc).mp hr
  exact hbc (by simpa using hcleared)

private lemma raw_q_ne_zero
    {b c : ℚ} (hc : c ≠ 0) (hbc : b ≠ c) :
    orderFifteenRawQ b c ≠ 0 := by
  exact div_ne_zero (pow_ne_zero 2 hc)
    (sub_ne_zero.mpr hbc)

private lemma raw_q_ne_one_of_admissible
    {b c : ℚ} (hbc : b ≠ c)
    (hA : c ^ 2 + c - b ≠ 0) :
    orderFifteenRawQ b c ≠ 1 := by
  intro hq
  simp only [orderFifteenRawQ] at hq
  have hcleared :=
    (div_eq_iff (sub_ne_zero.mpr hbc)).mp hq
  apply hA
  linear_combination hcleared



/-- The checked inverse formulas carry every admissible Tate parameter
to the standard affine equation `s² + st + s = t³ + t²`. -/
theorem orderFifteenModel_plane_equation
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderFifteenPolynomial b c = 0) :
    orderFifteenPlaneS b c ^ 2 +
          orderFifteenPlaneS b c * orderFifteenPlaneT b c +
          orderFifteenPlaneS b c =
        orderFifteenPlaneT b c ^ 3 +
          orderFifteenPlaneT b c ^ 2 := by
  have hr0 := raw_r_ne_zero hb hc
  have hr1 := raw_r_ne_one hc hbc
  have hraw :=
    orderFifteenRawPolynomial_eq_zero hc hbc hpoly
  have hq1 :=
    raw_q_ne_one_of_admissible hbc hA
  have hmiddle :=
    raw_middle_denominator_ne_zero hr0 hr1 hraw
  simpa [orderFifteenPlaneT, orderFifteenPlaneS] using
    orderFifteenPlane_equation_of_raw hq1 hmiddle hraw

/-- The inverse rational map lands on the Weierstrass equation used by
`MazurTorsion.XOneFifteen.curve`. -/
theorem orderFifteenModel_curve_equation
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderFifteenPolynomial b c = 0) :
    orderFifteenModelV b c ^ 2 =
      orderFifteenModelU b c *
        (orderFifteenModelU b c ^ 2 -
          7 * orderFifteenModelU b c + 16) := by
  have hplane :=
    orderFifteenModel_plane_equation hb hc hbc hA hpoly
  simpa [orderFifteenModelU, orderFifteenModelV] using
    MazurTorsion.XOneFifteen.to_curve_equation hplane

/-- The image coordinates define an affine point on
`MazurTorsion.XOneFifteen.curve`. -/
theorem orderFifteenModel_nonsingular
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderFifteenPolynomial b c = 0) :
    MazurTorsion.XOneFifteen.curve.toAffine.Nonsingular
      (orderFifteenModelU b c) (orderFifteenModelV b c) := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [MazurTorsion.XOneFifteen.curve]
  linear_combination
    orderFifteenModel_curve_equation hb hc hbc hA hpoly

/-- An admissible order-fifteen parameter does not map to the
two-torsion abscissa `U = 0`. -/
theorem orderFifteenModelU_ne_zero
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderFifteenPolynomial b c = 0) :
    orderFifteenModelU b c ≠ 0 := by
  let r := orderFifteenRawR b c
  let q := orderFifteenRawQ b c
  have hr0 : r ≠ 0 := by
    simpa [r] using raw_r_ne_zero hb hc
  have hr1 : r ≠ 1 := by
    simpa [r] using raw_r_ne_one hc hbc
  have hraw : orderFifteenRawPolynomial r q = 0 := by
    simpa [r, q] using
      orderFifteenRawPolynomial_eq_zero hc hbc hpoly
  have hq1 : q ≠ 1 := by
    simpa [q] using raw_q_ne_one_of_admissible hbc hA
  have hmiddle : q * r - 2 * r + 1 ≠ 0 :=
    raw_middle_denominator_ne_zero hr0 hr1 hraw
  have hfactor : q ^ 2 - q - r + 1 ≠ 0 :=
    raw_zero_abscissa_factor_ne_zero hq1 hraw
  have hcoordinate :
      orderFifteenModelU b c =
        -4 * (q ^ 2 - q - r + 1) /
          ((q - 1) * (q * r - 2 * r + 1)) := by
    simp only [orderFifteenModelU, orderFifteenPlaneT,
      orderFifteenPlaneTOfRaw]
    change
      4 *
          ((-(q ^ 2 * r + q ^ 2 - 3 * q * r + r)) /
              ((q - 1) * (q * r - 2 * r + 1)) + 1) =
        -4 * (q ^ 2 - q - r + 1) /
          ((q - 1) * (q * r - 2 * r + 1))
    apply four_neg_div_add_one
      (sub_ne_zero.mpr hq1) hmiddle
    ring
  rw [hcoordinate]
  exact div_ne_zero (mul_ne_zero (by norm_num) hfactor)
    (mul_ne_zero (sub_ne_zero.mpr hq1) hmiddle)

/-- An admissible order-fifteen parameter does not map to either
point with abscissa `U = 4`. -/
theorem orderFifteenModelU_ne_four
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderFifteenPolynomial b c = 0) :
    orderFifteenModelU b c ≠ 4 := by
  let r := orderFifteenRawR b c
  let q := orderFifteenRawQ b c
  have hr0 : r ≠ 0 := by
    simpa [r] using raw_r_ne_zero hb hc
  have hr1 : r ≠ 1 := by
    simpa [r] using raw_r_ne_one hc hbc
  have hq0 : q ≠ 0 := by
    simpa [q] using raw_q_ne_zero hc hbc
  have hraw : orderFifteenRawPolynomial r q = 0 := by
    simpa [r, q] using
      orderFifteenRawPolynomial_eq_zero hc hbc hpoly
  have hq1 : q ≠ 1 := by
    simpa [q] using raw_q_ne_one_of_admissible hbc hA
  have hmiddle : q * r - 2 * r + 1 ≠ 0 :=
    raw_middle_denominator_ne_zero hr0 hr1 hraw
  have hfactor :
      q ^ 2 * r + q ^ 2 - 3 * q * r + r ≠ 0 :=
    raw_four_abscissa_factor_ne_zero hq0 hq1 hraw
  have hcoordinate :
      orderFifteenModelU b c - 4 =
        -4 * (q ^ 2 * r + q ^ 2 - 3 * q * r + r) /
          ((q - 1) * (q * r - 2 * r + 1)) := by
    simp only [orderFifteenModelU, orderFifteenPlaneT,
      orderFifteenPlaneTOfRaw]
    change
      4 *
            ((-(q ^ 2 * r + q ^ 2 - 3 * q * r + r)) /
              ((q - 1) * (q * r - 2 * r + 1)) + 1) -
          4 =
        -4 * (q ^ 2 * r + q ^ 2 - 3 * q * r + r) /
          ((q - 1) * (q * r - 2 * r + 1))
    ring
  intro hU
  have hzero : orderFifteenModelU b c - 4 = 0 :=
    sub_eq_zero.mpr hU
  rw [hcoordinate] at hzero
  exact
    (div_ne_zero (mul_ne_zero (by norm_num) hfactor)
      (mul_ne_zero (sub_ne_zero.mpr hq1) hmiddle)) hzero

/-- The complete denominator-safe bridge: admissible Tate parameters give
a nonsingular point on the selected `X₁(15)` model outside both visible
finite abscissae. -/
theorem orderFifteenModel_of_admissible
    {b c : ℚ} (hb : b ≠ 0) (hc : c ≠ 0)
    (hbc : b ≠ c) (hA : c ^ 2 + c - b ≠ 0)
    (hpoly : orderFifteenPolynomial b c = 0) :
    MazurTorsion.XOneFifteen.curve.toAffine.Nonsingular
        (orderFifteenModelU b c) (orderFifteenModelV b c) ∧
      orderFifteenModelU b c ≠ 0 ∧
      orderFifteenModelU b c ≠ 4 := by
  exact ⟨orderFifteenModel_nonsingular hb hc hbc hA hpoly,
    orderFifteenModelU_ne_zero hb hc hbc hA hpoly,
    orderFifteenModelU_ne_four hb hc hbc hA hpoly⟩

/-- An exact rational point of order fifteen produces a nonsingular
rational point outside abscissae `0` and `4` on the chosen `X₁(15)`
model.  This is the end-to-end interface from the exact-order hypothesis
to the modular curve. -/
theorem exists_orderFifteenModel_of_exact_order
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 15) :
    ∃ b c : ℚ,
      MazurTorsion.XOneFifteen.curve.toAffine.Nonsingular
          (orderFifteenModelU b c) (orderFifteenModelV b c) ∧
        orderFifteenModelU b c ≠ 0 ∧
        orderFifteenModelU b c ≠ 4 := by
  obtain ⟨b, c, _u, _hu, hb, hc, hbc, hA, hpoly, _hdisc⟩ :=
    exists_tateOrderFifteen_certificate E Q hQ
  exact ⟨b, c,
    orderFifteenModel_of_admissible hb hc hbc hA hpoly⟩

end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.NumberTheory.XOneFifteenReduction. Original headers retained. -/
section

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Rational points on the chosen `X₁(15)` model

The two-isogeny descent proves that the rational point group of

`V² = U(U² - 7U + 16)`

is finite.  Reduction at seven bounds its cardinality by eight.  The
visible point `(4,4)` has order four, while a denominator-free duplication
identity and a monic quartic obstruction modulo seventeen rule out points
of order eight.  The exact two-torsion cardinality then forces the whole
group to have cardinality four.
-/

open WeierstrassCurve

namespace MazurTorsion.XOneFifteen

open WeierstrassCurve.Affine
  IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩







instance : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]































/-- The concrete good-prime bound, using the public full-torsion reduction
interface. The original point classification below remains unchanged. -/
theorem point_card_le_eight : Nat.card curve.toAffine.Point ≤ 8 := by
  let W : WeierstrassCurve ℤ := ⟨0, -7, 0, 16, 0⟩
  have hW : W.map (Int.castRingHom ℚ) = curve := by
    ext <;> norm_num [W, curve, WeierstrassCurve.map]
  letI : (W.map (Int.castRingHom ℚ)).IsElliptic := hW.symm ▸ inferInstance
  letI : Finite (W.map (Int.castRingHom ℚ)).toAffine.Point := hW.symm ▸ point_finite
  have hgood : ¬ (7 : ℤ) ∣ W.Δ := by
    norm_num [W, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hdiv := MazurTransfer.finite_toAffine_card_dvd W 7 (by decide) hgood
  have hcount : Nat.card (W.map (Int.castRingHom (ZMod 7))).toAffine.Point = 8 := by
    exact Nat.card_eq_fintype_card.trans (by decide +kernel)
  have hle : Nat.card curve.toAffine.Point ≤
      Nat.card (W.map (Int.castRingHom (ZMod 7))).toAffine.Point := by
    rw [← hW]
    exact Nat.le_of_dvd (by rw [hcount]; decide) hdiv
  simpa only [hcount] using hle


private lemma double_G_reduction : (2 : ℕ) • G = T := by
  simp only [two_nsmul, G]
  rw [Point.add_self_of_Y_ne
    (by norm_num [negY, curve])]
  rw [T]
  simp only [Point.some.injEq]
  constructor
  · norm_num [addX, WeierstrassCurve.Affine.slope, negY, curve]
  · norm_num [addY, addX,
      WeierstrassCurve.Affine.slope, negY, curve]

private lemma double_T_reduction : (2 : ℕ) • T = 0 := by
  simp only [two_nsmul]
  rw [T]
  apply Point.add_self_of_Y_eq
  norm_num [negY, curve]

private lemma four_G_reduction : (4 : ℕ) • G = 0 := by
  calc
    (4 : ℕ) • G = (2 : ℕ) • ((2 : ℕ) • G) := by
      norm_num [← mul_nsmul]
    _ = (2 : ℕ) • T := by rw [double_G_reduction]
    _ = 0 := double_T_reduction

/-- The visible point `(4,4)` has exact additive order four. -/
theorem addOrderOf_G : addOrderOf G = 4 := by
  apply addOrderOf_eq_of_nsmul_and_div_prime_nsmul
    (by norm_num) four_G_reduction
  intro p hp hpdiv
  have hp22 : p ∣ 2 * 2 := by
    simpa using hpdiv
  have hp2 : p = 2 := by
    rcases hp.dvd_mul.mp hp22 with hp2 | hp2
    · rcases (Nat.dvd_prime
        (by decide : Nat.Prime 2)).mp hp2 with hp1 | hp2
      · exact (hp.ne_one hp1).elim
      · exact hp2
    · rcases (Nat.dvd_prime
        (by decide : Nat.Prime 2)).mp hp2 with hp1 | hp2
      · exact (hp.ne_one hp1).elim
      · exact hp2
  subst p
  rw [show 4 / 2 = 2 by norm_num, double_G_reduction]
  simp [T]

private lemma curve_equation
    {x y : ℚ} (h : curve.toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 - 7 * x ^ 2 + 16 * x := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [curve] at heq
  convert heq using 1 <;> ring

private lemma duplication_identity_algebra
    {x y x₂ : ℚ} (hy : y ≠ 0)
    (hcurve : y ^ 2 = x ^ 3 - 7 * x ^ 2 + 16 * x)
    (hx₂ :
      x₂ =
        ((3 * x ^ 2 - 14 * x + 16) / (2 * y)) ^ 2 +
          7 - 2 * x) :
    x₂ * (2 * y) ^ 2 = (x ^ 2 - 16) ^ 2 := by
  rw [hx₂]
  field_simp [hy]
  linear_combination -4 * (-7 + 2 * x) * hcurve

/-- The denominator-free duplication identity on the chosen model. -/
private lemma duplication_identity_of_double
    {x y x₂ y₂ : ℚ}
    (hP : curve.toAffine.Nonsingular x y)
    (hP₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hdouble :
      (2 : ℕ) • Point.some x y hP =
        Point.some x₂ y₂ hP₂) :
    x₂ * (2 * y) ^ 2 = (x ^ 2 - 16) ^ 2 := by
  have hy : y ≠ curve.toAffine.negY x y := by
    intro hy
    have hzero :
        (2 : ℕ) • Point.some x y hP = 0 := by
      rw [two_nsmul, Point.add_self_of_Y_eq hy]
    rw [hzero] at hdouble
    exact Point.some_ne_zero hP₂ hdouble.symm
  have hy0 : y ≠ 0 := by
    intro hy0
    apply hy
    simp [curve, negY, hy0]
  let ℓ := curve.toAffine.slope x x y y
  have hadd :=
    Point.add_self_of_Y_ne
      (W := curve.toAffine) (h₁ := hP) hy
  have hx₂ : curve.toAffine.addX x x ℓ = x₂ := by
    have hsum :
        Point.some x y hP + Point.some x y hP =
          Point.some x₂ y₂ hP₂ := by
      simpa [two_nsmul] using hdouble
    exact (Point.some.inj (hadd.symm.trans hsum)).1
  have hℓ :
      ℓ = (3 * x ^ 2 - 14 * x + 16) / (2 * y) := by
    dsimp [ℓ]
    rw [slope_of_Y_ne rfl hy]
    simp only [negY]
    simp [curve]
    ring
  apply duplication_identity_algebra hy0
    (curve_equation hP)
  rw [← hx₂]
  simp only [addX]
  rw [hℓ]
  simp [curve]
  ring

private noncomputable def orderEightPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 4 -
    Polynomial.C 16 * Polynomial.X ^ 3 +
    Polynomial.C 80 * Polynomial.X ^ 2 -
    Polynomial.C 256 * Polynomial.X +
    Polynomial.C 256

private lemma orderEightPolynomial_monic :
    Polynomial.Monic orderEightPolynomial := by
  unfold orderEightPolynomial
  monicity!

private lemma orderEightPolynomial_no_root_mod_seventeen :
    ∀ x : ZMod 17,
      x ^ 4 - 16 * x ^ 3 + 80 * x ^ 2 -
        256 * x + 256 ≠ 0 := by
  decide

private lemma orderEightPolynomial_no_rational_root (x : ℚ) :
    x ^ 4 - 16 * x ^ 3 + 80 * x ^ 2 -
      256 * x + 256 ≠ 0 := by
  intro hx
  have hroot :
      Polynomial.aeval x orderEightPolynomial = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [orderEightPolynomial]
    exact hx
  obtain ⟨z, hxz, -⟩ :=
    exists_integer_of_is_root_of_monic
      orderEightPolynomial_monic hroot
  have hzrat :
      (z : ℚ) ^ 4 - 16 * (z : ℚ) ^ 3 +
          80 * (z : ℚ) ^ 2 - 256 * (z : ℚ) + 256 = 0 := by
    have hzcast : (z : ℚ) = x := by
      simpa using hxz.symm
    rw [hzcast]
    exact hx
  have hzint :
      z ^ 4 - 16 * z ^ 3 + 80 * z ^ 2 -
          256 * z + 256 = 0 := by
    exact_mod_cast hzrat
  apply orderEightPolynomial_no_root_mod_seventeen (z : ZMod 17)
  simpa using congrArg (fun n : ℤ ↦ (n : ZMod 17)) hzint

private def twoVisible :
    Fin 2 → {P : curve.toAffine.Point // (2 : ℕ) • P = 0}
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨T, double_T_reduction⟩

private lemma twoVisible_injective :
    Function.Injective twoVisible := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [twoVisible, T] at hij ⊢

private lemma twoVisible_bijective :
    Function.Bijective twoVisible := by
  letI : Finite
      {P : curve.toAffine.Point // (2 : ℕ) • P = 0} :=
    MazurTorsion.finite_two_torsion curve
  exact twoVisible_injective.bijective_of_nat_card_le
    (by simpa using two_torsion_card_eq_two.le)

private lemma eq_zero_or_eq_T
    {P : curve.toAffine.Point} (hP : (2 : ℕ) • P = 0) :
    P = 0 ∨ P = T := by
  obtain ⟨i, hi⟩ := twoVisible_bijective.2 ⟨P, hP⟩
  fin_cases i
  · left
    simpa [twoVisible] using congrArg Subtype.val hi.symm
  · right
    simpa [twoVisible] using congrArg Subtype.val hi.symm

/-- No rational point on the chosen model has additive order eight. -/
theorem addOrderOf_ne_eight (Q : curve.toAffine.Point) :
    addOrderOf Q ≠ 8 := by
  intro hQorder
  let P : curve.toAffine.Point := (2 : ℕ) • Q
  have hPorder : addOrderOf P = 4 := by
    dsimp [P]
    rw [addOrderOf_nsmul' Q (by norm_num), hQorder]
    norm_num
  have hdoublePorder :
      addOrderOf ((2 : ℕ) • P) = 2 := by
    rw [addOrderOf_nsmul' P (by norm_num), hPorder]
    norm_num
  have hdoublePtwo :
      (2 : ℕ) • ((2 : ℕ) • P) = 0 := by
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    rw [hdoublePorder]
  have hdoublePne :
      (2 : ℕ) • P ≠ 0 := by
    intro hzero
    have hdiv : addOrderOf P ∣ 2 :=
      addOrderOf_dvd_of_nsmul_eq_zero hzero
    rw [hPorder] at hdiv
    norm_num at hdiv
  have hdoubleP :
      (2 : ℕ) • P = T :=
    (eq_zero_or_eq_T hdoublePtwo).resolve_left hdoublePne
  have hPne : P ≠ 0 := by
    intro hzero
    rw [hzero] at hPorder
    norm_num at hPorder
  obtain ⟨xP, yP, hPns, hPcoords⟩ :
      ∃ (x y : ℚ) (h : curve.toAffine.Nonsingular x y),
        P = Point.some x y h := by
    cases hcase : P with
    | zero => exact (hPne hcase).elim
    | some x y h => exact ⟨x, y, h, rfl⟩
  have hPTcoords :
      (2 : ℕ) • Point.some xP yP hPns =
        Point.some 0 0
          (by
            apply curve.toAffine.equation_iff_nonsingular.mp
            norm_num [WeierstrassCurve.Affine.equation_iff, curve]) := by
    simpa only [hPcoords, T] using hdoubleP
  have hdupP :=
    duplication_identity_of_double hPns _ hPTcoords
  have hxPsq : xP ^ 2 = 16 := by
    have hsquare : (xP ^ 2 - 16) ^ 2 = 0 := by
      simpa using hdupP.symm
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  have hxP : xP = 4 := by
    have hcases : xP = 4 ∨ xP = -4 := by
      apply (sq_eq_sq_iff_eq_or_eq_neg).mp
      norm_num
      exact hxPsq
    rcases hcases with hxP | hxP
    · exact hxP
    · have hcurveP := curve_equation hPns
      rw [hxP] at hcurveP
      norm_num at hcurveP
      nlinarith [sq_nonneg yP]
  have hQne : Q ≠ 0 := by
    intro hzero
    rw [hzero] at hQorder
    norm_num at hQorder
  obtain ⟨xQ, yQ, hQns, hQcoords⟩ :
      ∃ (x y : ℚ) (h : curve.toAffine.Nonsingular x y),
        Q = Point.some x y h := by
    cases hcase : Q with
    | zero => exact (hQne hcase).elim
    | some x y h => exact ⟨x, y, h, rfl⟩
  have hQPcoords :
      (2 : ℕ) • Point.some xQ yQ hQns =
        Point.some xP yP hPns := by
    rw [← hQcoords, ← hPcoords]
  have hdupQ :=
    duplication_identity_of_double hQns hPns hQPcoords
  have hcurveQ := curve_equation hQns
  apply orderEightPolynomial_no_rational_root xQ
  rw [hxP] at hdupQ
  nlinarith [hdupQ, hcurveQ]

private lemma point_card_ne_eight :
    Nat.card curve.toAffine.Point ≠ 8 := by
  letI : Finite curve.toAffine.Point := point_finite
  intro hcard
  let f : curve.toAffine.Point →+ curve.toAffine.Point :=
    nsmulAddMonoidHom 2
  have hker : Nat.card f.ker = 2 := by
    change Nat.card
      {P : curve.toAffine.Point // (2 : ℕ) • P = 0} = 2
    exact two_torsion_card_eq_two
  have hrangeCard : Nat.card f.range = 4 := by
    have hproduct := f.ker.index_mul_card
    rw [AddSubgroup.index_ker, hker, hcard] at hproduct
    omega
  have hfour (P : curve.toAffine.Point) :
      (4 : ℕ) • P = 0 := by
    have hdvd : addOrderOf P ∣ 8 := by
      simpa [hcard] using addOrderOf_dvd_natCard P
    have hdvdpow : addOrderOf P ∣ 2 ^ 3 := by
      norm_num
      exact hdvd
    obtain ⟨k, hk, horder⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp hdvdpow
    have hk2 : k ≤ 2 := by
      by_contra hknot
      have hk3 : k = 3 := by omega
      apply addOrderOf_ne_eight P
      rw [horder, hk3]
      norm_num
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    rw [horder]
    interval_cases k <;> norm_num
  have hrange_le_ker : f.range ≤ f.ker := by
    rintro R ⟨P, rfl⟩
    change (2 : ℕ) • ((2 : ℕ) • P) = 0
    calc
      (2 : ℕ) • ((2 : ℕ) • P) =
          (4 : ℕ) • P := by
        rw [← mul_nsmul]
      _ = 0 := hfour P
  have hle : Nat.card f.range ≤ Nat.card f.ker :=
    AddSubgroup.card_le_of_le hrange_le_ker
  rw [hrangeCard, hker] at hle
  omega

/-- The chosen `X₁(15)` model has exactly four rational points. -/
theorem point_card_eq_four :
    Nat.card curve.toAffine.Point = 4 := by
  letI : Finite curve.toAffine.Point := point_finite
  have hle := point_card_le_eight
  have hdiv : 4 ∣ Nat.card curve.toAffine.Point := by
    rw [← addOrderOf_G]
    exact addOrderOf_dvd_natCard G
  obtain ⟨k, hk⟩ := hdiv
  have hpos : 0 < Nat.card curve.toAffine.Point :=
    Nat.card_pos
  have hcases :
      Nat.card curve.toAffine.Point = 4 ∨
        Nat.card curve.toAffine.Point = 8 := by
    omega
  exact hcases.resolve_right point_card_ne_eight

/-- The four visible rational points. -/
private lemma nonsingular_four_neg_four_reduction :
    curve.toAffine.Nonsingular 4 (-4) := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

/-- The four rational points used in the explicit cardinality lower bound. -/
def fourVisiblePoints : Fin 4 → curve.toAffine.Point
  | 0 => 0
  | 1 => T
  | 2 => G
  | 3 => .some 4 (-4) nonsingular_four_neg_four_reduction

theorem fourVisiblePoints_injective :
    Function.Injective fourVisiblePoints := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [fourVisiblePoints, T, G] at hij ⊢
  all_goals norm_num at hij

/-- The four visible points exhaust the rational point group. -/
theorem fourVisiblePoints_bijective :
    Function.Bijective fourVisiblePoints := by
  letI : Finite curve.toAffine.Point := point_finite
  exact fourVisiblePoints_injective.bijective_of_nat_card_le
    (by simp [point_card_eq_four])

/-- Every affine rational point on the chosen model has abscissa zero or
four. -/
theorem point_abscissa_eq_zero_or_four
    {U V : ℚ}
    (hP : curve.toAffine.Nonsingular U V) :
    U = 0 ∨ U = 4 := by
  let P : curve.toAffine.Point := .some U V hP
  obtain ⟨i, hi⟩ := fourVisiblePoints_bijective.2 P
  fin_cases i
  · have hzero : P ≠ 0 := Point.some_ne_zero hP
    exact (hzero (by
      simpa only [fourVisiblePoints] using hi.symm)).elim
  · left
    have hcoords : (0 : ℚ) = U ∧ (0 : ℚ) = V := by
      simpa only [fourVisiblePoints, T, P,
        Point.some.injEq] using hi
    exact hcoords.1.symm
  · right
    have hcoords : (4 : ℚ) = U ∧ (4 : ℚ) = V := by
      simpa only [fourVisiblePoints, G, P,
        Point.some.injEq] using hi
    exact hcoords.1.symm
  · right
    have hcoords : (4 : ℚ) = U ∧ (-4 : ℚ) = V := by
      simpa only [fourVisiblePoints, G, P,
        Point.some.injEq] using hi
    exact hcoords.1.symm

end MazurTorsion.XOneFifteen

end


/- Source module: MazurTorsion.Kubert.OrderFifteen. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Excluding rational points of order fifteen

An exact order-fifteen point produces, through Tate normal form, a rational
point on

`V² = U(U² - 7U + 16)`

whose abscissa is different from `0` and `4`.  The specialized two-isogeny
descent, reduction modulo seven, and order-eight obstruction show that every
affine rational point on this curve has one of exactly those two abscissae.
This contradiction closes the order-fifteen branch.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- No rational elliptic curve has a rational point of exact order
fifteen. -/
theorem no_rational_point_of_order_fifteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 15 := by
  intro hQ
  obtain ⟨b, c, hmodel, hU0, hU4⟩ :=
    exists_orderFifteenModel_of_exact_order E Q hQ
  rcases XOneFifteen.point_abscissa_eq_zero_or_four hmodel with h | h
  · exact hU0 h
  · exact hU4 h

/-- Obstruction-form restatement on the canonical rational base change. -/
theorem rationalPoint_addOrderOf_ne_fifteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 15 :=
  no_rational_point_of_order_fifteen E Q

end MazurTorsion.Kubert

end

open scoped WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 15 := by
  intro x hx
  have horder : addOrderOf (x : (E⁄ℚ).Point) = addOrderOf x :=
    addOrderOf_injective (AddCommGroup.torsion (E⁄ℚ).Point).subtype
      (AddCommGroup.torsion (E⁄ℚ).Point).subtype_injective x
  exact MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_fifteen E x (horder.trans hx)

example : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (x : MazurCampaign.RationalTorsion E), addOrderOf x ≠ 15 := solution
#print axioms solution
