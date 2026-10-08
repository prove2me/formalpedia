-- Prove2me | solution 1 for MazurTransfer.order13_from_genus_two_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T14:40:01.355546+00:00
-- url     : https://prove2.me/submissions/ba45b094-10a9-494f-9e71-e151bb2586d0

import Mathlib
open scoped WeierstrassCurve WeierstrassCurve.Affine


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

/-- The recurrence-defined `X`-coordinate of `6P`. Keeping the sixth multiple in recurrence
form avoids expanding a much larger rational expression and makes subsequent calculations
share the same checked addition interface. -/
def tateSixX (b c : ℚ) : ℚ :=
  tateNextX b c (tateFiveX b c) (tateFiveY b c)

/-- The recurrence-defined `Y`-coordinate of `6P`. -/
def tateSixY (b c : ℚ) : ℚ :=
  tateNextY b c (tateFiveX b c) (tateFiveY b c)

/-- If the additional fifth-multiple numerator `c²+c-b` is nonzero, the recurrence computes
`6P`. Together with `b ≠ 0`, `c ≠ 0`, and `b ≠ c`, this is precisely what proves that the
`X`-coordinate of `5P` is nonzero. -/
theorem six_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₆ : (tateNormalCurve b c).toAffine.Nonsingular
        (tateSixX b c) (tateSixY b c),
      (6 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some (tateSixX b c) (tateSixY b c) h₆ := by
  obtain ⟨h₅, hfive⟩ :=
    five_nsmul_origin_coordinates b c hb hc hbc h00
  have hx₅ : tateFiveX b c ≠ 0 := by
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero hb hc) hfiveNumerator)
      (pow_ne_zero 2 (sub_ne_zero.mpr hbc))
  obtain ⟨h₆, hsix⟩ :=
    add_origin_coordinates b c (tateFiveX b c) (tateFiveY b c) hx₅ h₅ h00
  refine ⟨h₆, ?_⟩
  rw [show (6 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      (5 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
  rw [hfive, hsix]
  rfl

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











end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.Kubert.OrderFourteenReduction. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Reduction of a point of order fourteen

An exact rational point of order `14` can be put in Tate normal form.  The checked
addition recurrence computes its sixth and seventh multiples.  Since the seventh
multiple has order `2`, its coordinates satisfy

`2 * y(7P) + (1-c) * x(7P) - b = 0`.

Clearing precisely the denominators introduced by the recurrence gives
`orderFourteenPolynomial`.  This file proves only this forward reduction, retaining
all denominator conditions and the discriminant scale.  It makes no assertion about
the rational points of the resulting genus-one parameter curve.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The numerator appearing in the denominator-safe formula for `x(6P)`. -/
def tateSixNumerator (b c : ℚ) : ℚ :=
  b ^ 2 - b * c - c ^ 3

/-- An auxiliary numerator in the coordinates of `7P`. -/
def tateSevenAux (b c : ℚ) : ℚ :=
  2 * b ^ 2 - b * c ^ 2 - 3 * b * c + c ^ 2



/-- The recurrence-defined `X`-coordinate of `7P`. -/
def tateSevenX (b c : ℚ) : ℚ :=
  tateNextX b c (tateSixX b c) (tateSixY b c)

/-- The recurrence-defined `Y`-coordinate of `7P`. -/
def tateSevenY (b c : ℚ) : ℚ :=
  tateNextY b c (tateSixX b c) (tateSixY b c)



private lemma tateFiveRatio_eq
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c) :
    tateFiveY b c / tateFiveX b c =
      c * tateSixNumerator b c /
        ((b - c) * (c ^ 2 + c - b)) := by
  simp only [tateFiveX, tateFiveY, tateSixNumerator]
  field_simp [hb, hc, sub_ne_zero.mpr hbc]

lemma tateSixX_eq_reduced
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0) :
    tateSixX b c =
      (b - c) * tateSixNumerator b c / (c ^ 2 + c - b) ^ 2 := by
  let A : ℚ := c ^ 2 + c - b
  let B : ℚ := tateSixNumerator b c
  let d : ℚ := b - c
  have hA : A ≠ 0 := by simpa only [A] using hfiveNumerator
  have hd : d ≠ 0 := by simpa only [d] using sub_ne_zero.mpr hbc
  have hratio :
      tateFiveY b c / tateFiveX b c = c * B / (d * A) := by
    simpa only [A, B, d] using tateFiveRatio_eq b c hb hc hbc
  have hxfive : tateFiveX b c = b * c * A / d ^ 2 := by
    simp only [tateFiveX, A, d]
  change tateNextX b c (tateFiveX b c) (tateFiveY b c) =
    d * B / A ^ 2
  simp only [tateNextX]
  rw [hratio, hxfive]
  field_simp [hA, hd]
  dsimp only [A, B, d, tateSixNumerator]
  ring

lemma tateSixY_eq_reduced
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0) :
    tateSixY b c =
      -c * (b - c) ^ 2 * tateSevenAux b c /
        (c ^ 2 + c - b) ^ 3 := by
  let A : ℚ := c ^ 2 + c - b
  let B : ℚ := tateSixNumerator b c
  let C : ℚ := tateSevenAux b c
  let d : ℚ := b - c
  have hA : A ≠ 0 := by simpa only [A] using hfiveNumerator
  have hd : d ≠ 0 := by simpa only [d] using sub_ne_zero.mpr hbc
  have hratio :
      tateFiveY b c / tateFiveX b c = c * B / (d * A) := by
    simpa only [A, B, d] using tateFiveRatio_eq b c hb hc hbc
  have hxfive : tateFiveX b c = b * c * A / d ^ 2 := by
    simp only [tateFiveX, A, d]
  have hyfive : tateFiveY b c = b * c ^ 2 * B / d ^ 3 := by
    simp only [tateFiveY, B, d, tateSixNumerator]
  have hxsix : tateSixX b c = d * B / A ^ 2 := by
    simpa only [A, B, d] using
      tateSixX_eq_reduced b c hb hc hbc hfiveNumerator
  change
    -((tateFiveY b c / tateFiveX b c) *
          (tateSixX b c - tateFiveX b c) + tateFiveY b c) -
        (1 - c) * tateSixX b c + b =
      -c * d ^ 2 * C / A ^ 3
  rw [hratio, hxfive, hyfive, hxsix]
  field_simp [hA, hd]
  dsimp only [A, B, C, d, tateSixNumerator, tateSevenAux]
  ring

private lemma tateSixRatio_eq
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (hsixNumerator : tateSixNumerator b c ≠ 0) :
    tateSixY b c / tateSixX b c =
      -c * (b - c) * tateSevenAux b c /
        ((c ^ 2 + c - b) * tateSixNumerator b c) := by
  rw [tateSixX_eq_reduced b c hb hc hbc hfiveNumerator,
    tateSixY_eq_reduced b c hb hc hbc hfiveNumerator]
  field_simp [hc, sub_ne_zero.mpr hbc, hfiveNumerator,
    hsixNumerator]

lemma tateSevenX_eq_reduced
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (hsixNumerator : tateSixNumerator b c ≠ 0) :
    tateSevenX b c =
      -b * c * (c ^ 2 + c - b) * tateSevenAux b c /
        tateSixNumerator b c ^ 2 := by
  let A : ℚ := c ^ 2 + c - b
  let B : ℚ := tateSixNumerator b c
  let C : ℚ := tateSevenAux b c
  let d : ℚ := b - c
  have hA : A ≠ 0 := by simpa only [A] using hfiveNumerator
  have hB : B ≠ 0 := by simpa only [B] using hsixNumerator
  have hd : d ≠ 0 := by simpa only [d] using sub_ne_zero.mpr hbc
  have hratio :
      tateSixY b c / tateSixX b c = -c * d * C / (A * B) := by
    simpa only [A, B, C, d] using
      tateSixRatio_eq b c hb hc hbc hfiveNumerator hsixNumerator
  have hxsix : tateSixX b c = d * B / A ^ 2 := by
    simpa only [A, B, d] using
      tateSixX_eq_reduced b c hb hc hbc hfiveNumerator
  change tateNextX b c (tateSixX b c) (tateSixY b c) =
    -b * c * A * C / B ^ 2
  simp only [tateNextX]
  rw [hratio, hxsix]
  field_simp [hA, hB, hd]
  dsimp only [A, B, C, d, tateSixNumerator, tateSevenAux]
  ring



/-- Checked recurrence from `6P` to `7P`, with every denominator recorded. -/
theorem seven_nsmul_origin_coordinates
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (hsixNumerator : tateSixNumerator b c ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0) :
    ∃ h₇ : (tateNormalCurve b c).toAffine.Nonsingular
        (tateSevenX b c) (tateSevenY b c),
      (7 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
        WeierstrassCurve.Affine.Point.some
          (tateSevenX b c) (tateSevenY b c) h₇ := by
  obtain ⟨h₆, hsix⟩ :=
    six_nsmul_origin_coordinates b c hb hc hbc hfiveNumerator h00
  have hxsix : tateSixX b c ≠ 0 := by
    rw [tateSixX_eq_reduced b c hb hc hbc hfiveNumerator]
    exact div_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr hbc) hsixNumerator)
      (pow_ne_zero 2 hfiveNumerator)
  obtain ⟨h₇, hseven⟩ :=
    add_origin_coordinates b c (tateSixX b c) (tateSixY b c)
      hxsix h₆ h00
  refine ⟨h₇, ?_⟩
  rw [show (7 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      (6 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
  rw [hsix, hseven]
  rfl



















end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.Kubert.OrderThirteenReduction. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


noncomputable section


/-!
# Reduction of a point of order thirteen

Let `P = (0, 0)` be the marked point on the Tate normal form

`y² + (1-c)xy - by = x³ - bx²`.

If `P` has exact order `13`, then `7P = -6P`; in particular, the two points have the
same `X`-coordinate.  The checked formulas for `6P` and `7P` turn this equality into

`(b-c) B³ + bc A³ C = 0`,

where

* `A = c² + c - b`,
* `B = b² - bc - c³`, and
* `C = 2b² - bc² - 3bc + c²`.

All factors used as denominators are proved nonzero from exact order, rather than
discarded during simplification.

The substitutions

`r = b/c`, `s = c²/(b-c)`

then give the affine plane model

`r³ + (-s⁴ + 5s³ - 9s² + 4s - 2)r²
    + (-s³ + 6s² - 3s + 1)r - s³ = 0`.

This file proves the forward reduction only.  It does not classify the rational
points of this genus-two modular curve.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The denominator-safe Tate-parameter polynomial forced by exact order `13`.

It is obtained by equating the checked `X`-coordinates of `6P` and `7P`. -/
def orderThirteenPolynomial (b c : ℚ) : ℚ :=
  let A := c ^ 2 + c - b
  let B := tateSixNumerator b c
  let C := tateSevenAux b c
  (b - c) * B ^ 3 + b * c * A ^ 3 * C

/-- The reduced affine `X₁(13)` polynomial in the coordinates
`r = b/c` and `s = c²/(b-c)`. -/
def orderThirteenReducedPolynomial (r s : ℚ) : ℚ :=
  r ^ 3 +
    (-s ^ 4 + 5 * s ^ 3 - 9 * s ^ 2 + 4 * s - 2) * r ^ 2 +
    (-s ^ 3 + 6 * s ^ 2 - 3 * s + 1) * r -
    s ^ 3

private theorem nsmul_ne_zero_of_marked_order_thirteen
    {G : Type*} [AddCommGroup G] (P : G)
    (horder : addOrderOf P = 13) (n : ℕ) (hndvd : ¬13 ∣ n) :
    n • P ≠ 0 := by
  intro hn
  apply hndvd
  rw [← horder]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn

private lemma c_ne_zero_of_marked_order_thirteen
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 13) :
    c ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfourNe : (4 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 4 (by norm_num)
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

private lemma parameters_ne_of_marked_order_thirteen
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 13) :
    b ≠ c := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfiveNe : (5 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 5 (by norm_num)
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

private lemma five_numerator_ne_of_marked_order_thirteen
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 13) :
    c ^ 2 + c - b ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfourNe : (4 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 4 (by norm_num)
  have hsixNe : (6 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 6 (by norm_num)
  obtain ⟨h₅, hfive⟩ :=
    five_nsmul_origin_coordinates b c hb hc hbc h00
  intro hA
  have hxfive : tateFiveX b c = 0 := by
    simp [tateFiveX, hA]
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff).mp hxfive with heq | hneg
  · apply hfourNe
    have hfiveEq : (5 : ℕ) • P = P :=
      hfive.trans heq
    have hcancel : (4 : ℕ) • P + P = 0 + P := by
      rw [← show (5 : ℕ) • P = (4 : ℕ) • P + P by abel]
      exact hfiveEq.trans (zero_add P).symm
    exact add_right_cancel hcancel
  · apply hsixNe
    rw [show (6 : ℕ) • P = (5 : ℕ) • P + P by abel]
    rw [hfive, hneg, neg_add_cancel]

private lemma six_numerator_ne_of_marked_order_thirteen
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 13) :
    tateSixNumerator b c ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hfiveNe : (5 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 5 (by norm_num)
  have hsevenNe : (7 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 7 (by norm_num)
  obtain ⟨h₆, hsix⟩ :=
    six_nsmul_origin_coordinates b c hb hc hbc hfiveNumerator h00
  intro hB
  have hxsix : tateSixX b c = 0 := by
    rw [tateSixX_eq_reduced b c hb hc hbc hfiveNumerator]
    simp [hB]
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff).mp hxsix with heq | hneg
  · apply hfiveNe
    have hsixEq : (6 : ℕ) • P = P :=
      hsix.trans heq
    have hcancel : (5 : ℕ) • P + P = 0 + P := by
      rw [← show (6 : ℕ) • P = (5 : ℕ) • P + P by abel]
      exact hsixEq.trans (zero_add P).symm
    exact add_right_cancel hcancel
  · apply hsevenNe
    rw [show (7 : ℕ) • P = (6 : ℕ) • P + P by abel]
    rw [hsix, hneg, neg_add_cancel]

private lemma seven_aux_ne_of_marked_order_thirteen
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (hsixNumerator : tateSixNumerator b c ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 13) :
    tateSevenAux b c ≠ 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hsixNe : (6 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 6 (by norm_num)
  have heightNe : (8 : ℕ) • P ≠ 0 :=
    nsmul_ne_zero_of_marked_order_thirteen P horder 8 (by norm_num)
  obtain ⟨h₇, hseven⟩ :=
    seven_nsmul_origin_coordinates b c hb hc hbc
      hfiveNumerator hsixNumerator h00
  have hxseven : tateSevenX b c ≠ 0 := by
    intro hx
    rcases (WeierstrassCurve.Affine.Point.X_eq_iff).mp hx with heq | hneg
    · apply hsixNe
      have hsevenEq : (7 : ℕ) • P = P :=
        hseven.trans heq
      have hcancel : (6 : ℕ) • P + P = 0 + P := by
        rw [← show (7 : ℕ) • P = (6 : ℕ) • P + P by abel]
        exact hsevenEq.trans (zero_add P).symm
      exact add_right_cancel hcancel
    · apply heightNe
      rw [show (8 : ℕ) • P = (7 : ℕ) • P + P by abel]
      rw [hseven, hneg, neg_add_cancel]
  intro hC
  apply hxseven
  rw [tateSevenX_eq_reduced b c hb hc hbc
    hfiveNumerator hsixNumerator]
  simp [hC]

private lemma orderThirteenPolynomial_eq_zero_of_opposite_multiples
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hfiveNumerator : c ^ 2 + c - b ≠ 0)
    (hsixNumerator : tateSixNumerator b c ≠ 0)
    (h₆ : (tateNormalCurve b c).toAffine.Nonsingular
      (tateSixX b c) (tateSixY b c))
    (h₇ : (tateNormalCurve b c).toAffine.Nonsingular
      (tateSevenX b c) (tateSevenY b c))
    (hopposite :
      WeierstrassCurve.Affine.Point.some
          (tateSevenX b c) (tateSevenY b c) h₇ =
        -WeierstrassCurve.Affine.Point.some
          (tateSixX b c) (tateSixY b c) h₆) :
    orderThirteenPolynomial b c = 0 := by
  let A : ℚ := c ^ 2 + c - b
  let B : ℚ := tateSixNumerator b c
  let C : ℚ := tateSevenAux b c
  have hA : A ≠ 0 := by simpa only [A] using hfiveNumerator
  have hB : B ≠ 0 := by simpa only [B] using hsixNumerator
  rw [WeierstrassCurve.Affine.Point.neg_some] at hopposite
  have hx :
      tateSevenX b c = tateSixX b c :=
    (WeierstrassCurve.Affine.Point.some.injEq
      (tateSevenX b c) (tateSevenY b c) h₇
      (tateSixX b c)
      ((tateNormalCurve b c).toAffine.negY
        (tateSixX b c) (tateSixY b c)) _).mp hopposite |>.1
  rw [tateSevenX_eq_reduced b c hb hc hbc
      hfiveNumerator hsixNumerator,
    tateSixX_eq_reduced b c hb hc hbc hfiveNumerator] at hx
  change -b * c * A * C / B ^ 2 = (b - c) * B / A ^ 2 at hx
  have hscaled :
      (b - c) * B ^ 3 + b * c * A ^ 3 * C = 0 := by
    field_simp [hA, hB] at hx
    linear_combination -hx
  simpa only [orderThirteenPolynomial, A, B, C] using hscaled

/-- Exact order `13` of the marked Tate point forces the denominator-safe
`X₁(13)` parameter polynomial to vanish. -/
theorem orderThirteenPolynomial_eq_zero_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 13) :
    orderThirteenPolynomial b c = 0 := by
  let P : (tateNormalCurve b c).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hc := c_ne_zero_of_marked_order_thirteen b c hb h00 horder
  have hbc := parameters_ne_of_marked_order_thirteen b c hb h00 horder
  have hA :=
    five_numerator_ne_of_marked_order_thirteen b c hb hc hbc h00 horder
  have hB :=
    six_numerator_ne_of_marked_order_thirteen b c hb hc hbc hA h00 horder
  obtain ⟨h₆, hsix⟩ :=
    six_nsmul_origin_coordinates b c hb hc hbc hA h00
  obtain ⟨h₇, hseven⟩ :=
    seven_nsmul_origin_coordinates b c hb hc hbc hA hB h00
  have hthirteen : (13 : ℕ) • P = 0 := by
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero P
  have hsum : (7 : ℕ) • P + (6 : ℕ) • P = 0 := by
    rw [← hthirteen]
    abel
  have hopposite : (7 : ℕ) • P = -((6 : ℕ) • P) :=
    eq_neg_of_add_eq_zero_left hsum
  rw [hsix, hseven] at hopposite
  exact orderThirteenPolynomial_eq_zero_of_opposite_multiples
    b c hb hc hbc hA hB h₆ h₇ hopposite

/-- Substituting `b = rs(r-1)` and `c = s(r-1)` factors the Tate polynomial as
`s⁷(r-1)¹¹` times the reduced polynomial. -/
lemma orderThirteenPolynomial_substitution (r s : ℚ) :
    orderThirteenPolynomial (r * s * (r - 1)) (s * (r - 1)) =
      s ^ 7 * (r - 1) ^ 11 * orderThirteenReducedPolynomial r s := by
  simp only [orderThirteenPolynomial, orderThirteenReducedPolynomial,
    tateSixNumerator, tateSevenAux]
  ring

/-- The forward rational change of variables from the Tate certificate to the
reduced affine model, including the inverse identities needed to justify the
substitution and the inherited noncuspidal conditions. -/
theorem exists_orderThirteen_reduced_certificate
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0) (hbc : b ≠ c)
    (hA : c ^ 2 + c - b ≠ 0)
    (hB : tateSixNumerator b c ≠ 0)
    (hC : tateSevenAux b c ≠ 0)
    (hpoly : orderThirteenPolynomial b c = 0) :
    ∃ r s : ℚ,
      r = b / c ∧ s = c ^ 2 / (b - c) ∧
      r ≠ 0 ∧ r ≠ 1 ∧ s ≠ 0 ∧ s ≠ 1 ∧ r ≠ s ∧
      r * s - 2 * r + 1 ≠ 0 ∧
      b = r * s * (r - 1) ∧ c = s * (r - 1) ∧
      orderThirteenReducedPolynomial r s = 0 := by
  let r : ℚ := b / c
  let s : ℚ := c ^ 2 / (b - c)
  have hbc' : b - c ≠ 0 := sub_ne_zero.mpr hbc
  have hrzero : r ≠ 0 := div_ne_zero hb hc
  have hrone : r ≠ 1 := by
    intro hr
    have : b = c := by
      dsimp only [r] at hr
      field_simp [hc] at hr
      exact hr
    exact hbc this
  have hszero : s ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 hc) hbc'
  have hcsub : c = s * (r - 1) := by
    dsimp only [r, s]
    field_simp [hc, hbc']
  have hbsub : b = r * s * (r - 1) := by
    dsimp only [r, s]
    field_simp [hc, hbc']
  have hAidentity :
      c ^ 2 + c - b = s * (r - 1) ^ 2 * (s - 1) := by
    rw [hbsub, hcsub]
    ring
  have hBone :
      tateSixNumerator b c =
        s ^ 2 * (r - 1) ^ 3 * (r - s) := by
    rw [hbsub, hcsub]
    simp only [tateSixNumerator]
    ring
  have hCone :
      tateSevenAux b c =
        -s ^ 2 * (r - 1) ^ 3 * (r * s - 2 * r + 1) := by
    rw [hbsub, hcsub]
    simp only [tateSevenAux]
    ring
  have hsone : s ≠ 1 := by
    intro hs
    apply hA
    rw [hAidentity, hs]
    ring
  have hrs : r ≠ s := by
    intro hrs
    apply hB
    rw [hBone, hrs]
    ring
  have hCfactor : r * s - 2 * r + 1 ≠ 0 := by
    intro hfactor
    apply hC
    rw [hCone, hfactor]
    ring
  have hsubpoly :
      orderThirteenPolynomial (r * s * (r - 1)) (s * (r - 1)) = 0 := by
    rwa [← hbsub, ← hcsub]
  rw [orderThirteenPolynomial_substitution] at hsubpoly
  have hprefactor : s ^ 7 * (r - 1) ^ 11 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 7 hszero)
      (pow_ne_zero 11 (sub_ne_zero.mpr hrone))
  have hreduced : orderThirteenReducedPolynomial r s = 0 :=
    (mul_eq_zero.mp hsubpoly).resolve_left hprefactor
  exact ⟨r, s, rfl, rfl, hrzero, hrone, hszero, hsone, hrs,
    hCfactor, hbsub, hcsub, hreduced⟩

/-- An exact rational point of order `13` produces both the denominator-safe Tate
certificate and a noncuspidal rational point on the reduced affine `X₁(13)` model. -/
theorem exists_tateOrderThirteen_certificate
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 13) :
    ∃ b c u r s : ℚ,
      u ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧
      c ^ 2 + c - b ≠ 0 ∧
      tateSixNumerator b c ≠ 0 ∧
      tateSevenAux b c ≠ 0 ∧
      orderThirteenPolynomial b c = 0 ∧
      u ^ 12 * E.Δ = tateNormalDiscriminant b c ∧
      r = b / c ∧ s = c ^ 2 / (b - c) ∧
      r ≠ 0 ∧ r ≠ 1 ∧ s ≠ 0 ∧ s ≠ 1 ∧ r ≠ s ∧
      r * s - 2 * r + 1 ≠ 0 ∧
      b = r * s * (r - 1) ∧ c = s * (r - 1) ∧
      orderThirteenReducedPolynomial r s = 0 := by
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
          (tateNormalCurve b c).toAffine.Point) = 13 := by
    rw [← heQ, AddEquiv.addOrderOf_eq]
    exact hQ
  have hc := c_ne_zero_of_marked_order_thirteen b c hb h00 hmarked
  have hbc := parameters_ne_of_marked_order_thirteen b c hb h00 hmarked
  have hA :=
    five_numerator_ne_of_marked_order_thirteen b c hb hc hbc h00 hmarked
  have hB :=
    six_numerator_ne_of_marked_order_thirteen b c hb hc hbc hA h00 hmarked
  have hC :=
    seven_aux_ne_of_marked_order_thirteen b c hb hc hbc hA hB h00 hmarked
  have hpoly :=
    orderThirteenPolynomial_eq_zero_of_marked_order b c hb h00 hmarked
  obtain ⟨r, s, hr, hs, hrzero, hrone, hszero, hsone, hrs,
      hCfactor, hbsub, hcsub, hreduced⟩ :=
    exists_orderThirteen_reduced_certificate
      b c hb hc hbc hA hB hC hpoly
  have hbase : (E⁄ℚ).Δ = E.Δ := by
    simp [WeierstrassCurve.baseChange]
  have hdisc' : u ^ 12 * E.Δ = tateNormalDiscriminant b c := by
    rw [← hbase, hdisc, tateNormalCurve_discriminant]
  exact ⟨b, c, u, r, s, hu, hb, hc, hbc, hA, hB, hC, hpoly,
    hdisc', hr, hs, hrzero, hrone, hszero, hsone, hrs, hCfactor,
    hbsub, hcsub, hreduced⟩

end MazurTorsion.Kubert

end

end


/- Source module: MazurTorsion.Kubert.OrderThirteenModel. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


noncomputable section


/-!
# A hyperelliptic model for the order-thirteen parameter curve

This file gives a checked rational map from the reduced Tate-parameter equation
in `OrderThirteenReduction` to the standard sextic model

`y² = x⁶ + 2x⁵ + x⁴ + 2x³ + 6x² + 4x + 1`.

The map is obtained by elementary completion of the square after resolving the
singular plane model.  Its only denominators are `s-1` and `r-s`; both were
already proved nonzero from exact order in the preceding reduction.

The two rational affine cusp abscissas on the sextic are `0` and `-1`.  The
forward image of an exact-order certificate has neither abscissa: `x = 0`
would discard `r-1` or `s-1`, while `x = -1` would discard the separately
retained factor `rs-2r+1`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The sextic defining the hyperelliptic model of `X₁(13)`. -/
def orderThirteenHyperellipticPolynomial (x : ℚ) : ℚ :=
  x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 +
    6 * x ^ 2 + 4 * x + 1

/-- The hyperelliptic abscissa attached to a reduced Tate certificate. -/
def orderThirteenHyperellipticX (r s : ℚ) : ℚ :=
  -((r - 1) * (s - 1) / (r - s))

/-- The hyperelliptic ordinate attached to a reduced Tate certificate.

Writing `U = (r-1)(s-1)/(r-s)` and `V = (r-s)/(1-s)`, the intermediate
quadratic model is

`V² + (U³-U²-1)V - U² + U = 0`.

Completing its square and replacing `U` by `-x` gives the displayed formula. -/
def orderThirteenHyperellipticY (r s : ℚ) : ℚ :=
  let U := (r - 1) * (s - 1) / (r - s)
  let V := (r - s) / (1 - s)
  2 * V + (U ^ 3 - U ^ 2 - 1)

/-- Cleared polynomial identity underlying the rational map to the sextic. -/
lemma orderThirteen_hyperelliptic_cleared_identity
    (r s : ℚ) (hsone : s ≠ 1) (hrs : r ≠ s) :
    (r - s) ^ 2 * (s - 1) ^ 2 *
        (orderThirteenHyperellipticY r s ^ 2 -
          orderThirteenHyperellipticPolynomial
            (orderThirteenHyperellipticX r s)) =
      4 * (r - 1) * orderThirteenReducedPolynomial r s := by
  simp only [orderThirteenHyperellipticY,
    orderThirteenHyperellipticX,
    orderThirteenHyperellipticPolynomial,
    orderThirteenReducedPolynomial]
  field_simp [sub_ne_zero.mpr hsone, sub_ne_zero.mpr hrs]
  ring

/-- A noncuspidal point on the reduced Tate model maps to the hyperelliptic
sextic. -/
theorem orderThirteen_reduced_to_hyperelliptic
    (r s : ℚ) (hsone : s ≠ 1) (hrs : r ≠ s)
    (hreduced : orderThirteenReducedPolynomial r s = 0) :
    orderThirteenHyperellipticY r s ^ 2 =
      orderThirteenHyperellipticPolynomial
        (orderThirteenHyperellipticX r s) := by
  have hidentity :=
    orderThirteen_hyperelliptic_cleared_identity r s hsone hrs
  rw [hreduced, mul_zero] at hidentity
  have hprefactor : (r - s) ^ 2 * (s - 1) ^ 2 ≠ 0 :=
    mul_ne_zero
      (pow_ne_zero 2 (sub_ne_zero.mpr hrs))
      (pow_ne_zero 2 (sub_ne_zero.mpr hsone))
  exact sub_eq_zero.mp <|
    (mul_eq_zero.mp hidentity).resolve_left hprefactor

lemma orderThirteenHyperellipticX_ne_zero
    (r s : ℚ) (hrone : r ≠ 1) (hsone : s ≠ 1) (hrs : r ≠ s) :
    orderThirteenHyperellipticX r s ≠ 0 := by
  simp only [orderThirteenHyperellipticX]
  exact neg_ne_zero.mpr <|
    div_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr hrone) (sub_ne_zero.mpr hsone))
      (sub_ne_zero.mpr hrs)

lemma orderThirteenHyperellipticX_ne_neg_one
    (r s : ℚ) (hrs : r ≠ s)
    (hfactor : r * s - 2 * r + 1 ≠ 0) :
    orderThirteenHyperellipticX r s ≠ -1 := by
  intro hx
  apply hfactor
  simp only [orderThirteenHyperellipticX] at hx
  field_simp [sub_ne_zero.mpr hrs] at hx
  linear_combination -hx

/-- An exact rational point of order `13` produces an affine rational point on
the standard sextic whose abscissa is neither rational affine cusp abscissa. -/
theorem exists_orderThirteen_hyperelliptic_certificate
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 13) :
    ∃ x y : ℚ,
      y ^ 2 = orderThirteenHyperellipticPolynomial x ∧
      x ≠ 0 ∧ x ≠ -1 := by
  obtain ⟨b, c, u, r, s, hu, hb, hc, hbc, hA, hB, hC, hpoly,
      hdisc, hr, hs, hrzero, hrone, hszero, hsone, hrs, hfactor,
      hbsub, hcsub, hreduced⟩ :=
    exists_tateOrderThirteen_certificate E Q hQ
  let x := orderThirteenHyperellipticX r s
  let y := orderThirteenHyperellipticY r s
  have hcurve : y ^ 2 = orderThirteenHyperellipticPolynomial x := by
    exact orderThirteen_reduced_to_hyperelliptic r s hsone hrs hreduced
  have hxzero : x ≠ 0 :=
    orderThirteenHyperellipticX_ne_zero r s hrone hsone hrs
  have hxnegone : x ≠ -1 :=
    orderThirteenHyperellipticX_ne_neg_one r s hrs hfactor
  exact ⟨x, y, hcurve, hxzero, hxnegone⟩

/-- A route-neutral exclusion of noncuspidal rational points on the
hyperelliptic model rules out exact rational order thirteen. -/
theorem rationalPoint_addOrderOf_ne_thirteen_of_noNoncuspidalPoint
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point)
    (hNoNoncuspidal :
      ∀ x y : ℚ, x ≠ 0 → x ≠ -1 →
        y ^ 2 = orderThirteenHyperellipticPolynomial x → False) :
    addOrderOf Q ≠ 13 := by
  intro hQ
  obtain ⟨x, y, hcurve, hxzero, hxnegone⟩ :=
    exists_orderThirteen_hyperelliptic_certificate E Q hQ
  exact hNoNoncuspidal x y hxzero hxnegone hcurve

end MazurTorsion.Kubert

end

end

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point)
    (hNo : ∀ x y : ℚ, x ≠ 0 → x ≠ -1 →
      y ^ 2 = x ^ 6 + 2 * x ^ 5 + x ^ 4 + 2 * x ^ 3 + 6 * x ^ 2 + 4 * x + 1 → False) :
    addOrderOf Q ≠ 13 := by
  exact MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_thirteen_of_noNoncuspidalPoint
    E Q hNo
#print axioms solution
