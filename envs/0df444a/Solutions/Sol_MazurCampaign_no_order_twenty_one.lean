-- Prove2me | solution 1 for MazurCampaign.no_order_twenty_one
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T11:26:22.97987+00:00
-- url     : https://prove2.me/submissions/dcbbdd04-30d9-4c58-a49c-a93416491f78

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurTransfer_xzero_twenty_one_hauptmodul_values


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


/- Source module: MazurTorsion.Kubert.ThreeNormalForm. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The order-three normal form

A rational point of exact order three normalizes to the marked origin of

`y² + a₁xy + a₃y = x³`

by a translation and a shear alone, so the discriminant and `c₄` are
preserved on the nose.  The associated `X₀(3)` hauptmodul value is

`t₃ = (a₁³ - 27a₃)/a₃`,

and the cleared `j`-identity `(t₃+27)(t₃+3)³·Δ = c₄³·t₃` holds on the
normal form.  This is the three-side input to the composite-level
hauptmodul certificates.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The order-three normal form `y² + a₁xy + a₃y = x³`. -/
def threeNormalCurve (a₁ a₃ : ℚ) : WeierstrassCurve ℚ :=
  ⟨a₁, 0, a₃, 0, 0⟩







/-- The discriminant of the order-three normal form. -/
lemma threeNormalCurve_Δ (a₁ a₃ : ℚ) :
    (threeNormalCurve a₁ a₃).Δ = a₃ ^ 3 * (a₁ ^ 3 - 27 * a₃) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, threeNormalCurve]
  ring

/-- The invariant `c₄` of the order-three normal form. -/
lemma threeNormalCurve_c₄ (a₁ a₃ : ℚ) :
    (threeNormalCurve a₁ a₃).c₄ = a₁ * (a₁ ^ 3 - 24 * a₃) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    threeNormalCurve]
  ring

/-- On a curve with `a₂ = a₄ = 0` and nonvertical tangent at the origin,
vanishing of thrice the origin forces `a₂ = 0` to be complemented by no
condition; conversely, when `3·(0,0) = 0` on a curve with `a₄ = a₆ = 0`
and `a₃ ≠ 0`, the coefficient `a₂` must vanish. -/
lemma a₂_eq_zero_of_three_nsmul_origin_eq_zero
    (W : WeierstrassCurve ℚ) (ha₄ : W.a₄ = 0)
    (ha₃ : W.a₃ ≠ 0) (h00 : W.toAffine.Nonsingular 0 0)
    (htriple :
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 = 0) :
    W.a₂ = 0 := by
  have hvertical : (0 : ℚ) ≠ W.toAffine.negY 0 0 := by
    simp only [WeierstrassCurve.Affine.negY]
    intro h
    apply ha₃
    linarith
  have hslope : W.toAffine.slope 0 0 0 0 = 0 := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hvertical]
    simp only [WeierstrassCurve.Affine.negY, ha₄]
    ring_nf
  have hdouble :
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
          WeierstrassCurve.Affine.Point.some 0 0 h00 =
        -WeierstrassCurve.Affine.Point.some 0 0 h00 := by
    rw [← add_eq_zero_iff_eq_neg]
    exact htriple
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne' hvertical,
    WeierstrassCurve.Affine.Point.neg_some] at hdouble
  have hx :=
    (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hdouble |>.1
  rw [WeierstrassCurve.Affine.addX, hslope] at hx
  linarith [hx]

/-- Normalization of an exact order-three point to the marked origin of the
order-three normal form.  The translation-shear change has `u = 1`, so the
discriminant and `c₄` are preserved exactly. -/
theorem exists_threeNormalCurve
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (P : W.toAffine.Point) (hP0 : P ≠ 0)
    (hP3 : P + P + P = 0) :
    ∃ (a₁ a₃ : ℚ) (_ : a₃ ≠ 0)
      (h00 : (threeNormalCurve a₁ a₃).toAffine.Nonsingular 0 0)
      (e : W.toAffine.Point ≃+ (threeNormalCurve a₁ a₃).toAffine.Point),
      e P = WeierstrassCurve.Affine.Point.some 0 0 h00 ∧
        W.Δ = (threeNormalCurve a₁ a₃).Δ ∧
        W.c₄ = (threeNormalCurve a₁ a₃).c₄ ∧
        W.c₆ = (threeNormalCurve a₁ a₃).c₆ := by
  have hP2 : P + P ≠ 0 := by
    intro h2
    apply hP0
    calc
      P = P + P + P - (P + P) := by abel
      _ = 0 := by rw [hP3, h2, sub_zero]
  obtain ⟨X, Y, hns, hPxy⟩ :
      ∃ (X Y : ℚ) (h : W.toAffine.Nonsingular X Y),
        P = WeierstrassCurve.Affine.Point.some X Y h := by
    rcases hcase : P with _ | ⟨X, Y, h⟩
    · exact absurd (by rw [hcase]; rfl) hP0
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
  have hC₁a₃ne : (C₁ • W).a₃ ≠ 0 := by
    rw [hC₁a₃]
    exact htangentDenom
  have h00₁ : (C₁ • W).toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.nonsingular_zero.mpr
      ⟨hC₁a₆, Or.inl hC₁a₃ne⟩
  have hmap₁ :
      WeierstrassCurve.Affine.Point.equivVariableChange W C₁
          (WeierstrassCurve.Affine.Point.some 0 0 h00₁) = P := by
    rw [WeierstrassCurve.Affine.Point.equivVariableChange_some, hPxy]
    exact WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp [hC₁]) (by simp [hC₁])
  have htriple₁ :
      WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ +
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ = 0 := by
    have := congrArg
      (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm hP3
    rw [map_add, map_add, map_zero] at this
    have hpre :
        (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm P =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [← hmap₁]
      exact (WeierstrassCurve.Affine.Point.equivVariableChange
        W C₁).symm_apply_apply _
    rwa [hpre] at this
  have hC₁a₂ : (C₁ • W).a₂ = 0 :=
    a₂_eq_zero_of_three_nsmul_origin_eq_zero
      (C₁ • W) hC₁a₄ hC₁a₃ne h00₁ htriple₁
  have hcurve :
      C₁ • W = threeNormalCurve (C₁ • W).a₁ (C₁ • W).a₃ := by
    ext <;> simp [threeNormalCurve, hC₁a₂, hC₁a₄, hC₁a₆]
  have hΔ : W.Δ = (C₁ • W).Δ := by
    rw [WeierstrassCurve.variableChange_Δ, hC₁]
    simp
  have hc₄ : W.c₄ = (C₁ • W).c₄ := by
    rw [WeierstrassCurve.variableChange_c₄, hC₁]
    simp
  refine ⟨(C₁ • W).a₁, (C₁ • W).a₃, hC₁a₃ne,
    hcurve ▸ h00₁,
    (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm.trans
      (WeierstrassCurve.Affine.Point.equivOfEq hcurve), ?_, ?_, ?_, ?_⟩
  · have hfirst :
        (WeierstrassCurve.Affine.Point.equivVariableChange W C₁).symm P =
          WeierstrassCurve.Affine.Point.some 0 0 h00₁ := by
      rw [← hmap₁]
      exact (WeierstrassCurve.Affine.Point.equivVariableChange
        W C₁).symm_apply_apply _
    simp only [AddEquiv.trans_apply, hfirst,
      WeierstrassCurve.Affine.Point.equivOfEq_some]
  · rw [hΔ, hcurve]
    rfl
  · rw [hc₄, hcurve]
    rfl
  · have hc₆W : W.c₆ = (C₁ • W).c₆ := by
      rw [WeierstrassCurve.variableChange_c₆, hC₁]
      simp
    rw [hc₆W, hcurve]
    rfl

/-- The cleared `j`-identity for the order-three hauptmodul value on the
normal form: with `t₃ = (a₁³-27a₃)/a₃`,

`(t₃+27)(t₃+3)³ · Δ = c₄³ · t₃`. -/
theorem threeNormal_hauptmodul_identity
    (a₁ a₃ : ℚ) (ha₃ : a₃ ≠ 0) :
    ((a₁ ^ 3 - 27 * a₃) / a₃ + 27) *
        ((a₁ ^ 3 - 27 * a₃) / a₃ + 3) ^ 3 *
        (threeNormalCurve a₁ a₃).Δ =
      (threeNormalCurve a₁ a₃).c₄ ^ 3 *
        ((a₁ ^ 3 - 27 * a₃) / a₃) := by
  rw [threeNormalCurve_Δ, threeNormalCurve_c₄]
  field_simp
  ring

end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.Kubert.OrderSevenParametrization. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# The order-seven Tate parametrization

On Tate normal form the marked origin has order seven exactly when

`b² - bc - c³ = 0`,

and then `d = b/c` parametrizes `X₁(7)`:

`b = d³ - d²`, `c = d² - d`, with `d ∉ {0,1}`.

The discriminant of the parametrized family is
`d⁷(d-1)⁷(d³-8d²+5d+1)`, and the `X₀(7)` hauptmodul value

`t₇ = 49d(d-1)/(d³-8d²+5d+1)`

satisfies the cleared `j`-identity used by the composite-level
hauptmodul certificates.
-/
section
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- On Tate normal form, an origin killed by seven and not by lower
multiples satisfies `b² - bc - c³ = 0` with `c ≠ 0`. -/
theorem orderSeven_tate_relation
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (hP0 : (WeierstrassCurve.Affine.Point.some 0 0 h00 :
      (tateNormalCurve b c).toAffine.Point) ≠ 0)
    (h7 : (7 : ℕ) • (WeierstrassCurve.Affine.Point.some 0 0 h00 :
      (tateNormalCurve b c).toAffine.Point) = 0) :
    c ≠ 0 ∧ b ^ 2 - b * c - c ^ 3 = 0 := by
  set P : (tateNormalCurve b c).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00 with hPdef
  obtain ⟨h₃, htriple⟩ := three_nsmul_origin_coordinates b c hb h00
  have hc : c ≠ 0 := by
    intro hc0
    subst hc0
    have h3eq : (3 : ℕ) • P = -P := by
      rw [htriple, hPdef, WeierstrassCurve.Affine.Point.neg_some]
      exact WeierstrassCurve.Affine.Point.some_eq_some _ rfl
        (by norm_num [WeierstrassCurve.Affine.negY, tateNormalCurve])
    have h4 : (4 : ℕ) • P = 0 := by
      have h4split : (4 : ℕ) • P = (3 : ℕ) • P + P := by abel
      rw [h4split, h3eq]
      abel
    apply hP0
    calc
      P = (2 : ℕ) • ((4 : ℕ) • P) - (7 : ℕ) • P := by abel
      _ = 0 := by rw [h4, h7]; simp
  refine ⟨hc, ?_⟩
  obtain ⟨h₄, hquad⟩ := four_mul_origin_coordinates b c hb hc h00
  have hfour : (4 : ℕ) • P = WeierstrassCurve.Affine.Point.some
      (b * (b - c) / c ^ 2) (b ^ 2 * (c ^ 2 + c - b) / c ^ 3) h₄ := by
    rw [hPdef, show (4 : ℕ) • WeierstrassCurve.Affine.Point.some 0 0 h00 =
      WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 +
        WeierstrassCurve.Affine.Point.some 0 0 h00 by abel]
    exact hquad
  have hthree : (3 : ℕ) • P = WeierstrassCurve.Affine.Point.some
      c (b - c) h₃ := by
    rw [hPdef]
    exact (three_nsmul_origin_coordinates b c hb h00).choose_spec
  have hsum : (4 : ℕ) • P = -((3 : ℕ) • P) := by
    rw [← add_eq_zero_iff_eq_neg]
    calc
      (4 : ℕ) • P + (3 : ℕ) • P = (7 : ℕ) • P := by abel
      _ = 0 := h7
  rw [hfour, hthree, WeierstrassCurve.Affine.Point.neg_some] at hsum
  have hx :=
    (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp hsum |>.1
  have hcleared : b * (b - c) = c ^ 3 := by
    field_simp at hx
    linarith [hx]
  linarith [hcleared]

/-- The order-seven relation is rationally parametrized by `d = b/c`. -/
theorem orderSeven_parametrization
    (b c : ℚ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hrel : b ^ 2 - b * c - c ^ 3 = 0) :
    ∃ d : ℚ, d ≠ 0 ∧ d ≠ 1 ∧
      b = d ^ 3 - d ^ 2 ∧ c = d ^ 2 - d := by
  refine ⟨b / c, div_ne_zero hb hc, ?_, ?_, ?_⟩
  · intro h1
    have hbc : b = c := by
      field_simp at h1
      linarith [h1]
    rw [hbc] at hrel
    have : c ^ 2 * c = 0 := by linarith [hrel]
    exact hc (by
      rcases mul_eq_zero.mp this with h | h
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      · exact h)
  · field_simp
    linear_combination -hrel
  · field_simp
    linear_combination -hrel

/-- The discriminant of the parametrized order-seven family. -/
theorem orderSeven_Δ (d : ℚ) :
    (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ =
      d ^ 7 * (d - 1) ^ 7 * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, tateNormalCurve]
  ring

/-- The invariant `c₄` of the parametrized order-seven family. -/
theorem orderSeven_c₄ (d : ℚ) :
    (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ =
      (d ^ 2 - d + 1) *
        (d ^ 6 - 11 * d ^ 5 + 30 * d ^ 4 - 15 * d ^ 3 -
          10 * d ^ 2 + 5 * d + 1) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    tateNormalCurve]
  ring

/-- The cleared `j`-identity for the order-seven hauptmodul value on the
parametrized family: with `t₇ = 49d(d-1)/(d³-8d²+5d+1)`,

`(t₇²+13t₇+49)(t₇²+245t₇+2401)³ · Δ = c₄³ · t₇⁷`. -/
theorem orderSeven_hauptmodul_identity
    (d : ℚ) (hd0 : d ≠ 0) (hd1 : d ≠ 1)
    (hK : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0) :
    ((49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)) ^ 2 +
          13 * (49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)) + 49) *
        ((49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)) ^ 2 +
          245 * (49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)) +
          2401) ^ 3 *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ =
      (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 *
        (49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1)) ^ 7 := by
  rw [orderSeven_Δ, orderSeven_c₄]
  set K : ℚ := d ^ 3 - 8 * d ^ 2 + 5 * d + 1 with hKdef
  field_simp [hK]
  simp only [hKdef]
  ring

end MazurTorsion.Kubert

end
end


/- Source module: MazurTorsion.NumberTheory.XZeroTwentyOneDescent. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The elementary two-descent boundary for `X₀(21)`

The conductor-`21` elliptic curve

`y² + xy = x³ - 4x - 1`

is a standard model of `X₀(21)`.  Completing the square and making the
integral change of coordinates

`V = 4x + 1`, `W = 8y + 4x`

gives the full rational two-torsion model

`W² = V(V - 9)(V + 7)`.

This file carries out the denominator and local parts of the complete
two-descent on this model.  Every nonzero rational abscissa has one of the
eight squareclasses `±1`, `±3`, `±7`, `±21`.  Two classes are impossible
modulo sixteen, and translation by `(0,0)`, expressed by

`(V,W) ↦ (-63/V, 63W/V²)`,

pairs the other four local branches with them.  The two remaining
homogeneous spaces are

`c² = m⁴ - 2m²n² - 63n⁴`

and

`c² = -3m⁴ - 2m²n² + 21n⁴`.

They are everywhere locally soluble and require genuine infinite descent.
Rather than conceal those global steps, the final rational-point
classification takes their precise primitive classifications as explicit
hypotheses.

The plane equation obtained by eliminating `j` between the classical
`X₀(3)` and `X₀(7)` hauptmoduls is also recorded, together with its four
visible noncuspidal points.  No modular interpretation or birational map
from that plane model is asserted here.
-/

namespace MazurTorsion.XZeroTwentyOne























/-- The denominator-free fibre-product equation for the classical
hauptmoduls on `X₀(3)` and `X₀(7)`. -/
def HauptmodulPair (t₃ t₇ : ℚ) : Prop :=
  (t₃ + 27) * (t₃ + 3) ^ 3 * t₇ ^ 7 =
    t₃ * (t₇ ^ 2 + 13 * t₇ + 49) *
      (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3



















































end MazurTorsion.XZeroTwentyOne

end


/- Source module: MazurTorsion.Kubert.OrderTwentyOneReduction. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The order-twenty-one hauptmodul certificate

A rational point of exact order twenty-one provides a point of exact order
seven and a point of exact order three.  The order-seven multiple
normalizes the curve into the parametrized `X₁(7)` Tate family, and the
order-three multiple further produces the order-three normal form.  Both
normal forms carry cleared `j`-identities for their hauptmodul values, so
the two values satisfy the recorded fibre-product equation of `X₀(3)` and
`X₀(7)`:

`HauptmodulPair t₃ t₇` with `t₃ ≠ 0` and `t₇ ≠ 0`.

The cleared `j`-links back to the original curve are retained for the
final exceptional-`j` exclusions.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- Two cleared hauptmodul `j`-identities against a common curve glue into
the fibre-product equation. -/
theorem hauptmodulPair_of_cleared
    {t₃ t₇ Δ C : ℚ} (hΔ : Δ ≠ 0)
    (h3 : (t₃ + 27) * (t₃ + 3) ^ 3 * Δ = C ^ 3 * t₃)
    (h7 : (t₇ ^ 2 + 13 * t₇ + 49) *
        (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 * Δ = C ^ 3 * t₇ ^ 7) :
    MazurTorsion.XZeroTwentyOne.HauptmodulPair t₃ t₇ := by
  unfold MazurTorsion.XZeroTwentyOne.HauptmodulPair
  apply mul_left_cancel₀ hΔ
  linear_combination t₇ ^ 7 * h3 - t₃ * h7

/-- Exact order twenty-one normalizes the curve into the parametrized
order-seven Tate family, carrying the discriminant and `c₄` scales and the
image of the original point. -/
theorem orderTwentyOne_tate_package
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (h21 : addOrderOf P = 21) :
    ∃ (d u : ℚ) (_ : d ≠ 0) (_ : d ≠ 1) (_ : u ≠ 0)
      (h00 : (tateNormalCurve (d ^ 3 - d ^ 2)
        (d ^ 2 - d)).toAffine.Nonsingular 0 0)
      (e : E.toAffine.Point ≃+
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).toAffine.Point),
      e ((3 : ℕ) • P) = WeierstrassCurve.Affine.Point.some 0 0 h00 ∧
        u ^ 12 * E.Δ =
          (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ ∧
        u ^ 4 * E.c₄ =
          (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ := by
  have h210 : (21 : ℕ) • P = 0 := by
    rw [← h21]
    exact addOrderOf_nsmul_eq_zero P
  have hnot : ∀ n : ℕ, ¬ (21 ∣ n) → (n : ℕ) • P ≠ 0 := by
    intro n hn hzero
    exact hn (h21 ▸ addOrderOf_dvd_of_nsmul_eq_zero hzero)
  have hQ0 : (3 : ℕ) • P ≠ 0 := hnot 3 (by norm_num)
  have hQ2 : (3 : ℕ) • P + (3 : ℕ) • P ≠ 0 := by
    intro h
    exact hnot 6 (by norm_num) (by rw [show (6 : ℕ) • P =
      (3 : ℕ) • P + (3 : ℕ) • P by abel]; exact h)
  have hQ3 : (3 : ℕ) • P + (3 : ℕ) • P + (3 : ℕ) • P ≠ 0 := by
    intro h
    exact hnot 9 (by norm_num) (by rw [show (9 : ℕ) • P =
      (3 : ℕ) • P + (3 : ℕ) • P + (3 : ℕ) • P by abel]; exact h)
  obtain ⟨b, c, u, hu, hb, h00, e, heQ, hdisc, hc₄, -⟩ :=
    exists_tateNormalCurve_scaled E ((3 : ℕ) • P) hQ2 hQ3
  have horigin0 :
      (WeierstrassCurve.Affine.Point.some 0 0 h00 :
        (tateNormalCurve b c).toAffine.Point) ≠ 0 := by
    rw [← heQ]
    intro h
    exact hQ0 (by simpa using e.injective (by simpa using h))
  have h7smul :
      (7 : ℕ) • (WeierstrassCurve.Affine.Point.some 0 0 h00 :
        (tateNormalCurve b c).toAffine.Point) = 0 := by
    rw [← heQ, ← map_nsmul]
    have : (7 : ℕ) • ((3 : ℕ) • P) = (21 : ℕ) • P := by
      rw [← mul_nsmul]
    rw [this, h210, map_zero]
  obtain ⟨hc, hrel⟩ :=
    orderSeven_tate_relation b c hb h00 horigin0 h7smul
  obtain ⟨d, hd0, hd1, hbeq, hceq⟩ :=
    orderSeven_parametrization b c hb hc hrel
  subst hbeq
  subst hceq
  exact ⟨d, u, hd0, hd1, hu, h00, e, heQ, hdisc, hc₄⟩

/-- A rational point of exact order twenty-one produces noncuspidal
rational hauptmodul values satisfying the `X₀(3)`–`X₀(7)` fibre-product
equation, with cleared `j`-links to the ambient curve. -/
theorem exists_hauptmodulPair_of_order_twentyOne
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (h21 : addOrderOf P = 21) :
    ∃ t₃ t₇ : ℚ, t₃ ≠ 0 ∧ t₇ ≠ 0 ∧
      MazurTorsion.XZeroTwentyOne.HauptmodulPair t₃ t₇ ∧
      (t₃ + 27) * (t₃ + 3) ^ 3 * E.Δ = E.c₄ ^ 3 * t₃ ∧
      (t₇ ^ 2 + 13 * t₇ + 49) *
        (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 * E.Δ = E.c₄ ^ 3 * t₇ ^ 7 := by
  have hΔE : E.Δ ≠ 0 := E.isUnit_Δ.ne_zero
  -- the order-seven side
  obtain ⟨d, u, hd0, hd1, hu, h00₇, e₇, -, hdisc₇, hc₄₇⟩ :=
    orderTwentyOne_tate_package E P h21
  have hΔfam :
      (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ =
        d ^ 7 * (d - 1) ^ 7 * (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) :=
    orderSeven_Δ d
  have hK : d ^ 3 - 8 * d ^ 2 + 5 * d + 1 ≠ 0 := by
    intro hzero
    apply hΔE
    have h12 : u ^ 12 * E.Δ = 0 := by
      rw [hdisc₇, hΔfam, hzero, mul_zero]
    rcases mul_eq_zero.mp h12 with h | h
    · exact absurd h (pow_ne_zero 12 hu)
    · exact h
  set t₇ : ℚ :=
    49 * d * (d - 1) / (d ^ 3 - 8 * d ^ 2 + 5 * d + 1) with ht₇def
  have ht₇0 : t₇ ≠ 0 := by
    rw [ht₇def]
    apply div_ne_zero _ hK
    exact mul_ne_zero (mul_ne_zero (by norm_num) hd0)
      (sub_ne_zero.mpr hd1)
  have h7fam := orderSeven_hauptmodul_identity d hd0 hd1 hK
  have h7 : (t₇ ^ 2 + 13 * t₇ + 49) *
      (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 * E.Δ = E.c₄ ^ 3 * t₇ ^ 7 := by
    apply mul_left_cancel₀ (pow_ne_zero 12 hu)
    calc
      u ^ 12 * ((t₇ ^ 2 + 13 * t₇ + 49) *
          (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 * E.Δ) =
          (t₇ ^ 2 + 13 * t₇ + 49) *
            (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 * (u ^ 12 * E.Δ) := by
        ring
      _ = (t₇ ^ 2 + 13 * t₇ + 49) *
            (t₇ ^ 2 + 245 * t₇ + 2401) ^ 3 *
            (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
        rw [hdisc₇]
      _ = (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 *
            t₇ ^ 7 := by
        rw [ht₇def]
        exact h7fam
      _ = (u ^ 4 * E.c₄) ^ 3 * t₇ ^ 7 := by rw [hc₄₇]
      _ = u ^ 12 * (E.c₄ ^ 3 * t₇ ^ 7) := by ring
  -- the order-three side
  have h70 : (7 : ℕ) • P ≠ 0 := by
    intro hzero
    have := addOrderOf_dvd_of_nsmul_eq_zero hzero
    rw [h21] at this
    omega
  have h73 : (7 : ℕ) • P + (7 : ℕ) • P + (7 : ℕ) • P = 0 := by
    rw [show (7 : ℕ) • P + (7 : ℕ) • P + (7 : ℕ) • P =
      (21 : ℕ) • P by abel, ← h21]
    exact addOrderOf_nsmul_eq_zero P
  obtain ⟨a₁, a₃, ha₃, h00₃, e₃, -, hΔ₃, hc₄₃, -⟩ :=
    exists_threeNormalCurve E ((7 : ℕ) • P) h70 h73
  set t₃ : ℚ := (a₁ ^ 3 - 27 * a₃) / a₃ with ht₃def
  have hΔ₃fam : (threeNormalCurve a₁ a₃).Δ =
      a₃ ^ 3 * (a₁ ^ 3 - 27 * a₃) := threeNormalCurve_Δ a₁ a₃
  have hnum : a₁ ^ 3 - 27 * a₃ ≠ 0 := by
    intro hzero
    apply hΔE
    rw [hΔ₃, hΔ₃fam, hzero, mul_zero]
  have ht₃0 : t₃ ≠ 0 := by
    rw [ht₃def]
    exact div_ne_zero hnum ha₃
  have h3fam := threeNormal_hauptmodul_identity a₁ a₃ ha₃
  have h3 : (t₃ + 27) * (t₃ + 3) ^ 3 * E.Δ = E.c₄ ^ 3 * t₃ := by
    rw [hΔ₃, hc₄₃, ht₃def]
    exact h3fam
  exact ⟨t₃, t₇, ht₃0, ht₇0,
    hauptmodulPair_of_cleared hΔE h3 h7, h3, h7⟩

end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.Kubert.OrderTwentyOneExceptionalJ. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The four exceptional `j`-invariants at level twenty-one

The four noncuspidal rational points of `X₀(21)` have

`j ∈ {3375/2, -140625/8, -189613868625/128, -1159088625/2097152}`.

Every numerator is divisible by `5³` while every denominator is a power of
two.  On the order-seven Tate family the invariant `c₄` is the value of the
binary form

`(m² - mn + n²)(m⁶ - 11m⁵n + 30m⁴n² - 15m³n³ - 10m²n⁴ + 5mn⁵ + n⁶)`,

which has no nontrivial zero modulo five.  Consequently
`c₄(d)³ = j₀·Δ(d)` is impossible for every rational `d` and each of the
four exceptional values: a curve carrying a rational point of order seven
never has one of the four exceptional `j`-invariants.
-/

namespace MazurTorsion.Kubert



/-- The homogenized `c₄` of the order-seven family, as a binary form. -/
private def sevenC₄Form (m n : ℤ) : ℤ :=
  (m ^ 2 - m * n + n ^ 2) *
    (m ^ 6 - 11 * m ^ 5 * n + 30 * m ^ 4 * n ^ 2 - 15 * m ^ 3 * n ^ 3 -
      10 * m ^ 2 * n ^ 4 + 5 * m * n ^ 5 + n ^ 6)

/-- The homogenized discriminant of the order-seven family. -/
private def sevenΔForm (m n : ℤ) : ℤ :=
  m ^ 7 * (m - n) ^ 7 *
    (m ^ 3 - 8 * m ^ 2 * n + 5 * m * n ^ 2 + n ^ 3) * n ^ 7

private lemma sevenC₄Form_cube_unit_mod_five :
    ∀ m n q : ZMod 5, q ≠ 0 → (m ≠ 0 ∨ n ≠ 0) →
      q * ((m ^ 2 - m * n + n ^ 2) *
        (m ^ 6 - 11 * m ^ 5 * n + 30 * m ^ 4 * n ^ 2 -
          15 * m ^ 3 * n ^ 3 - 10 * m ^ 2 * n ^ 4 +
          5 * m * n ^ 5 + n ^ 6)) ^ 3 ≠ 0 := by
  decide

/-- Homogenization of the family `c₄` at a reduced fraction. -/
private lemma c₄_homogenize (m n : ℤ) (hn : (n : ℚ) ≠ 0) :
    (tateNormalCurve (((m : ℚ) / n) ^ 3 - ((m : ℚ) / n) ^ 2)
        (((m : ℚ) / n) ^ 2 - ((m : ℚ) / n))).c₄ * (n : ℚ) ^ 8 =
      ((sevenC₄Form m n : ℤ) : ℚ) := by
  rw [orderSeven_c₄]
  unfold sevenC₄Form
  push_cast
  field_simp

/-- Homogenization of the family discriminant at a reduced fraction. -/
private lemma Δ_homogenize (m n : ℤ) (hn : (n : ℚ) ≠ 0) :
    (tateNormalCurve (((m : ℚ) / n) ^ 3 - ((m : ℚ) / n) ^ 2)
        (((m : ℚ) / n) ^ 2 - ((m : ℚ) / n))).Δ * (n : ℚ) ^ 24 =
      ((sevenΔForm m n : ℤ) : ℚ) := by
  rw [orderSeven_Δ]
  unfold sevenΔForm
  push_cast
  field_simp

/-- On the order-seven family, `q·c₄³ = p·Δ` is impossible whenever
`5 ∣ p` and `5 ∤ q`. -/
private lemma no_exceptional_j_of_five_dvd
    (p q : ℤ) (hp : (5 : ℤ) ∣ p) (hq : ¬ (5 : ℤ) ∣ q) (d : ℚ)
    (h : (q : ℚ) *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 =
      (p : ℚ) *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ) :
    False := by
  set m : ℤ := d.num with hm
  set n : ℤ := (d.den : ℤ) with hn
  have hn0 : (n : ℚ) ≠ 0 := by
    rw [hn]
    exact_mod_cast d.den_ne_zero
  have hd : d = (m : ℚ) / n := d.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [hm, hn] using Rat.isCoprime_num_den d
  rw [hd] at h
  -- clear denominators to the integral binary forms
  have hcleared :
      q * sevenC₄Form m n ^ 3 = p * sevenΔForm m n := by
    have hC := c₄_homogenize m n hn0
    have hD := Δ_homogenize m n hn0
    have h24 :
        (q : ℚ) *
            ((tateNormalCurve (((m : ℚ) / n) ^ 3 - ((m : ℚ) / n) ^ 2)
              (((m : ℚ) / n) ^ 2 - ((m : ℚ) / n))).c₄ * (n : ℚ) ^ 8) ^ 3 =
          (p : ℚ) *
            ((tateNormalCurve (((m : ℚ) / n) ^ 3 - ((m : ℚ) / n) ^ 2)
              (((m : ℚ) / n) ^ 2 - ((m : ℚ) / n))).Δ * (n : ℚ) ^ 24) := by
      calc
        (q : ℚ) * _ =
            ((q : ℚ) *
              (tateNormalCurve (((m : ℚ) / n) ^ 3 - ((m : ℚ) / n) ^ 2)
                (((m : ℚ) / n) ^ 2 - ((m : ℚ) / n))).c₄ ^ 3) *
              (n : ℚ) ^ 24 := by ring
        _ = ((p : ℚ) *
              (tateNormalCurve (((m : ℚ) / n) ^ 3 - ((m : ℚ) / n) ^ 2)
                (((m : ℚ) / n) ^ 2 - ((m : ℚ) / n))).Δ) *
              (n : ℚ) ^ 24 := by rw [h]
        _ = (p : ℚ) * _ := by ring
    rw [hC, hD] at h24
    exact_mod_cast h24
  -- reduce modulo five
  have hmod := congrArg (fun z : ℤ ↦ (z : ZMod 5)) hcleared
  simp only [Int.cast_mul, Int.cast_pow] at hmod
  have hp5 : ((p : ZMod 5)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd p 5).mpr hp
  have hq5 : ((q : ZMod 5)) ≠ 0 := by
    intro hz
    exact hq ((ZMod.intCast_zmod_eq_zero_iff_dvd q 5).mp hz)
  -- coprimality prevents both coordinates from vanishing modulo five
  have hnotboth : ((m : ZMod 5) ≠ 0 ∨ (n : ZMod 5) ≠ 0) := by
    by_contra hcon
    push Not at hcon
    have h5m : (5 : ℤ) ∣ m :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd m 5).mp hcon.1
    have h5n : (5 : ℤ) ∣ n :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd n 5).mp hcon.2
    have : IsUnit (5 : ℤ) := hmn.isUnit_of_dvd' h5m h5n
    norm_num [Int.isUnit_iff] at this
  apply sevenC₄Form_cube_unit_mod_five (m : ZMod 5) (n : ZMod 5)
    (q : ZMod 5) hq5 hnotboth
  have hCcast : ((sevenC₄Form m n : ℤ) : ZMod 5) =
      ((m : ZMod 5) ^ 2 - (m : ZMod 5) * (n : ZMod 5) +
        (n : ZMod 5) ^ 2) *
      ((m : ZMod 5) ^ 6 - 11 * (m : ZMod 5) ^ 5 * (n : ZMod 5) +
        30 * (m : ZMod 5) ^ 4 * (n : ZMod 5) ^ 2 -
        15 * (m : ZMod 5) ^ 3 * (n : ZMod 5) ^ 3 -
        10 * (m : ZMod 5) ^ 2 * (n : ZMod 5) ^ 4 +
        5 * (m : ZMod 5) * (n : ZMod 5) ^ 5 + (n : ZMod 5) ^ 6) := by
    unfold sevenC₄Form
    push_cast
    ring
  rw [← hCcast, hmod, hp5, zero_mul]

/-- No curve in the order-seven Tate family has `j = 3375/2`. -/
theorem no_seven_family_j_first (d : ℚ) :
    (2 : ℚ) * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 ≠
      (3375 : ℚ) * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
  intro h
  exact no_exceptional_j_of_five_dvd 3375 2 (by norm_num) (by norm_num) d
    (by exact_mod_cast h)

/-- No curve in the order-seven Tate family has `j = -140625/8`. -/
theorem no_seven_family_j_second (d : ℚ) :
    (8 : ℚ) * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 ≠
      (-140625 : ℚ) *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
  intro h
  exact no_exceptional_j_of_five_dvd (-140625) 8
    (by norm_num) (by norm_num) d (by exact_mod_cast h)

/-- No curve in the order-seven Tate family has `j = -189613868625/128`. -/
theorem no_seven_family_j_third (d : ℚ) :
    (128 : ℚ) * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 ≠
      (-189613868625 : ℚ) *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
  intro h
  exact no_exceptional_j_of_five_dvd (-189613868625) 128
    (by norm_num) (by norm_num) d (by exact_mod_cast h)

/-- No curve in the order-seven Tate family has
`j = -1159088625/2097152`. -/
theorem no_seven_family_j_fourth (d : ℚ) :
    (2097152 : ℚ) *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 ≠
      (-1159088625 : ℚ) *
        (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
  intro h
  exact no_exceptional_j_of_five_dvd (-1159088625) 2097152
    (by norm_num) (by norm_num) d (by exact_mod_cast h)

end MazurTorsion.Kubert

end


/- Source module: MazurTransfer.XZero21PlaneInterface. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

namespace MazurTorsion.XZeroTwentyOne
/-- Boundary: restore the original hauptmodul classification interface from
its exact denominator-free public contract. Named downstream consumer:
the rational order-21 exclusion. -/
theorem hauptmodulPair_t₃_cases {t₃ t₇ : ℚ}
    (h3 : t₃ ≠ 0) (h7 : t₇ ≠ 0) (hpair : HauptmodulPair t₃ t₇) :
    t₃ = -18 ∨ t₃ = -1152 ∨ t₃ = -81 / 2 ∨ t₃ = -81 / 128 :=
  MazurTransfer.xzero_twenty_one_hauptmodul_values t₃ t₇ h3 h7 hpair
end MazurTorsion.XZeroTwentyOne

end


/- Source module: MazurTorsion.Kubert.OrderTwentyOne. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Excluding the exceptional hauptmodul values at order twenty-one

The hauptmodul certificate sends an exact order-21 point to a rational
pair on the `X₀(3)`–`X₀(7)` fibre product with a cleared `j`-link.  When
the `t₃`-value is one of the four noncuspidal values

`-18, -81/2, -1152, -81/128`,

the `j`-link forces one of the four exceptional `j`-equations on the
order-seven Tate family carrying the point, which the mod-five
certificates exclude.  Together with the plane-to-Weierstrass transfer
(the remaining leaf), this closes exact rational order twenty-one.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- An exact order-21 point cannot coexist with a `j`-link at any of the
four noncuspidal `t₃`-values of `X₀(21)`. -/
theorem no_orderTwentyOne_exceptional_t₃
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (h21 : addOrderOf P = 21)
    {t₃ : ℚ}
    (hlink : (t₃ + 27) * (t₃ + 3) ^ 3 * E.Δ = E.c₄ ^ 3 * t₃)
    (hval : t₃ = -18 ∨ t₃ = -81 / 2 ∨ t₃ = -1152 ∨
      t₃ = -81 / 128) : False := by
  obtain ⟨d, u, hd0, hd1, hu, h00₇, e₇, -, hdisc₇, hc₄₇⟩ :=
    orderTwentyOne_tate_package E P h21
  have hscale :
      ∀ p q : ℚ, q * E.c₄ ^ 3 = p * E.Δ →
        q * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 =
          p * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
    intro p q hpq
    calc
      q * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).c₄ ^ 3 =
          q * (u ^ 4 * E.c₄) ^ 3 := by rw [hc₄₇]
      _ = u ^ 12 * (q * E.c₄ ^ 3) := by ring
      _ = u ^ 12 * (p * E.Δ) := by rw [hpq]
      _ = p * (u ^ 12 * E.Δ) := by ring
      _ = p * (tateNormalCurve (d ^ 3 - d ^ 2) (d ^ 2 - d)).Δ := by
        rw [hdisc₇]
  rcases hval with rfl | rfl | rfl | rfl
  · exact no_seven_family_j_first d
      (hscale 3375 2 (by linear_combination (1 / 9 : ℚ) * hlink))
  · exact no_seven_family_j_second d
      (hscale (-140625) 8 (by linear_combination (16 / 81 : ℚ) * hlink))
  · exact no_seven_family_j_third d
      (hscale (-189613868625) 128
        (by linear_combination (1 / 9 : ℚ) * hlink))
  · exact no_seven_family_j_fourth d
      (hscale (-1159088625) 2097152
        (by linear_combination (268435456 / 81 : ℚ) * hlink))

/-- No elliptic curve over `ℚ` has a rational point of exact order
twenty-one. -/
theorem no_rational_point_of_order_twentyOne
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (h21 : addOrderOf P = 21) : False := by
  obtain ⟨t₃, t₇, ht₃0, ht₇0, hpair, h3link, -⟩ :=
    exists_hauptmodulPair_of_order_twentyOne E P h21
  have hcases :=
    MazurTorsion.XZeroTwentyOne.hauptmodulPair_t₃_cases
      ht₃0 ht₇0 hpair
  apply no_orderTwentyOne_exceptional_t₃ E P h21 h3link
  tauto

/-- Interface form of the order-21 exclusion on the base-changed model. -/
theorem rationalPoint_addOrderOf_ne_twentyOne
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 21 := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  intro hQ
  exact no_rational_point_of_order_twentyOne (E⁄ℚ) Q hQ

end MazurTorsion.Kubert

end

open scoped WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 21 := by
  intro x hx
  have horder : addOrderOf (x : (E⁄ℚ).Point) = addOrderOf x :=
    addOrderOf_injective (AddCommGroup.torsion (E⁄ℚ).Point).subtype
      (AddCommGroup.torsion (E⁄ℚ).Point).subtype_injective x
  exact MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_twentyOne E x (horder.trans hx)

example : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (x : MazurCampaign.RationalTorsion E), addOrderOf x ≠ 21 := solution
#print axioms solution
