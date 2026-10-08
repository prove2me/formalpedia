-- Prove2me | solution 1 for MazurCampaign.no_order_twenty_seven
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:15:13.311843+00:00
-- url     : https://prove2.me/submissions/a47175c6-235e-453f-9a4e-4d6594abeebe

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Definitions.Def_MazurTransfer_OrderTwentySevenLegs
import Definitions.Def_MazurTransfer_OrderTwentySevenTrisectionData
import Theorems.Thm_MazurTransfer_order_twenty_seven_legs_chain_impossible
import Theorems.Thm_MazurTransfer_order27_third_leg_exists


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


/- Source module: MazurTorsion.Kubert.OrderNineReduction. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Reduction of a point of order nine

If the marked point `P = (0, 0)` on Tate normal form has exact order nine,
then `5P = -4P`.  Comparing the already checked fourth- and fifth-multiple
abscissas and clearing only the proved-nonzero denominators gives

`c⁵ + c⁴ + (1-b)c³ - 3bc² + 3b²c - b³ = 0`.

This is the common Tate-parameter certificate used by the order-eighteen
and order-twenty-seven branches.  No rational-point classification of the
resulting parameter curve is asserted here.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The Tate-parameter equation forced by exact order nine of the marked
point. -/
def orderNinePolynomial (b c : ℚ) : ℚ :=
  c ^ 5 + c ^ 4 + (1 - b) * c ^ 3 -
    3 * b * c ^ 2 + 3 * b ^ 2 * c - b ^ 3

lemma c_ne_zero_of_marked_order_nine
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 9) :
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
  obtain ⟨h₃, hthree⟩ :=
    three_nsmul_origin_coordinates b 0 hb h00
  have hneg :
      WeierstrassCurve.Affine.Point.some 0 (b - 0) h₃ = -P := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp)
      (by
        simp [W, tateNormalCurve,
          WeierstrassCurve.Affine.negY])
  apply hfourNe
  rw [show (4 : ℕ) • P = (3 : ℕ) • P + P by abel]
  rw [hthree, hneg, neg_add_cancel]

lemma parameters_ne_of_marked_order_nine
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 9) :
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
  obtain ⟨h₂, htwo⟩ :=
    two_nsmul_origin_coordinates b b hb h00
  obtain ⟨h₃, hthree⟩ :=
    three_nsmul_origin_coordinates b b hb h00
  have hneg :
      WeierstrassCurve.Affine.Point.some b (b * b) h₂ =
        -WeierstrassCurve.Affine.Point.some b (b - b) h₃ := by
    rw [WeierstrassCurve.Affine.Point.neg_some]
    exact WeierstrassCurve.Affine.Point.some_eq_some W
      (by simp)
      (by
        simp [tateNormalCurve,
          WeierstrassCurve.Affine.negY]
        ring)
  apply hfiveNe
  rw [show (5 : ℕ) • P = (2 : ℕ) • P + (3 : ℕ) • P by abel]
  rw [htwo, hthree, hneg, neg_add_cancel]

/-- Exact order nine of the marked Tate point forces
`orderNinePolynomial b c = 0`. -/
theorem orderNinePolynomial_eq_zero_of_marked_order
    (b c : ℚ) (hb : b ≠ 0)
    (h00 : (tateNormalCurve b c).toAffine.Nonsingular 0 0)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 9) :
    orderNinePolynomial b c = 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  have hc :=
    c_ne_zero_of_marked_order_nine b c hb h00 horder
  have hbc :=
    parameters_ne_of_marked_order_nine b c hb h00 horder
  obtain ⟨h₄, hfour⟩ :=
    four_mul_origin_coordinates b c hb hc h00
  obtain ⟨h₅, hfive⟩ :=
    five_nsmul_origin_coordinates b c hb hc hbc h00
  have hfour' :
      (4 : ℕ) • P =
        WeierstrassCurve.Affine.Point.some
          (b * (b - c) / c ^ 2)
          (b ^ 2 * (c ^ 2 + c - b) / c ^ 3) h₄ := by
    rw [show (4 : ℕ) • P = P + P + P + P by abel]
    exact hfour
  have hsum : (5 : ℕ) • P = -((4 : ℕ) • P) := by
    apply eq_neg_of_add_eq_zero_left
    rw [← add_nsmul]
    norm_num
    rw [← horder]
    exact addOrderOf_nsmul_eq_zero P
  rw [hfive, hfour',
    WeierstrassCurve.Affine.Point.neg_some] at hsum
  have hx :
      tateFiveX b c = b * (b - c) / c ^ 2 := by
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at hsum
    exact hsum.1
  simp only [tateFiveX] at hx
  field_simp [hc, sub_ne_zero.mpr hbc] at hx
  simp only [orderNinePolynomial]
  linear_combination hx



end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.Kubert.OrderEighteenModel. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# An explicit genus-two model attached to order eighteen

The order-nine Tate-parameter equation admits the rational parameter

`d = c² / (b - c)`.

Away from the nondegenerate loci already supplied by
`exists_tateOrderEighteen_certificate`, it gives

`c = d²(d - 1)` and `b = c(d² - d + 1)`.

Combining this parametrization with the rational root of the Tate
two-division polynomial gives the auxiliary equation

`(2s + 1)(d²(d - 1)s² - (d² - d + 1)) = s²`.

The displayed rational change of variables then produces a point on

`Y² = X⁶ - 4X⁵ + 10X⁴ - 10X³ + 5X² - 2X + 1`.

This file proves only these algebraic reductions.  In particular, it does
not assert the rational-point classification of this genus-two curve.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The rational parameter on the nondegenerate order-nine Tate curve. -/
def orderNineParameterD (b c : ℚ) : ℚ :=
  c ^ 2 / (b - c)











lemma orderNinePolynomial_eq_difference_form (b c : ℚ) :
    orderNinePolynomial b c =
      c ^ 5 - (b - c) * c ^ 3 - (b - c) ^ 3 := by
  simp only [orderNinePolynomial]
  ring



/-- The nondegenerate order-nine Tate equation has the claimed rational
parametrization. -/
theorem orderNine_parameterization
    (b c : ℚ) (hc : c ≠ 0) (hbc : b ≠ c)
    (hnine : orderNinePolynomial b c = 0) :
    c =
        orderNineParameterD b c ^ 2 *
          (orderNineParameterD b c - 1) ∧
      b =
        c *
          (orderNineParameterD b c ^ 2 -
            orderNineParameterD b c + 1) := by
  let d := orderNineParameterD b c
  have hnine' :
      c ^ 5 - (b - c) * c ^ 3 - (b - c) ^ 3 = 0 := by
    rw [← orderNinePolynomial_eq_difference_form]
    exact hnine
  have hcparam : c = d ^ 2 * (d - 1) := by
    dsimp [d, orderNineParameterD]
    field_simp [sub_ne_zero.mpr hbc]
    ring_nf at hnine' ⊢
    linear_combination -hnine'
  have hbparam : b = c * (d ^ 2 - d + 1) := by
    dsimp [d, orderNineParameterD]
    field_simp [sub_ne_zero.mpr hbc]
    ring_nf at hnine' ⊢
    linear_combination -hnine'
  exact ⟨hcparam, hbparam⟩



















end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenReduction. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The order-twenty-seven family reduction

A rational point of exact order twenty-seven has an order-nine triple,
which normalizes the curve into the rationally parametrized `X₁(9)` Tate
family

`b = f²(f-1)(f²-f+1)`, `c = f²(f-1)`.

This file packages the normalization: the parameter constraints, the
discriminant and `c₄` formulas of the family, the scaling data, and the
transported coordinates of the original point, whose triple is the
marked origin.  It is the ground floor of the order-twenty-seven
hauptmodul tower.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The order-nine Tate parameter values. -/
@[simp] def nineB (f : ℚ) : ℚ := f ^ 2 * (f - 1) * (f ^ 2 - f + 1)

/-- The `c`-parameter of the order-nine Tate normal form. -/
@[simp] def nineC (f : ℚ) : ℚ := f ^ 2 * (f - 1)

/-- The discriminant of the parametrized order-nine family. -/
theorem orderNine_Δ (f : ℚ) :
    (tateNormalCurve (nineB f) (nineC f)).Δ =
      f ^ 9 * (f - 1) ^ 9 * (f ^ 2 - f + 1) ^ 3 *
        (f ^ 3 - 6 * f ^ 2 + 3 * f + 1) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, tateNormalCurve, nineB, nineC]
  ring



/-- Exact order twenty-seven normalizes the curve into the parametrized
order-nine Tate family, carrying the scaling data, the marked image of
the order-nine triple, and the coordinates of the transported point. -/
theorem orderTwentySeven_family_package
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : E.toAffine.Point) (h27 : addOrderOf P = 27) :
    ∃ (f u : ℚ) (_ : f ≠ 0) (_ : f ≠ 1)
      (_ : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0) (_ : u ≠ 0)
      (h00 : (tateNormalCurve (nineB f)
        (nineC f)).toAffine.Nonsingular 0 0)
      (e : E.toAffine.Point ≃+
        (tateNormalCurve (nineB f) (nineC f)).toAffine.Point),
      e ((3 : ℕ) • P) = WeierstrassCurve.Affine.Point.some 0 0 h00 ∧
        u ^ 12 * E.Δ = (tateNormalCurve (nineB f) (nineC f)).Δ ∧
        u ^ 4 * E.c₄ = (tateNormalCurve (nineB f) (nineC f)).c₄ ∧
        addOrderOf (e P) = 27 ∧
        (3 : ℕ) • e P = WeierstrassCurve.Affine.Point.some 0 0 h00 := by
  have h270 : (27 : ℕ) • P = 0 := by
    rw [← h27]
    exact addOrderOf_nsmul_eq_zero P
  have hnot : ∀ n : ℕ, ¬ (27 ∣ n) → (n : ℕ) • P ≠ 0 := by
    intro n hn hzero
    exact hn (h27 ▸ addOrderOf_dvd_of_nsmul_eq_zero hzero)
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
  -- the marked point has exact order nine
  have horder9 : addOrderOf
      (WeierstrassCurve.Affine.Point.some 0 0 h00 :
        (tateNormalCurve b c).toAffine.Point) = 9 := by
    rw [← heQ]
    have hpres : addOrderOf (e ((3 : ℕ) • P)) =
        addOrderOf ((3 : ℕ) • P) := by
      apply Nat.dvd_antisymm
      · exact addOrderOf_map_dvd e.toAddMonoidHom ((3 : ℕ) • P)
      · conv_lhs => rw [← e.symm_apply_apply ((3 : ℕ) • P)]
        exact addOrderOf_map_dvd e.symm.toAddMonoidHom
          (e ((3 : ℕ) • P))
    rw [hpres]
    -- `addOrderOf (3 • P) = 9`
    have h9smul : (9 : ℕ) • ((3 : ℕ) • P) = 0 := by
      rw [← mul_nsmul]
      norm_num
      exact h270
    have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h9smul
    have h30 : (3 : ℕ) • P ≠ 0 := hnot 3 (by norm_num)
    have h3smul : (3 : ℕ) • ((3 : ℕ) • P) ≠ 0 := by
      rw [← mul_nsmul]
      norm_num
      exact hnot 9 (by norm_num)
    have hdvd' : addOrderOf ((3 : ℕ) • P) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
      exact hdvd
    rcases (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp
        hdvd' with ⟨k, hk2, hkval⟩
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl | rfl
    · exfalso
      apply h30
      have hone := addOrderOf_nsmul_eq_zero ((3 : ℕ) • P)
      rw [hkval, pow_zero, one_nsmul] at hone
      exact hone
    · exfalso
      apply h3smul
      have hthree := addOrderOf_nsmul_eq_zero ((3 : ℕ) • P)
      rwa [hkval, pow_one] at hthree
    · rw [hkval]
      norm_num
  -- the order-nine relation and its parametrization
  have hnine := orderNinePolynomial_eq_zero_of_marked_order
    b c hb h00 horder9
  have hc := c_ne_zero_of_marked_order_nine b c hb h00 horder9
  have hbc := parameters_ne_of_marked_order_nine b c hb h00 horder9
  obtain ⟨f, hcparam, hbparam⟩ :
      ∃ f : ℚ, c = f ^ 2 * (f - 1) ∧
        b = c * (f ^ 2 - f + 1) :=
    ⟨orderNineParameterD b c,
      (orderNine_parameterization b c hc hbc hnine).1,
      (orderNine_parameterization b c hc hbc hnine).2⟩
  have hbval : b = nineB f := by
    rw [nineB, hbparam, hcparam]
  have hcval : c = nineC f := by
    rw [nineC]
    exact hcparam
  subst hbval
  subst hcval
  have hf0 : f ≠ 0 := by
    intro h0
    apply hc
    rw [nineC, h0]
    ring
  have hf1 : f ≠ 1 := by
    intro h1
    apply hc
    rw [nineC, h1]
    ring
  have hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0 := by
    intro hzero
    have hΔ0 : (tateNormalCurve (nineB f) (nineC f)).Δ = 0 := by
      rw [orderNine_Δ, hzero, mul_zero]
    have hΔne : (tateNormalCurve (nineB f) (nineC f)).Δ ≠ 0 := by
      rw [← hdisc]
      exact mul_ne_zero (pow_ne_zero 12 hu) E.isUnit_Δ.ne_zero
    exact hΔne hΔ0
  -- transported order of the point itself
  have horder27 : addOrderOf (e P) = 27 := by
    have hpres : addOrderOf (e P) = addOrderOf P := by
      apply Nat.dvd_antisymm
      · exact addOrderOf_map_dvd e.toAddMonoidHom P
      · conv_lhs => rw [← e.symm_apply_apply P]
        exact addOrderOf_map_dvd e.symm.toAddMonoidHom (e P)
    rw [hpres, h27]
  refine ⟨f, u, hf0, hf1, hK, hu, h00, e, heQ, hdisc, hc₄,
    horder27, ?_⟩
  rw [← map_nsmul]
  exact heQ

end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenTrisection. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The trisection condition on the order-nine family

If a rational point of the parametrized `X₁(9)` family triples to the
marked origin, its abscissa is a root of the explicit trisection
polynomial

`T(f, ξ) = ξ·ψ₃(ξ)² - ψ₂²(ξ)·ω(ξ)`.

The proof composes the affine doubling and addition formulas and
eliminates the intermediate coordinates through staged certified
`linear_combination`s: the ordinate of the double is removed first,
the resulting eliminant is reduced modulo the curve equation to a
cubic in the abscissa of the double whose coefficients no longer
involve the ordinate, and the doubling relation clears that abscissa.
A final two-variable polynomial identity recognises the outcome as
`ψ₂² · T`; the two-division value `ψ₂²` is nonzero because the point
is not killed by two.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert



/-- Curve-reduced numerator `ξ·ψ₂² - ψ₃` of the doubling abscissa. -/
private def trisU (f ξ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f - 6) + 18) - 35) + 48)
    - 2 * ξ - 48) + 8 * ξ + 35) + ξ * (-ξ - 16) - 18) + ξ * (3 * ξ + 20) + 6) + ξ * (-4 * ξ - 16)
    - 1) + ξ * (4 * ξ + 8)) + ξ * (-3 * ξ - 2)) + 2 * ξ ^ 2) - ξ ^ 2) + ξ ^ 4

/-- Quadratic coefficient of the curve-reduced tripling cubic. -/
private def trisA₂ (f ξ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f - 6) + 18) - 35) + 48) + ξ
    - 48) - 4 * ξ + 35) + ξ * (5 * ξ + 8) - 18) + ξ * (-15 * ξ - 10) + 6) + ξ * (ξ * (3 * ξ + 20)
    + 8) - 1) + ξ * (ξ * (-18 * ξ - 20) - 4)) + ξ * (ξ * (27 * ξ + 15) + 1)) + ξ ^ 2 * (-30 * ξ - 10
    )) + ξ ^ 2 * (18 * ξ + 5)) + ξ ^ 3 * (13 * ξ + 3)

/-- Linear coefficient of the curve-reduced tripling cubic. -/
private def trisA₁ (f ξ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f - 7) + 3 * ξ
    + 24) - 24 * ξ - 54) + ξ * (3 * ξ + 87) + 89) + ξ * (-27 * ξ - 204) - 114) + ξ * (ξ * (ξ + 93)
    + 348) + 118) + ξ * (ξ * (-12 * ξ - 195) - 450) - 101) + ξ * (ξ * (54 * ξ + 304) + 450) + 72)
    + ξ * (ξ * (-128 * ξ - 370) - 348) - 42) + ξ * (ξ * (225 * ξ + 371) + 207) + 19) + ξ * (ξ * (
    -288 * ξ - 313) - 96) - 6) + ξ * (ξ * (ξ * (7 * ξ + 258) + 209) + 36) + 1) + ξ * (ξ * (ξ * (
    -42 * ξ - 180) - 106) - 12)) + ξ * (ξ * (ξ * (63 * ξ + 90) + 34) + 3)) + ξ ^ 2 * (ξ * (-70 * ξ
    - 44) - 6)) + ξ ^ 2 * (ξ * (42 * ξ + 24) + 3)) + ξ ^ 3 * (ξ * (10 * ξ + 7) + 1)

/-- Constant coefficient of the curve-reduced tripling cubic. -/
private def trisA₀ (f ξ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f
    - 8) + 3 * ξ + 32) - 21 * ξ - 84) + ξ * (3 * ξ + 72) + 160) + ξ * (-21 * ξ - 162) - 232) + ξ * (
    ξ * (ξ + 69) + 267) + 262) + ξ * (ξ * (-9 * ξ - 150) - 342) - 232) + ξ * (ξ * (31 * ξ + 243)
    + 354) + 160) + ξ * (ξ * (-65 * ξ - 306) - 303) - 84) + ξ * (ξ * (100 * ξ + 306) + 216) + 32)
    + ξ * (ξ * (-118 * ξ - 243) - 126) - 8) + ξ * (ξ * (ξ * (ξ + 113) + 153) + 57) + 1) + ξ * (ξ * (
    ξ * (-3 * ξ - 91) - 78) - 18)) + ξ * (ξ * (ξ * (ξ * (-ξ + 4) + 59) + 33) + 3)) + ξ ^ 2 * (ξ * (
    ξ * (6 * ξ - 4) - 30) - 12)) + ξ ^ 2 * (ξ * (ξ * (-9 * ξ + 3) + 10) + 3)) + ξ ^ 3 * (ξ * (10 * ξ
    - 2) - 2)) + ξ ^ 3 * (ξ * (-6 * ξ + 1) + 1)) + ξ ^ 5 * (-3 * ξ - 1)

/-- Intermediate eliminant after removing the ordinate of the double. -/
private def trisG₁ (f ξ η x₂ : ℚ) : ℚ :=
  f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f * (f
    - 8) + 3 * ξ + x₂ + 32) - 21 * ξ - 7 * x₂ - 84) + ξ * (3 * ξ + 3 * x₂ + 72) + 24 * x₂ + 160)
    + ξ * (-13 * ξ - 24 * x₂ - 162) - 8 * η + x₂ * (x₂ - 54) - 232) + ξ * (ξ * (ξ + 3 * x₂ + 21)
    + 87 * x₂ + 267) + 48 * η + x₂ * (-6 * x₂ + 89) + 262) + ξ * (ξ * (3 * ξ - 23 * x₂ - 6) - 20 * η
    - 204 * x₂ - 342) + η * (-4 * x₂ - 144) + x₂ * (18 * x₂ - 114) - 232) + ξ * (ξ * (ξ * (x₂ - 29)
    + 73 * x₂ - 37) + 100 * η + 348 * x₂ + 354) + η * (20 * x₂ + 280) + x₂ * (-35 * x₂ + 118) + 160)
    + ξ * (ξ * (ξ * (3 * ξ - 6 * x₂ + 79) - 15 * η + x₂ * (-x₂ - 147) + 78) + η * (-10 * x₂ - 240)
    - 450 * x₂ - 303) + η * (x₂ * (x₂ - 48) - 384) + x₂ * (48 * x₂ - 101) - 84) + ξ * (ξ * (ξ * (
    -8 * ξ + 6 * x₂ - 136) + 40 * η + x₂ * (8 * x₂ + 228) - 78) + η * (64 * x₂ + 380) + x₂ * (x₂
    + 450) + 216) + η * (24 * η + x₂ * (-8 * x₂ + 76) + 384) + x₂ * (x₂ * (-x₂ - 48) + 72) + 32)
    + ξ * (ξ * (ξ * (5 * ξ - 3 * η + 10 * x₂ + 178) + η * (-6 * x₂ - 25) + x₂ * (-23 * x₂ - 282)
    + 37) + η * (x₂ * (x₂ - 166) - 440) + x₂ * (-4 * x₂ - 348) - 126) + η * (-96 * η + x₂ * (23 * x₂
    - 88) - 280) + x₂ * (x₂ * (4 * x₂ + 35) - 42) - 8) + ξ * (ξ * (ξ * (-6 * ξ - 11 * η - 25 * x₂
    - 191) + η * (42 * x₂ - 25) + x₂ * (46 * x₂ + 291) + 9) + η * (44 * η + x₂ * (-7 * x₂ + 282)
    + 400) + x₂ * (x₂ * (-2 * x₂ + 8) + 207) + 57) + η * (η * (4 * x₂ + 192) + x₂ * (-41 * x₂ + 80)
    + 144) + x₂ * (x₂ * (-8 * x₂ - 18) + 19) + 1) + ξ * (ξ * (ξ * (23 * ξ + 51 * η + 24 * x₂ + 169)
    + η * (-90 * x₂ + 50) + x₂ * (-65 * x₂ - 253) - 30) + η * (-132 * η + x₂ * (15 * x₂ - 340) - 300
    ) + x₂ * (x₂ * (6 * x₂ - 10) - 96) - 18) + η * (η * (-12 * x₂ - 240) + x₂ * (50 * x₂ - 60) - 48)
    + x₂ * (x₂ * (10 * x₂ + 6) - 6)) + ξ * (ξ * (ξ * (ξ * (-4 * ξ + x₂ - 39) - 68 * η + x₂ * (4 * x₂
    - 4) - 113) + η * (19 * η + 120 * x₂ - 25) + x₂ * (x₂ * (-x₂ + 61) + 173) + 25) + η * (η * (
    6 * x₂ + 176) + x₂ * (-20 * x₂ + 282) + 180) + x₂ * (x₂ * (-8 * x₂ + 8) + 36) + 3) + η * (η * (
    x₂ * (-x₂ + 16) + 192) + x₂ * (-41 * x₂ + 36) + 8) + x₂ * (x₂ * (-8 * x₂ - 1) + 1)) + ξ * (ξ * (
    ξ * (ξ * (-4 * ξ + 22 * x₂ + 49) + 90 * η + x₂ * (-20 * x₂ - 26) + 50) + η * (-18 * η - 160 * x₂
    - 25) + x₂ * (x₂ * (2 * x₂ - 43) - 90) - 12) + η * (η * (-36 * x₂ - 176) + x₂ * (18 * x₂ - 166)
    - 80) + x₂ * (x₂ * (8 * x₂ - 4) - 12)) + η * (η * (-32 * η + x₂ * (6 * x₂ - 16) - 96) + x₂ * (
    x₂ * (4 * x₂ + 23) - 16)) + 4 * x₂ ^ 3) + ξ * (ξ * (ξ * (ξ * (20 * ξ - 47 * x₂ - 41) - 107 * η
    + x₂ * (28 * x₂ + 30) - 10) + η * (-21 * η + 146 * x₂ + 40) + x₂ * (x₂ * (-x₂ + 23) + 30) + 3)
    + η * (η * (54 * x₂ + 132) + x₂ * (-7 * x₂ + 64) + 20) + x₂ * (x₂ * (-6 * x₂ + 1) + 3)) + η * (
    η * (64 * η + x₂ * (-9 * x₂ + 12) + 24) + x₂ * (x₂ * (-8 * x₂ - 8) + 4)) - x₂ ^ 3) + ξ * (ξ * (
    ξ * (ξ * (-16 * ξ + 28 * η + 46 * x₂ + 28) + η * (-28 * x₂ + 87) + x₂ * (-32 * x₂ - 24) - 2)
    + η * (2 * η + x₂ * (-4 * x₂ - 122) - 30) + x₂ * (x₂ * (2 * x₂ - 12) - 6)) + η * (η * (-32 * η
    - 60 * x₂ - 88) + x₂ * (x₂ * (4 * x₂ + 3) - 20)) + 4 * x₂ ^ 3) + η * (η * (-64 * η + x₂ * (
    10 * x₂ - 8)) + x₂ ^ 2 * (8 * x₂ + 2))) + ξ * (ξ * (ξ * (ξ * (4 * ξ - 28 * η - 22 * x₂ - 14)
    + η * (28 * x₂ - 39) + x₂ * (20 * x₂ + 14) + 1) + η * (18 * η + x₂ * (4 * x₂ + 70) + 15)
    + x₂ * (x₂ * (-2 * x₂ + 6) + 3)) + η * (η * (32 * η + 36 * x₂ + 44) + x₂ * (x₂ * (-4 * x₂ - 3)
    + 10)) - 2 * x₂ ^ 3) + η * (η * (32 * η + x₂ * (-6 * x₂ + 4)) + x₂ ^ 2 * (-4 * x₂ - 1))) + ξ * (
    ξ * (ξ * (ξ * (ξ * (9 * ξ - 18 * x₂ - 4) - 28 * η + x₂ * (9 * x₂ + 1)) + η * (-28 * η + 28 * x₂
    + 3) + x₂ * (4 * x₂ + 1)) + η * (η * (28 * x₂ + 19) + x₂ * (4 * x₂ + 6)) - x₂ ^ 3) + η * (η * (
    32 * η + x₂ * (4 * x₂ + 6)) + x₂ ^ 2 * (-4 * x₂ - 1))) + η ^ 2 * (16 * η ^ 2 + x₂ ^ 2 * (-4 * x₂
    - 1))

private lemma tris_stage₁ (f ξ η x₂ y₂ : ℚ)
    (hH2 : y₂ * (2 * η + (1 - nineC f) * ξ - nineB f) +
        (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
          2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) * (x₂ - ξ) +
        (η + (1 - nineC f) * x₂ - nineB f) *
          (2 * η + (1 - nineC f) * ξ - nineB f) = 0)
    (hH3 : (y₂ - η) ^ 2 +
        (1 - nineC f) * (y₂ - η) * (x₂ - ξ) -
        (-(nineB f) + x₂ + ξ) * (x₂ - ξ) ^ 2 = 0) :
    trisG₁ f ξ η x₂ = 0 := by
  unfold trisG₁
  simp only [nineB, nineC] at hH2 hH3
  linear_combination
    (2 * η + (1 - f ^ 2 * (f - 1)) * ξ - f ^ 2 * (f - 1) * (f ^ 2 - f + 1)) ^ 2 * hH3 -
    (f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (-f + 4) - 2 * ξ - 8) + 6 * ξ + 10) + ξ * (-ξ - 8)
      - 8) + ξ * (2 * x₂ + 8) + 5 * η - y₂ + 4) + ξ * (3 * ξ - 4 * x₂ - 6) - 10 * η + 2 * y₂
      - 1) + ξ * (-2 * ξ + 6 * η + 4 * x₂ - y₂ + 4) + η * (-x₂ + 10) - 2 * y₂) + ξ * (-6 * η
      - 2 * x₂ + y₂ - 2) + η * (x₂ - 5) + y₂) + ξ * (ξ * (3 * ξ - 3 * x₂ - 1) - 6 * η + y₂)
      + η * (-6 * η + x₂ + 2 * y₂)) * hH2

private lemma tris_reduce (f ξ η x₂ : ℚ)
    (hG1 : trisG₁ f ξ η x₂ = 0)
    (hcurve : η ^ 2 + (1 - nineC f) * ξ * η - nineB f * η -
        ξ ^ 3 + nineB f * ξ ^ 2 = 0) :
    -famTwoDivision f ξ * x₂ ^ 3 + trisA₂ f ξ * x₂ ^ 2 + trisA₁ f ξ * x₂ +
      trisA₀ f ξ = 0 := by
  unfold trisG₁ at hG1
  unfold famTwoDivision trisA₂ trisA₁ trisA₀
  simp only [nineB, nineC] at hcurve
  linear_combination hG1 -
    (f ^ 2 * (f * (f * (f * (f * (f * (f * (f * (8 * f - 32) + 12 * ξ + 4 * x₂ + 64) - 36 * ξ
      - 12 * x₂ - 80) + ξ * (3 * ξ + 6 * x₂ + 48) + x₂ * (-x₂ + 16) + 64) + ξ * (-2 * ξ
      - 36 * x₂ - 48) - 16 * η + x₂ * (6 * x₂ - 16) - 32) + ξ * (-5 * ξ + 54 * x₂ + 36)
      + 32 * η + x₂ * (-9 * x₂ + 12) + 8) + ξ * (2 * ξ - 16 * η - 60 * x₂ - 24) - 32 * η
      + x₂ * (10 * x₂ - 8)) + ξ * (2 * ξ + 16 * η + 36 * x₂ + 12) + 16 * η + x₂ * (-6 * x₂
      + 4)) + ξ * (ξ * (-12 * ξ + 28 * x₂ + 3) + 16 * η + x₂ * (4 * x₂ + 6)) + 16 * η ^ 2
      + x₂ ^ 2 * (-4 * x₂ - 1)) * hcurve

private lemma tris_hx (f ξ η x₂ : ℚ)
    (hH1 : x₂ * (2 * η + (1 - nineC f) * ξ - nineB f) ^ 2 =
        (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
          2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) ^ 2 +
        (1 - nineC f) *
          (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
            2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) *
          (2 * η + (1 - nineC f) * ξ - nineB f) -
        (-(nineB f) + 2 * ξ) *
          (2 * η + (1 - nineC f) * ξ - nineB f) ^ 2)
    (hcurve : η ^ 2 + (1 - nineC f) * ξ * η - nineB f * η -
        ξ ^ 3 + nineB f * ξ ^ 2 = 0) :
    x₂ * famTwoDivision f ξ = trisU f ξ := by
  unfold famTwoDivision trisU
  simp only [nineB, nineC] at hH1 hcurve
  linear_combination hH1 +
    (f ^ 2 * (f * (f * (f * (-f + 6) - 9) + 10) - 6) - 8 * ξ - 4 * x₂ - 1) * hcurve

private lemma tris_cubic_elim (A₂ A₁ A₀ E U x₂ : ℚ)
    (h : -E * x₂ ^ 3 + A₂ * x₂ ^ 2 + A₁ * x₂ + A₀ = 0)
    (hx : x₂ * E = U) :
    -U ^ 3 + A₂ * U ^ 2 + A₁ * U * E + A₀ * E ^ 2 = 0 := by
  linear_combination E ^ 2 * h +
    ((x₂ * E) ^ 2 + x₂ * E * U + U ^ 2 - A₂ * (x₂ * E + U) - A₁ * E) * hx

private lemma tris_main_identity (f ξ : ℚ) :
    -trisU f ξ ^ 3 + trisA₂ f ξ * trisU f ξ ^ 2 +
      trisA₁ f ξ * trisU f ξ * famTwoDivision f ξ +
      trisA₀ f ξ * famTwoDivision f ξ ^ 2 =
    famTwoDivision f ξ * trisectionPoly f ξ := by
  unfold trisU trisA₂ trisA₁ trisA₀ famTwoDivision trisectionPoly
  ring

/-- Tripling to the marked origin forces the trisection polynomial to
vanish. -/
theorem trisectionPoly_eq_zero_of_three_nsmul
    (f ξ η : ℚ)
    (hQ : (tateNormalCurve (nineB f) (nineC f)).toAffine.Nonsingular ξ η)
    (h00 : (tateNormalCurve (nineB f)
      (nineC f)).toAffine.Nonsingular 0 0)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some ξ η hQ :
        (tateNormalCurve (nineB f) (nineC f)).toAffine.Point) = 27)
    (h3Q : (3 : ℕ) •
        (WeierstrassCurve.Affine.Point.some ξ η hQ :
          (tateNormalCurve (nineB f) (nineC f)).toAffine.Point) =
      WeierstrassCurve.Affine.Point.some 0 0 h00) :
    trisectionPoly f ξ = 0 := by
  set P : (tateNormalCurve (nineB f) (nineC f)).toAffine.Point :=
    WeierstrassCurve.Affine.Point.some ξ η hQ with hP
  -- the curve equation
  have hcurve : η ^ 2 + (1 - nineC f) * ξ * η - nineB f * η -
      ξ ^ 3 + nineB f * ξ ^ 2 = 0 := by
    have heq := hQ.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    simp only [tateNormalCurve_a₁, tateNormalCurve_a₂, tateNormalCurve_a₃,
      tateNormalCurve_a₄, tateNormalCurve_a₆] at heq
    linear_combination heq
  -- the point is not killed by two
  have hden : 2 * η + (1 - nineC f) * ξ - nineB f ≠ 0 := by
    intro hzero
    have hvert : η = (tateNormalCurve (nineB f)
        (nineC f)).toAffine.negY ξ η := by
      simp only [WeierstrassCurve.Affine.negY, tateNormalCurve_a₁,
        tateNormalCurve_a₃]
      linarith
    have h2P : P + P = 0 :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_eq hvert
    have h2P' : (2 : ℕ) • P = 0 := by
      rw [two_nsmul]
      exact h2P
    have := addOrderOf_dvd_of_nsmul_eq_zero h2P'
    rw [horder] at this
    omega
  have hvertne : η ≠ (tateNormalCurve (nineB f)
      (nineC f)).toAffine.negY ξ η := by
    intro hvert
    apply hden
    simp only [WeierstrassCurve.Affine.negY, tateNormalCurve_a₁,
      tateNormalCurve_a₃] at hvert
    linarith
  -- doubling data
  have hslope₁ : (tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η =
      (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
          2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) /
        (2 * η + (1 - nineC f) * ξ - nineB f) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hvertne]
    simp only [WeierstrassCurve.Affine.negY, tateNormalCurve_a₁,
      tateNormalCurve_a₂, tateNormalCurve_a₃, tateNormalCurve_a₄,
      nineB, nineC]
    ring
  have hS : (tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η *
      (2 * η + (1 - nineC f) * ξ - nineB f) =
      -2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
        2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η := by
    rw [hslope₁]
    exact div_mul_cancel₀ _ hden
  set x₂ : ℚ := (tateNormalCurve (nineB f) (nineC f)).toAffine.addX ξ ξ
    ((tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η) with hx₂def
  set y₂ : ℚ := (tateNormalCurve (nineB f) (nineC f)).toAffine.addY ξ ξ η
    ((tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η) with hy₂def
  have hdouble : P + P =
      WeierstrassCurve.Affine.Point.some x₂ y₂
        (WeierstrassCurve.Affine.nonsingular_add hQ hQ
          (fun hc ↦ hvertne hc.2)) := by
    rw [hP]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_ne hvertne
  -- coordinates of the double, with the slope kept atomic
  have hx₂val : x₂ =
      (tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η ^ 2 +
        (1 - nineC f) *
          (tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η +
        nineB f - 2 * ξ := by
    rw [hx₂def, WeierstrassCurve.Affine.addX]
    simp only [tateNormalCurve_a₁, tateNormalCurve_a₂]
    ring
  have hy₂val : y₂ =
      -((tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η *
          (x₂ - ξ) + η) -
        (1 - nineC f) * x₂ + nineB f := by
    rw [hy₂def, WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.negAddY, ← hx₂def]
    simp only [WeierstrassCurve.Affine.negY, tateNormalCurve_a₁,
      tateNormalCurve_a₃]
    ring
  -- cleared coordinates of the double
  have hH1 : x₂ * (2 * η + (1 - nineC f) * ξ - nineB f) ^ 2 =
      (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
        2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) ^ 2 +
      (1 - nineC f) *
        (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
          2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) *
        (2 * η + (1 - nineC f) * ξ - nineB f) -
      (-(nineB f) + 2 * ξ) *
        (2 * η + (1 - nineC f) * ξ - nineB f) ^ 2 := by
    rw [hx₂val]
    linear_combination
      ((tateNormalCurve (nineB f) (nineC f)).toAffine.slope ξ ξ η η *
          (2 * η + (1 - nineC f) * ξ - nineB f) +
        (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
          2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) +
        (1 - nineC f) * (2 * η + (1 - nineC f) * ξ - nineB f)) * hS
  have hH2 : y₂ * (2 * η + (1 - nineC f) * ξ - nineB f) +
      (-2 * f ^ 5 * ξ + 4 * f ^ 4 * ξ - 4 * f ^ 3 * ξ + f ^ 3 * η +
        2 * f ^ 2 * ξ - f ^ 2 * η + 3 * ξ ^ 2 - η) * (x₂ - ξ) +
      (η + (1 - nineC f) * x₂ - nineB f) *
        (2 * η + (1 - nineC f) * ξ - nineB f) = 0 := by
    rw [hy₂val]
    linear_combination (-(x₂ - ξ)) * hS
  -- the double is distinct in abscissa from the point
  have hxne : x₂ ≠ ξ := by
    intro hxeq
    have hPP : P + P = P ∨ P + P = -P := by
      rw [hdouble]
      apply WeierstrassCurve.Affine.Point.X_eq_iff.mp
      simpa using hxeq
    rcases hPP with h | h
    · have hP0 : P = 0 := add_right_cancel (h.trans (zero_add P).symm)
      exact WeierstrassCurve.Affine.Point.some_ne_zero hQ (hP ▸ hP0)
    · have h3 : (3 : ℕ) • P = 0 := by
        rw [show (3 : ℕ) • P = P + P + P by abel, h]
        abel
      rw [h3Q] at h3
      exact WeierstrassCurve.Affine.Point.some_ne_zero h00 h3
  -- the triple has abscissa zero
  have hH3 : (y₂ - η) ^ 2 +
      (1 - nineC f) * (y₂ - η) * (x₂ - ξ) -
      (-(nineB f) + x₂ + ξ) * (x₂ - ξ) ^ 2 = 0 := by
    have hxne' : x₂ - ξ ≠ 0 := sub_ne_zero.mpr hxne
    have hS₂ : (tateNormalCurve (nineB f) (nineC f)).toAffine.slope x₂ ξ y₂ η *
        (x₂ - ξ) = y₂ - η := by
      rw [WeierstrassCurve.Affine.slope_of_X_ne hxne]
      exact div_mul_cancel₀ _ hxne'
    have htriple : (3 : ℕ) • P =
        WeierstrassCurve.Affine.Point.some
          ((tateNormalCurve (nineB f) (nineC f)).toAffine.addX x₂ ξ
            ((tateNormalCurve (nineB f) (nineC f)).toAffine.slope x₂ ξ y₂ η))
          ((tateNormalCurve (nineB f) (nineC f)).toAffine.addY x₂ ξ y₂
            ((tateNormalCurve (nineB f) (nineC f)).toAffine.slope x₂ ξ y₂ η))
          (WeierstrassCurve.Affine.nonsingular_add
            (WeierstrassCurve.Affine.nonsingular_add hQ hQ
              (fun hc ↦ hvertne hc.2)) hQ
            (fun hc ↦ hxne hc.1)) := by
      rw [show (3 : ℕ) • P = P + P + P by abel, hdouble]
      exact WeierstrassCurve.Affine.Point.add_of_X_ne hxne
    rw [h3Q] at htriple
    have hx3 : (tateNormalCurve (nineB f) (nineC f)).toAffine.addX x₂ ξ
        ((tateNormalCurve (nineB f) (nineC f)).toAffine.slope x₂ ξ y₂ η) =
        0 := by
      have := (WeierstrassCurve.Affine.Point.some.injEq
        _ _ _ _ _ _).mp htriple.symm
      exact this.1
    rw [WeierstrassCurve.Affine.addX] at hx3
    simp only [tateNormalCurve_a₁, tateNormalCurve_a₂] at hx3
    linear_combination (x₂ - ξ) ^ 2 * hx3 -
      (y₂ - η +
        (tateNormalCurve (nineB f) (nineC f)).toAffine.slope x₂ ξ y₂ η *
          (x₂ - ξ) +
        (1 - nineC f) * (x₂ - ξ)) * hS₂
  -- eliminate the double through the staged certificates
  have hG1 := tris_stage₁ f ξ η x₂ y₂ hH2 hH3
  have hred := tris_reduce f ξ η x₂ hG1 hcurve
  have hx := tris_hx f ξ η x₂ hH1 hcurve
  have hcube := tris_cubic_elim (trisA₂ f ξ) (trisA₁ f ξ) (trisA₀ f ξ)
    (famTwoDivision f ξ) (trisU f ξ) x₂ hred hx
  have key : famTwoDivision f ξ * trisectionPoly f ξ = 0 :=
    (tris_main_identity f ξ).symm.trans hcube
  -- the two-division value is nonzero
  have hE2 : famTwoDivision f ξ ≠ 0 := by
    have hsq : famTwoDivision f ξ =
        (2 * η + (1 - nineC f) * ξ - nineB f) ^ 2 -
          4 * (η ^ 2 + (1 - nineC f) * ξ * η - nineB f * η -
            ξ ^ 3 + nineB f * ξ ^ 2) := by
      unfold famTwoDivision
      simp only [nineB, nineC]
      ring
    rw [hsq, hcurve, mul_zero, sub_zero]
    exact pow_ne_zero 2 hden
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hE2
  · exact h

end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenThirdLeg. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The third hauptmodul leg of the order-twenty-seven tower

The trisection abscissa produces a third leg completing the `X₀(9)` chain after the two family legs.
-/

namespace MazurTorsion.Kubert









/-- The trisection abscissa produces a third leg completing the
`X₀(9)` chain after the two family legs. -/
theorem thirdLeg_exists (f ξ : ℚ) (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0)
    (hT : trisectionPoly f ξ = 0) :
    ∃ s₃ : ℚ, orderNineG9F (a2legN f / a2legD f) s₃ = 0 := by
  exact MazurTransfer.order27_third_leg_exists f ξ hf0 hf1 hK hT


end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.Kubert.OrderTwentySevenEndpoint. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The endgame of the order-twenty-seven tower

On the parametrized `X₁(9)` family the first two hauptmodul legs are
never cuspidal, and the first leg never takes the CM value `-243`: the
would-be CM parameter satisfies a monic integral polynomial of degree
nine with no root modulo two.  Combined with the classification of the
chained `X₀(9)` correspondence, any third leg completing the chain is
impossible.  Producing such a third leg from a rational point of exact
order twenty-seven is the remaining step of the exclusion.
-/

namespace MazurTorsion.Kubert











/-- No rational value can complete the two family legs to a chain of
the Fricke-twisted `X₀(9)` correspondence. -/
theorem legs_chain_impossible (f : ℚ) (hf0 : f ≠ 0) (hf1 : f ≠ 1)
    (hK : f ^ 3 - 6 * f ^ 2 + 3 * f + 1 ≠ 0) (s₃ : ℚ)
    (h2 : orderNineG9F (a2legN f / a2legD f) s₃ = 0) : False := by
  exact MazurTransfer.order_twenty_seven_legs_chain_impossible f hf0 hf1 hK s₃ h2


end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.Kubert.OrderTwentySeven. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# No rational point of order twenty-seven

A point of exact order twenty-seven normalizes into the parametrized
`X₁(9)` Tate family with its triple at the marked origin.  The
trisection certificate places its abscissa on the trisection locus,
which produces a third hauptmodul leg completing the two family legs
to a chain of the Fricke-twisted `X₀(9)` correspondence.  The
classification of that chain leaves only the cusp and the CM point,
and both are impossible for the family legs.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- No rational point of an elliptic curve over `ℚ` has order `27`. -/
theorem no_rational_point_of_order_twentySeven
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (P : E.toAffine.Point) :
    addOrderOf P ≠ 27 := by
  intro h27
  obtain ⟨f, u, hf0, hf1, hK, hu, h00, e, heQ, hdisc, hc₄, horder27, h3Q⟩ :=
    orderTwentySeven_family_package E P h27
  cases hEP : e P with
  | zero =>
    rw [hEP] at horder27
    have h1 : addOrderOf (WeierstrassCurve.Affine.Point.zero :
        (tateNormalCurve (nineB f) (nineC f)).toAffine.Point) = 1 :=
      addOrderOf_zero
    rw [h1] at horder27
    exact absurd horder27 (by norm_num)
  | @some ξ η hQ =>
    rw [hEP] at horder27 h3Q
    have hT := trisectionPoly_eq_zero_of_three_nsmul f ξ η hQ h00 horder27 h3Q
    obtain ⟨s₃, hG2⟩ := thirdLeg_exists f ξ hf0 hf1 hK hT
    exact legs_chain_impossible f hf0 hf1 hK s₃ hG2

/-- Interface form of the order-27 exclusion on the base-changed model. -/
theorem rationalPoint_addOrderOf_ne_twentySeven
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 27 := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  intro hQ
  exact no_rational_point_of_order_twentySeven (E⁄ℚ) Q hQ

end MazurTorsion.Kubert

end

open scoped WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 27 := by
  intro x hx
  have horder : addOrderOf (x : (E⁄ℚ).Point) = addOrderOf x :=
    addOrderOf_injective (AddCommGroup.torsion (E⁄ℚ).Point).subtype
      (AddCommGroup.torsion (E⁄ℚ).Point).subtype_injective x
  exact MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_twentySeven E x (horder.trans hx)

example : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (x : MazurCampaign.RationalTorsion E), addOrderOf x ≠ 27 := solution
#print axioms solution
