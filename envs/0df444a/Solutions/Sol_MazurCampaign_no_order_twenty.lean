-- Prove2me | solution 1 for MazurCampaign.no_order_twenty
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T09:27:51.134188+00:00
-- url     : https://prove2.me/submissions/dac13c60-8f4b-473d-aa6e-a85db224520a

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurCampaign_no_two_ten


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


/- Source module: MazurTorsion.EllipticCurve.TwoIsogeny. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The explicit two-isogeny with kernel generated by `(0, 0)`

For the rational Weierstrass curve

`E(a,b) : y² = x(x² + ax + b)`

this file defines the denominator-safe point map to

`E'(a,b) : Y² = X(X² - 2aX + a² - 4b)`.

Away from the kernel its coordinates are

`X = y²/x² = x + a + b/x`,

`Y = y(b - x²)/x²`.

The second coordinate is the negative of the other common convention
`y(1 - b/x²)`.

The exact-pin library has no general isogeny or elliptic-curve-morphism
API.  Accordingly, `pointMapFun` and `dualPointMapFun` are underlying point
functions rather than bundled homomorphisms.  This file proves their
denominator safety, exact kernels, kernel-translation identity, and the
global composition `dualPointMapFun (pointMapFun P) = 2 • P`.  Bundling
`pointMapFun` remains the separate task of proving preservation of the raw
affine chord-and-tangent addition formula in all secant, tangent, and
exceptional-fiber cases.
-/

open WeierstrassCurve

namespace MazurTorsion.TwoIsogeny

open WeierstrassCurve.Affine

section AbstractOrder

variable {A B : Type*} [AddGroup A] [AddGroup B]



end AbstractOrder

/-- A rational Weierstrass model with the two-torsion point `(0,0)`. -/
def sourceCurve (a b : ℚ) : WeierstrassCurve ℚ :=
  ⟨0, a, 0, b, 0⟩

/-- The standard quotient model by the subgroup generated by `(0,0)`. -/
def targetCurve (a b : ℚ) : WeierstrassCurve ℚ :=
  ⟨0, -2 * a, 0, a ^ 2 - 4 * b, 0⟩

lemma sourceCurve_discriminant (a b : ℚ) :
    (sourceCurve a b).Δ = 16 * b ^ 2 * (a ^ 2 - 4 * b) := by
  simp [sourceCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma targetCurve_discriminant (a b : ℚ) :
    (targetCurve a b).Δ =
      256 * b * (a ^ 2 - 4 * b) ^ 2 := by
  simp [targetCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma source_b_ne_zero (a b : ℚ)
    [(sourceCurve a b).IsElliptic] :
    b ≠ 0 := by
  have hs : 16 * b ^ 2 * (a ^ 2 - 4 * b) ≠ 0 := by
    simpa only [sourceCurve_discriminant] using
      (sourceCurve a b).isUnit_Δ.ne_zero
  exact fun hb ↦ hs (by simp [hb])

lemma source_discriminant_factor_ne_zero (a b : ℚ)
    [(sourceCurve a b).IsElliptic] :
    a ^ 2 - 4 * b ≠ 0 := by
  have hs : 16 * b ^ 2 * (a ^ 2 - 4 * b) ≠ 0 := by
    simpa only [sourceCurve_discriminant] using
      (sourceCurve a b).isUnit_Δ.ne_zero
  exact fun hd ↦ hs (by simp [hd])

/-- Nonsingularity of the source implies nonsingularity of its standard
two-isogenous model. -/
noncomputable instance targetCurve_isElliptic
    (a b : ℚ) [(sourceCurve a b).IsElliptic] :
    (targetCurve a b).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero,
    targetCurve_discriminant]
  have hs : 16 * b ^ 2 * (a ^ 2 - 4 * b) ≠ 0 := by
    simpa only [sourceCurve_discriminant] using
      (sourceCurve a b).isUnit_Δ.ne_zero
  have hb : b ≠ 0 := source_b_ne_zero a b
  have hd : a ^ 2 - 4 * b ≠ 0 :=
    source_discriminant_factor_ne_zero a b
  exact mul_ne_zero (mul_ne_zero (by norm_num) hb) (pow_ne_zero 2 hd)

lemma source_equation {a b x y : ℚ}
    (h : (sourceCurve a b).toAffine.Nonsingular x y) :
    y ^ 2 = x * (x ^ 2 + a * x + b) := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [sourceCurve] at heq
  convert heq using 1 <;> ring

lemma target_equation {a b X Y : ℚ}
    (h : (targetCurve a b).toAffine.Nonsingular X Y) :
    Y ^ 2 = X * (X ^ 2 - 2 * a * X + a ^ 2 - 4 * b) := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [targetCurve] at heq
  convert heq using 1 <;> ring

private lemma source_origin_nonsingular
    (a b : ℚ) [(sourceCurve a b).IsElliptic] :
    (sourceCurve a b).toAffine.Nonsingular 0 0 := by
  apply (sourceCurve a b).toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, sourceCurve]

/-- The nonzero rational two-torsion point on the source curve. -/
def sourceOrigin (a b : ℚ) [(sourceCurve a b).IsElliptic] :
    (sourceCurve a b).toAffine.Point :=
  .some 0 0 (source_origin_nonsingular a b)

private lemma target_origin_nonsingular
    (a b : ℚ) [(sourceCurve a b).IsElliptic] :
    (targetCurve a b).toAffine.Nonsingular 0 0 := by
  apply (targetCurve a b).toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, targetCurve]

/-- The visible two-torsion point `(0,0)` on the target curve. -/
def targetOrigin (a b : ℚ) [(sourceCurve a b).IsElliptic] :
    (targetCurve a b).toAffine.Point :=
  .some 0 0 (target_origin_nonsingular a b)

/-- The `X`-coordinate of the explicit isogeny away from its kernel. -/
def mapX (x y : ℚ) : ℚ :=
  y ^ 2 / x ^ 2

/-- The `Y`-coordinate of the explicit isogeny away from its kernel. -/
def mapY (b x y : ℚ) : ℚ :=
  y * (b - x ^ 2) / x ^ 2

lemma mapX_eq {a b x y : ℚ} (hx : x ≠ 0)
    (hcurve : y ^ 2 = x * (x ^ 2 + a * x + b)) :
    mapX x y = x + a + b / x := by
  simp only [mapX]
  field_simp [hx]
  linear_combination hcurve



/-- Direct substitution verifies that the explicit rational functions land
on the target curve. -/
lemma map_equation {a b x y : ℚ} (hx : x ≠ 0)
    (hcurve : y ^ 2 = x * (x ^ 2 + a * x + b)) :
    mapY b x y ^ 2 =
      mapX x y *
        (mapX x y ^ 2 - 2 * a * mapX x y +
          a ^ 2 - 4 * b) := by
  rw [mapX_eq hx hcurve]
  simp only [mapY]
  field_simp [hx]
  rw [hcurve]
  ring

private lemma map_nonsingular {a b x y : ℚ}
    [(sourceCurve a b).IsElliptic]
    (h : (sourceCurve a b).toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    (targetCurve a b).toAffine.Nonsingular
      (mapX x y) (mapY b x y) := by
  apply (targetCurve a b).toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  have hm := map_equation hx (source_equation h)
  simp only [targetCurve]
  convert hm using 1 <;> ring

/-- The denominator-safe underlying point map.  Both the point at infinity
and the affine kernel point `(0,0)` are sent to infinity. -/
noncomputable def pointMapFun (a b : ℚ)
    [(sourceCurve a b).IsElliptic] :
    (sourceCurve a b).toAffine.Point →
      (targetCurve a b).toAffine.Point
  | .zero => .zero
  | .some x y h =>
      if hx : x = 0 then .zero
      else .some (mapX x y) (mapY b x y)
        (map_nonsingular h hx)

@[simp] lemma pointMapFun_zero (a b : ℚ)
    [(sourceCurve a b).IsElliptic] :
    pointMapFun a b 0 = 0 :=
  rfl

@[simp] lemma pointMapFun_sourceOrigin (a b : ℚ)
    [(sourceCurve a b).IsElliptic] :
    pointMapFun a b (sourceOrigin a b) = 0 := by
  simp only [sourceOrigin, pointMapFun]
  change Point.zero = Point.zero
  rfl

lemma pointMapFun_some_of_ne {a b x y : ℚ}
    [(sourceCurve a b).IsElliptic]
    (h : (sourceCurve a b).toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    pointMapFun a b (.some x y h) =
      .some (mapX x y) (mapY b x y)
        (map_nonsingular h hx) := by
  simp [pointMapFun, hx]

lemma source_y_eq_zero_of_x_eq_zero {a b x y : ℚ}
    (h : (sourceCurve a b).toAffine.Nonsingular x y)
    (hx : x = 0) :
    y = 0 := by
  have hcurve := source_equation h
  rw [hx] at hcurve
  norm_num at hcurve
  exact hcurve

lemma pointMapFun_eq_zero_iff {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (P : (sourceCurve a b).toAffine.Point) :
    pointMapFun a b P = 0 ↔
      P = 0 ∨ P = sourceOrigin a b := by
  cases P with
  | zero =>
      change Point.zero = Point.zero ↔
        Point.zero = Point.zero ∨
          Point.zero = sourceOrigin a b
      simp
  | some x y h =>
      by_cases hx : x = 0
      · have hy := source_y_eq_zero_of_x_eq_zero h hx
        subst x
        subst y
        have hP :
            (Point.some 0 0 h :
              (sourceCurve a b).toAffine.Point) =
                sourceOrigin a b := by
          rfl
        rw [hP, pointMapFun_sourceOrigin]
        simp
      · rw [pointMapFun_some_of_ne h hx]
        have hmapne :
            (Point.some (mapX x y) (mapY b x y)
              (map_nonsingular h hx) :
                (targetCurve a b).toAffine.Point) ≠ 0 :=
          Point.some_ne_zero _
        have hPzero :
            (Point.some x y h :
              (sourceCurve a b).toAffine.Point) ≠ 0 :=
          Point.some_ne_zero _
        have hPorigin :
            (Point.some x y h :
              (sourceCurve a b).toAffine.Point) ≠
                sourceOrigin a b := by
          intro horigin
          have hxzero : x = 0 := by
            exact (show x = 0 ∧ y = 0 by
              simpa only [sourceOrigin, Point.some.injEq] using
                horigin).1
          exact hx hxzero
        simp only [hmapne, hPzero, hPorigin, false_or]



@[simp] lemma sourceOrigin_add_self (a b : ℚ)
    [(sourceCurve a b).IsElliptic] :
    sourceOrigin a b + sourceOrigin a b = 0 := by
  simp only [sourceOrigin]
  apply Point.add_self_of_Y_eq
  norm_num [sourceCurve, negY]

lemma pointMapFun_kernel_killed_by_two {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    {P : (sourceCurve a b).toAffine.Point}
    (hP : pointMapFun a b P = 0) :
    (2 : ℕ) • P = 0 := by
  rcases (pointMapFun_eq_zero_iff P).mp hP with rfl | rfl
  · simp
  · simpa only [two_nsmul] using sourceOrigin_add_self a b







/-- The `x`-coordinate of the dual two-isogeny. -/
def dualMapX (X Y : ℚ) : ℚ :=
  Y ^ 2 / (4 * X ^ 2)

/-- The `y`-coordinate of the dual two-isogeny. -/
def dualMapY (a b X Y : ℚ) : ℚ :=
  Y * (a ^ 2 - 4 * b - X ^ 2) / (8 * X ^ 2)

/-- Direct substitution verifies the dual rational functions. -/
lemma dual_map_equation {a b X Y : ℚ} (hX : X ≠ 0)
    (hcurve :
      Y ^ 2 =
        X * (X ^ 2 - 2 * a * X + a ^ 2 - 4 * b)) :
    dualMapY a b X Y ^ 2 =
      dualMapX X Y *
        (dualMapX X Y ^ 2 + a * dualMapX X Y + b) := by
  simp only [dualMapX, dualMapY]
  field_simp [hX]
  rw [hcurve]
  ring

private lemma dual_map_nonsingular {a b X Y : ℚ}
    [(sourceCurve a b).IsElliptic]
    (h : (targetCurve a b).toAffine.Nonsingular X Y)
    (hX : X ≠ 0) :
    (sourceCurve a b).toAffine.Nonsingular
      (dualMapX X Y) (dualMapY a b X Y) := by
  apply (sourceCurve a b).toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  have hm := dual_map_equation hX (target_equation h)
  simp only [sourceCurve]
  convert hm using 1 <;> ring

/-- The denominator-safe underlying point map for the dual isogeny. -/
noncomputable def dualPointMapFun (a b : ℚ)
    [(sourceCurve a b).IsElliptic] :
    (targetCurve a b).toAffine.Point →
      (sourceCurve a b).toAffine.Point
  | .zero => .zero
  | .some X Y h =>
      if hX : X = 0 then .zero
      else .some (dualMapX X Y) (dualMapY a b X Y)
        (dual_map_nonsingular h hX)

@[simp] lemma dualPointMapFun_zero (a b : ℚ)
    [(sourceCurve a b).IsElliptic] :
    dualPointMapFun a b 0 = 0 :=
  rfl

@[simp] lemma dualPointMapFun_targetOrigin (a b : ℚ)
    [(sourceCurve a b).IsElliptic] :
    dualPointMapFun a b (targetOrigin a b) = 0 := by
  simp only [targetOrigin, dualPointMapFun]
  change Point.zero = Point.zero
  rfl

lemma dualPointMapFun_some_of_ne {a b X Y : ℚ}
    [(sourceCurve a b).IsElliptic]
    (h : (targetCurve a b).toAffine.Nonsingular X Y)
    (hX : X ≠ 0) :
    dualPointMapFun a b (.some X Y h) =
      .some (dualMapX X Y) (dualMapY a b X Y)
        (dual_map_nonsingular h hX) := by
  simp [dualPointMapFun, hX]

lemma target_y_eq_zero_of_x_eq_zero {a b X Y : ℚ}
    (h : (targetCurve a b).toAffine.Nonsingular X Y)
    (hX : X = 0) :
    Y = 0 := by
  have hcurve := target_equation h
  rw [hX] at hcurve
  norm_num at hcurve
  exact hcurve



@[simp] lemma targetOrigin_add_self (a b : ℚ)
    [(sourceCurve a b).IsElliptic] :
    targetOrigin a b + targetOrigin a b = 0 := by
  simp only [targetOrigin]
  apply Point.add_self_of_Y_eq
  norm_num [targetCurve, negY]



lemma dualMapX_map {b x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) :
    dualMapX (mapX x y) (mapY b x y) =
      (x ^ 2 - b) ^ 2 / (4 * y ^ 2) := by
  simp only [dualMapX, mapX, mapY]
  field_simp [hx, hy]
  ring



private lemma source_y_ne_negY {a b x y : ℚ} (hy : y ≠ 0) :
    y ≠ (sourceCurve a b).toAffine.negY x y := by
  intro h
  simp only [sourceCurve, negY] at h
  apply hy
  linarith

private lemma source_duplication_identity_algebra
    {a b x y x₂ : ℚ} (hy : y ≠ 0)
    (hcurve : y ^ 2 = x * (x ^ 2 + a * x + b))
    (hx₂ :
      x₂ =
        ((3 * x ^ 2 + 2 * a * x + b) / (2 * y)) ^ 2 -
          a - 2 * x) :
    x₂ * (2 * y) ^ 2 = (x ^ 2 - b) ^ 2 := by
  rw [hx₂]
  field_simp [hy]
  linear_combination -4 * (a + 2 * x) * hcurve

lemma source_doubleX {a b x y : ℚ}
    (h : (sourceCurve a b).toAffine.Nonsingular x y)
    (hy : y ≠ 0) :
    (sourceCurve a b).toAffine.addX x x
        ((sourceCurve a b).toAffine.slope x x y y) =
      (x ^ 2 - b) ^ 2 / (4 * y ^ 2) := by
  have hcurve := source_equation h
  have hx₂ :
      (sourceCurve a b).toAffine.addX x x
          ((sourceCurve a b).toAffine.slope x x y y) =
        ((3 * x ^ 2 + 2 * a * x + b) / (2 * y)) ^ 2 -
          a - 2 * x := by
    rw [(sourceCurve a b).toAffine.slope_of_Y_ne rfl
      (source_y_ne_negY hy)]
    simp [sourceCurve, negY, addX]
    ring
  have hid :=
    source_duplication_identity_algebra hy hcurve hx₂
  rw [eq_div_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))]
  convert hid using 1
  all_goals ring

lemma source_doubleY {a b x y : ℚ}
    (h : (sourceCurve a b).toAffine.Nonsingular x y)
    (hy : y ≠ 0) :
    (sourceCurve a b).toAffine.addY x x y
        ((sourceCurve a b).toAffine.slope x x y y) =
      dualMapY a b (mapX x y) (mapY b x y) := by
  have hcurve := source_equation h
  have hx : x ≠ 0 := by
    intro hx
    rw [hx] at hcurve
    norm_num at hcurve
    exact hy hcurve
  rw [(sourceCurve a b).toAffine.slope_of_Y_ne rfl
    (source_y_ne_negY hy)]
  simp only [sourceCurve, negY, addY, negAddY, addX,
    dualMapY, mapX, mapY]
  field_simp [hx, hy]
  linear_combination
    8 * y ^ 3 *
      (8 * a ^ 2 * x ^ 3 + 5 * a * b * x ^ 2 +
        27 * a * x ^ 4 + b ^ 2 * x + 4 * b * x ^ 3 +
        b * y ^ 2 + 27 * x ^ 5 - 9 * x ^ 2 * y ^ 2) *
        hcurve

/-- The explicit dual composed with the explicit two-isogeny is
multiplication by two on rational points. -/
theorem dualPointMapFun_comp_pointMapFun {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (P : (sourceCurve a b).toAffine.Point) :
    dualPointMapFun a b (pointMapFun a b P) =
      (2 : ℕ) • P := by
  cases P with
  | zero =>
      change Point.zero = (2 : ℕ) •
        (Point.zero : (sourceCurve a b).toAffine.Point)
      rfl
  | some x y h =>
      by_cases hx : x = 0
      · have hy := source_y_eq_zero_of_x_eq_zero h hx
        subst x
        subst y
        have hP :
            (Point.some 0 0 h :
              (sourceCurve a b).toAffine.Point) =
                sourceOrigin a b := by
          rfl
        rw [hP, pointMapFun_sourceOrigin,
          dualPointMapFun_zero, two_nsmul,
          sourceOrigin_add_self]
      · by_cases hy : y = 0
        · have himage :
              pointMapFun a b
                  (Point.some x y h :
                    (sourceCurve a b).toAffine.Point) =
                targetOrigin a b := by
            rw [pointMapFun_some_of_ne h hx]
            rw [targetOrigin]
            simp only [Point.some.injEq]
            subst y
            simp [mapX, mapY]
          rw [himage, dualPointMapFun_targetOrigin, two_nsmul]
          symm
          apply Point.add_self_of_Y_eq
          simp [sourceCurve, negY, hy]
        · have hmapX : mapX x y ≠ 0 := by
            exact div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx)
          rw [pointMapFun_some_of_ne h hx,
            dualPointMapFun_some_of_ne _ hmapX,
            two_nsmul,
            Point.add_self_of_Y_ne (source_y_ne_negY hy)]
          simp only [Point.some.injEq]
          constructor
          · exact (dualMapX_map hx hy).trans
              (source_doubleX h hy).symm
          · exact (source_doubleY h hy).symm

end MazurTorsion.TwoIsogeny

end


/- Source module: MazurTorsion.GroupTheory.IndependentCyclicGenerators. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Embeddings from independent cyclic generators

This file packages a small group-theoretic construction used after an
explicit two-isogeny.  A point `P` of exact order two and a point `Q` of
exact order `n` generate an embedded `ZMod 2 × ZMod n` as soon as `P`
does not lie in the cyclic subgroup generated by `Q`.
-/

namespace MazurTorsion.IndependentCyclicGenerators

variable {G : Type*} [AddCommGroup G]

/-- The homomorphism from `ZMod n` which sends `1` to `P`. -/
def zmodHom (n : ℕ) (P : G) (hP : n • P = 0) :
    ZMod n →+ G :=
  ZMod.lift n
    ⟨
      { toFun := fun z : ℤ => z • P
        map_zero' := zero_zsmul P
        map_add' := fun a b => add_zsmul P a b },
      by simpa using hP⟩

@[simp] theorem zmodHom_intCast
    (n : ℕ) (P : G) (hP : n • P = 0) (z : ℤ) :
    zmodHom n P hP (z : ZMod n) = z • P := by
  simp [zmodHom]

@[simp] theorem zmodHom_one
    (n : ℕ) (P : G) (hP : n • P = 0) :
    zmodHom n P hP 1 = P := by
  simpa using zmodHom_intCast n P hP 1

/-- Exact order makes the cyclic-generator homomorphism injective. -/
theorem zmodHom_injective
    (n : ℕ) (P : G) (hP : n • P = 0)
    (horder : addOrderOf P = n) :
    Function.Injective (zmodHom n P hP) := by
  change Function.Injective (ZMod.lift n _)
  rw [ZMod.lift_injective]
  intro z hz
  change z • P = 0 at hz
  apply (CharP.intCast_eq_zero_iff (ZMod n) n z).2
  rw [← horder]
  exact (addOrderOf_dvd_iff_zsmul_eq_zero).2 hz

/-- The sum of the two cyclic-generator maps. -/
def productHom
    (P Q : G) (hP : (2 : ℕ) • P = 0)
    (n : ℕ) (hQ : n • Q = 0) :
    ZMod 2 × ZMod n →+ G :=
  (zmodHom 2 P hP).coprod (zmodHom n Q hQ)

@[simp] theorem productHom_apply
    (P Q : G) (hP : (2 : ℕ) • P = 0)
    (n : ℕ) (hQ : n • Q = 0)
    (z : ZMod 2 × ZMod n) :
    productHom P Q hP n hQ z =
      zmodHom 2 P hP z.1 + zmodHom n Q hQ z.2 :=
  rfl

private theorem zmodHom_mem_zmultiples
    (n : ℕ) (Q : G) (hQ : n • Q = 0)
    (z : ZMod n) :
    zmodHom n Q hQ z ∈ AddSubgroup.zmultiples Q := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  rw [zmodHom_intCast]
  exact AddSubgroup.zsmul_mem_zmultiples Q k

/-- The product map is injective when the order-two generator is not in
the cyclic subgroup generated by the other generator. -/
theorem productHom_injective
    (P Q : G)
    (hPorder : addOrderOf P = 2)
    (n : ℕ) (hQorder : addOrderOf Q = n)
    (hindependent : P ∉ AddSubgroup.zmultiples Q) :
    Function.Injective
      (productHom P Q
        (addOrderOf_dvd_iff_nsmul_eq_zero.mp
          (hPorder ▸ dvd_rfl))
        n
        (addOrderOf_dvd_iff_nsmul_eq_zero.mp
          (hQorder ▸ dvd_rfl))) := by
  let hP : (2 : ℕ) • P = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp
      (hPorder ▸ dvd_rfl)
  let hQ : n • Q = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp
      (hQorder ▸ dvd_rfl)
  let fP : ZMod 2 →+ G := zmodHom 2 P hP
  let fQ : ZMod n →+ G := zmodHom n Q hQ
  let f : ZMod 2 × ZMod n →+ G := fP.coprod fQ
  have hfker : f.ker = ⊥ := by
    apply (AddSubgroup.eq_bot_iff_forall f.ker).mpr
    rintro ⟨i, j⟩ hij
    have hsum : fP i + fQ j = 0 := by
      simpa only [AddMonoidHom.mem_ker, f,
        AddMonoidHom.coprod_apply] using hij
    have hfi_mem :
        fP i ∈ AddSubgroup.zmultiples Q := by
      have hfj_mem :
          fQ j ∈ AddSubgroup.zmultiples Q := by
        exact zmodHom_mem_zmultiples n Q hQ j
      have hneg_mem :
          -fQ j ∈ AddSubgroup.zmultiples Q :=
        (AddSubgroup.zmultiples Q).neg_mem hfj_mem
      rw [eq_neg_of_add_eq_zero_left hsum]
      exact hneg_mem
    have hi : i = 0 := by
      by_contra hi
      have hi_one : i = 1 :=
        Fin.eq_one_of_ne_zero i hi
      apply hindependent
      simpa only [fP, hi_one, zmodHom_one] using hfi_mem
    have hj : j = 0 := by
      apply (zmodHom_injective n Q hQ hQorder)
      rw [map_zero]
      simpa only [hi, map_zero, zero_add] using hsum
    exact Prod.ext hi hj
  exact (AddMonoidHom.ker_eq_bot_iff f).mp hfker

/-- Existence form suited to a `ForbidsEmbedding` contradiction. -/
theorem exists_embedding
    (P Q : G)
    (hPorder : addOrderOf P = 2)
    (n : ℕ) (hQorder : addOrderOf Q = n)
    (hindependent : P ∉ AddSubgroup.zmultiples Q) :
    ∃ f : ZMod 2 × ZMod n →+ G, Function.Injective f := by
  let hP : (2 : ℕ) • P = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp
      (hPorder ▸ dvd_rfl)
  let hQ : n • Q = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp
      (hQorder ▸ dvd_rfl)
  exact
    ⟨productHom P Q hP n hQ,
      productHom_injective P Q hPorder n hQorder
        hindependent⟩

/-- In a cyclic group of exact order `2n`, the sole nonzero point killed
by two is the `n`-multiple of a generator.  Consequently, any other point
of exact order two is outside that cyclic subgroup. -/
theorem orderTwo_not_mem_zmultiples
    (P Q : G) (n : ℕ)
    (hPorder : addOrderOf P = 2)
    (hQorder : addOrderOf Q = 2 * n)
    (hhalf : P ≠ n • Q) :
    P ∉ AddSubgroup.zmultiples Q := by
  have hP0 : P ≠ 0 := by
    intro hP
    rw [hP, addOrderOf_zero] at hPorder
    norm_num at hPorder
  have hPtwo : (2 : ℕ) • P = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp
      (hPorder ▸ dvd_rfl)
  have hQtwoN : (2 * n : ℕ) • Q = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp
      (hQorder ▸ dvd_rfl)
  have hStwo : (2 : ℤ) • (n • Q) = 0 := by
    rw [show (2 : ℤ) = (2 : ℕ) by norm_num,
      natCast_zsmul]
    simpa only [Nat.mul_comm, mul_nsmul] using hQtwoN
  intro hmem
  obtain ⟨k, hk⟩ :=
    AddSubgroup.mem_zmultiples_iff.mp hmem
  have htwice : (2 * k : ℤ) • Q = 0 := by
    calc
      (2 * k : ℤ) • Q = (2 : ℤ) • (k • Q) := by
        rw [mul_zsmul]
      _ = (2 : ℤ) • P := by rw [hk]
      _ = (2 : ℕ) • P := by
        norm_num only [ofNat_zsmul]
      _ = 0 := hPtwo
  have hdiv : ((2 * n : ℕ) : ℤ) ∣ 2 * k := by
    rw [← hQorder]
    exact
      (addOrderOf_dvd_iff_zsmul_eq_zero).2 htwice
  have hnDiv : (n : ℤ) ∣ k := by
    apply
      (mul_dvd_mul_iff_left
        (show (2 : ℤ) ≠ 0 by norm_num)).mp
    exact_mod_cast hdiv
  obtain ⟨l, hl⟩ := hnDiv
  have hP_eq : P = l • (n • Q) := by
    calc
      P = k • Q := hk.symm
      _ = ((n : ℤ) * l) • Q := by rw [hl]
      _ = l • (n • Q) := by
        rw [mul_comm, mul_zsmul]
        norm_num
  obtain ⟨r, hr | hr⟩ := Int.even_or_odd' l
  · apply hP0
    calc
      P = l • (n • Q) := hP_eq
      _ = (2 * r : ℤ) • (n • Q) := by rw [hr]
      _ = (r * 2 : ℤ) • (n • Q) := by
        rw [Int.mul_comm 2 r]
      _ = r • ((2 : ℤ) • (n • Q)) :=
        mul_zsmul (n • Q) r 2
      _ = 0 := by rw [hStwo, smul_zero]
  · apply hhalf
    calc
      P = l • (n • Q) := hP_eq
      _ = (2 * r + 1 : ℤ) • (n • Q) := by rw [hr]
      _ = (2 * r : ℤ) • (n • Q) + n • Q := by
        rw [add_zsmul, one_zsmul]
      _ = (r * 2 : ℤ) • (n • Q) + n • Q := by
        rw [Int.mul_comm 2 r]
      _ = r • ((2 : ℤ) • (n • Q)) + n • Q := by
        rw [mul_zsmul]
      _ = n • Q := by rw [hStwo, smul_zero, zero_add]

end MazurTorsion.IndependentCyclicGenerators

end


/- Source module: MazurTorsion.EllipticCurve.TwoIsogenyMultiples. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Fixed-multiple compatibility for the explicit two-isogeny

This file derives the compatibility of `pointMapFun` with small fixed
multiples.  The key observation for doubling is that the composite in the
opposite order is another instance of the already proved composite formula,
after replacing `(a,b)` by `(-2a,a²-4b)`.
-/

open WeierstrassCurve

namespace MazurTorsion.TwoIsogeny

open WeierstrassCurve.Affine

noncomputable local instance transformedSource_isElliptic
    (a b : ℚ) [(sourceCurve a b).IsElliptic] :
    (sourceCurve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic := by
  change (targetCurve a b).IsElliptic
  infer_instance

private def targetAsTransformedSource (a b : ℚ) :
    (targetCurve a b).toAffine.Point →
      (sourceCurve (-2 * a) (a ^ 2 - 4 * b)).toAffine.Point
  | .zero => .zero
  | .some X Y h =>
      .some X Y (by simpa [sourceCurve, targetCurve] using h)

private lemma targetAsTransformedSource_eq (a b : ℚ)
    (Q : (targetCurve a b).toAffine.Point) :
    targetAsTransformedSource a b Q = Q := by
  cases Q <;> rfl

private lemma pointMapFun_dualPointMapFun_eq_transformed_comp
    {a b : ℚ} [(sourceCurve a b).IsElliptic]
    (Q : (targetCurve a b).toAffine.Point) :
    targetAsTransformedSource a b
        (pointMapFun a b (dualPointMapFun a b Q)) =
      dualPointMapFun (-2 * a) (a ^ 2 - 4 * b)
        (pointMapFun (-2 * a) (a ^ 2 - 4 * b)
          (targetAsTransformedSource a b Q)) := by
  cases Q with
  | zero => rfl
  | some X Y h =>
      by_cases hX : X = 0
      · subst X
        have hY : Y = 0 :=
          target_y_eq_zero_of_x_eq_zero h rfl
        subst Y
        rfl
      · have h' :
            (sourceCurve (-2 * a) (a ^ 2 - 4 * b)).toAffine.Nonsingular
              X Y := by
          simpa [sourceCurve, targetCurve] using h
        by_cases hY : Y = 0
        · subst Y
          rw [dualPointMapFun_some_of_ne h hX]
          simp [targetAsTransformedSource, dualMapX, pointMapFun,
            dualPointMapFun, mapX, hX]
        · have hmapX : mapX X Y ≠ 0 :=
            div_ne_zero (pow_ne_zero 2 hY) (pow_ne_zero 2 hX)
          have hdualX : dualMapX X Y ≠ 0 :=
            div_ne_zero (pow_ne_zero 2 hY)
              (mul_ne_zero (by norm_num) (pow_ne_zero 2 hX))
          rw [dualPointMapFun_some_of_ne h hX,
            pointMapFun_some_of_ne _ hdualX,
            show pointMapFun (-2 * a) (a ^ 2 - 4 * b)
                (targetAsTransformedSource a b
                  (.some X Y h)) =
                .some (mapX X Y) (mapY (a ^ 2 - 4 * b) X Y) _ by
              simpa only [targetAsTransformedSource] using
                pointMapFun_some_of_ne h' hX,
            dualPointMapFun_some_of_ne _ hmapX]
          simp only [targetAsTransformedSource, Point.some.injEq]
          constructor <;>
            simp only [mapX, mapY, dualMapX, dualMapY] <;>
            field_simp [hX, hY] <;>
            ring

theorem pointMapFun_comp_dualPointMapFun {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (Q : (targetCurve a b).toAffine.Point) :
    pointMapFun a b (dualPointMapFun a b Q) =
      (2 : ℕ) • Q := by
  have hcomp :=
    pointMapFun_dualPointMapFun_eq_transformed_comp Q
  rw [dualPointMapFun_comp_pointMapFun] at hcomp
  rw [targetAsTransformedSource_eq a b _,
    targetAsTransformedSource_eq a b Q] at hcomp
  exact hcomp

theorem pointMapFun_two_nsmul {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (P : (sourceCurve a b).toAffine.Point) :
    pointMapFun a b ((2 : ℕ) • P) =
      (2 : ℕ) • pointMapFun a b P := by
  rw [← dualPointMapFun_comp_pointMapFun P,
    pointMapFun_comp_dualPointMapFun]

theorem dualPointMapFun_two_nsmul {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (Q : (targetCurve a b).toAffine.Point) :
    dualPointMapFun a b ((2 : ℕ) • Q) =
      (2 : ℕ) • dualPointMapFun a b Q := by
  rw [← pointMapFun_comp_dualPointMapFun Q,
    dualPointMapFun_comp_pointMapFun]

theorem pointMapFun_pow_two_nsmul {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (n : ℕ) (P : (sourceCurve a b).toAffine.Point) :
    pointMapFun a b ((2 ^ n : ℕ) • P) =
      (2 ^ n : ℕ) • pointMapFun a b P := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow : (2 ^ (n + 1) : ℕ) = 2 * 2 ^ n := by
        rw [pow_succ, Nat.mul_comm]
      calc
        pointMapFun a b ((2 ^ (n + 1) : ℕ) • P) =
            pointMapFun a b
              ((2 : ℕ) • ((2 ^ n : ℕ) • P)) := by
          rw [hpow, mul_nsmul]
          rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]
        _ = (2 : ℕ) •
            pointMapFun a b ((2 ^ n : ℕ) • P) :=
          pointMapFun_two_nsmul _
        _ = (2 : ℕ) •
            ((2 ^ n : ℕ) • pointMapFun a b P) :=
          congrArg ((2 : ℕ) • ·) ih
        _ = (2 ^ (n + 1) : ℕ) • pointMapFun a b P := by
          rw [hpow, mul_nsmul]
          rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]

theorem dualPointMapFun_pow_two_nsmul {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (n : ℕ) (Q : (targetCurve a b).toAffine.Point) :
    dualPointMapFun a b ((2 ^ n : ℕ) • Q) =
      (2 ^ n : ℕ) • dualPointMapFun a b Q := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow : (2 ^ (n + 1) : ℕ) = 2 * 2 ^ n := by
        rw [pow_succ, Nat.mul_comm]
      calc
        dualPointMapFun a b ((2 ^ (n + 1) : ℕ) • Q) =
            dualPointMapFun a b
              ((2 : ℕ) • ((2 ^ n : ℕ) • Q)) := by
          rw [hpow, mul_nsmul]
          rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]
        _ = (2 : ℕ) •
            dualPointMapFun a b ((2 ^ n : ℕ) • Q) :=
          dualPointMapFun_two_nsmul _
        _ = (2 : ℕ) •
            ((2 ^ n : ℕ) • dualPointMapFun a b Q) :=
          congrArg ((2 : ℕ) • ·) ih
        _ = (2 ^ (n + 1) : ℕ) • dualPointMapFun a b Q := by
          rw [hpow, mul_nsmul]
          rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]



lemma targetOrigin_ne_zero (a b : ℚ)
    [(sourceCurve a b).IsElliptic] :
    targetOrigin a b ≠ 0 :=
  Point.some_ne_zero _

private lemma nsmul_ne_zero_of_addOrderOf_eq
    {G : Type*} [AddGroup G] {P : G} {n m : ℕ}
    (horder : addOrderOf P = n) (hndvd : ¬n ∣ m) :
    m • P ≠ 0 := by
  intro hm
  apply hndvd
  rw [← horder]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hm

/-- Doubling compatibility already extracts the order-five and full
two-torsion data needed in the order-twenty branch.  No compatibility with
odd multiples is required. -/
theorem order_twenty_image_data {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (Q : (sourceCurve a b).toAffine.Point)
    (hQ : addOrderOf Q = 20)
    (hmid : (10 : ℕ) • Q = sourceOrigin a b) :
    (2 : ℕ) • pointMapFun a b ((5 : ℕ) • Q) = 0 ∧
      pointMapFun a b ((5 : ℕ) • Q) ≠ 0 ∧
      pointMapFun a b ((5 : ℕ) • Q) ≠ targetOrigin a b ∧
      addOrderOf
          ((3 : ℕ) • pointMapFun a b ((4 : ℕ) • Q)) = 5 := by
  have h10Q :
      (10 : ℕ) • Q ≠ 0 :=
    nsmul_ne_zero_of_addOrderOf_eq hQ (by norm_num)
  have h20Q : (20 : ℕ) • Q = 0 := by
    rw [← hQ]
    exact addOrderOf_nsmul_eq_zero Q
  let S := pointMapFun a b ((5 : ℕ) • Q)
  let A := pointMapFun a b ((4 : ℕ) • Q)
  have hS_two : (2 : ℕ) • S = 0 := by
    calc
      (2 : ℕ) • S =
          pointMapFun a b ((2 : ℕ) • ((5 : ℕ) • Q)) :=
        (pointMapFun_two_nsmul _).symm
      _ = pointMapFun a b ((10 : ℕ) • Q) := by
        congr 1
        rw [← mul_nsmul]
      _ = pointMapFun a b (sourceOrigin a b) := by rw [hmid]
      _ = 0 := pointMapFun_sourceOrigin a b
  have hS_ne : S ≠ 0 := by
    intro hS
    have hkilled :
        (2 : ℕ) • ((5 : ℕ) • Q) = 0 :=
      pointMapFun_kernel_killed_by_two hS
    apply h10Q
    rw [← mul_nsmul] at hkilled
    norm_num at hkilled
    exact hkilled
  have hS_origin : S ≠ targetOrigin a b := by
    intro hS
    dsimp [S] at hS
    apply h10Q
    calc
      (10 : ℕ) • Q =
          (2 : ℕ) • ((5 : ℕ) • Q) := by
        rw [← mul_nsmul]
      _ = dualPointMapFun a b
          (pointMapFun a b ((5 : ℕ) • Q)) :=
        (dualPointMapFun_comp_pointMapFun _).symm
      _ = dualPointMapFun a b (targetOrigin a b) := by rw [hS]
      _ = 0 := dualPointMapFun_targetOrigin a b
  have h16A : (16 : ℕ) • A = A := by
    calc
      (16 : ℕ) • A =
          pointMapFun a b ((16 : ℕ) • ((4 : ℕ) • Q)) := by
        simpa only [show (16 : ℕ) = 2 ^ 4 by norm_num] using
          (pointMapFun_pow_two_nsmul 4 ((4 : ℕ) • Q)).symm
      _ = pointMapFun a b ((64 : ℕ) • Q) := by
        congr 1
      _ = pointMapFun a b ((4 : ℕ) • Q) := by
        rw [nsmul_eq_mod_nsmul 64 h20Q]
      _ = A := rfl
  have h15A : (15 : ℕ) • A = 0 := by
    rw [show (15 : ℕ) • A = (16 : ℕ) • A - A by abel,
      h16A, sub_self]
  have hthreeA : (3 : ℕ) • A ≠ 0 := by
    intro hthree
    have hfour : (4 : ℕ) • A = A := by
      rw [show (4 : ℕ) • A = (3 : ℕ) • A + A by abel,
        hthree, zero_add]
    have hdual_four :
        (4 : ℕ) • dualPointMapFun a b A =
          dualPointMapFun a b A := by
      calc
        (4 : ℕ) • dualPointMapFun a b A =
            dualPointMapFun a b ((4 : ℕ) • A) := by
          simpa only [show (4 : ℕ) = 2 ^ 2 by norm_num] using
            (dualPointMapFun_pow_two_nsmul 2 A).symm
        _ = dualPointMapFun a b A := by rw [hfour]
    have hdualA :
        dualPointMapFun a b A = (8 : ℕ) • Q := by
      calc
        dualPointMapFun a b A =
            (2 : ℕ) • ((4 : ℕ) • Q) :=
          dualPointMapFun_comp_pointMapFun _
        _ = (8 : ℕ) • Q := by
          rw [← mul_nsmul]
    have h32eq8 : (32 : ℕ) • Q = (8 : ℕ) • Q := by
      calc
        (32 : ℕ) • Q =
            (4 : ℕ) • ((8 : ℕ) • Q) := by
          rw [← mul_nsmul]
        _ = (4 : ℕ) • dualPointMapFun a b A := by rw [hdualA]
        _ = dualPointMapFun a b A := hdual_four
        _ = (8 : ℕ) • Q := hdualA
    have h24Q : (24 : ℕ) • Q = 0 := by
      rw [show (24 : ℕ) • Q =
          (32 : ℕ) • Q - (8 : ℕ) • Q by abel,
        h32eq8, sub_self]
    have hdvd : addOrderOf Q ∣ 24 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr h24Q
    rw [hQ] at hdvd
    norm_num at hdvd
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have horder_five : addOrderOf ((3 : ℕ) • A) = 5 := by
    apply addOrderOf_eq_prime
    · rw [← mul_nsmul]
      norm_num
      exact h15A
    · exact hthreeA
  exact ⟨hS_two, hS_ne, hS_origin, horder_five⟩



/-- A source point of order twenty whose midpoint is the isogeny kernel
produces a target point of exact order ten.  The visible target
two-torsion point is independent of its cyclic subgroup. -/
theorem exists_order_ten_image_independent {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (Q : (sourceCurve a b).toAffine.Point)
    (hQ : addOrderOf Q = 20)
    (hmid : (10 : ℕ) • Q = sourceOrigin a b) :
    ∃ C : (targetCurve a b).toAffine.Point,
      addOrderOf C = 10 ∧
        targetOrigin a b ∉ AddSubgroup.zmultiples C := by
  let S := pointMapFun a b ((5 : ℕ) • Q)
  let R := (3 : ℕ) • pointMapFun a b ((4 : ℕ) • Q)
  have hdata := order_twenty_image_data Q hQ hmid
  change (2 : ℕ) • S = 0 ∧ S ≠ 0 ∧
    S ≠ targetOrigin a b ∧ addOrderOf R = 5 at hdata
  rcases hdata with ⟨hS_two, hS_ne, hS_origin, hR_order⟩
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hS_order : addOrderOf S = 2 :=
    addOrderOf_eq_prime hS_two hS_ne
  have hT_two : (2 : ℕ) • targetOrigin a b = 0 := by
    simpa only [two_nsmul] using targetOrigin_add_self a b
  have hT_order : addOrderOf (targetOrigin a b) = 2 :=
    addOrderOf_eq_prime hT_two (targetOrigin_ne_zero a b)
  let C := S + R
  have hcoprime :
      Nat.Coprime (addOrderOf S) (addOrderOf R) := by
    rw [hS_order, hR_order]
    norm_num
  have hC_order : addOrderOf C = 10 := by
    calc
      addOrderOf C = addOrderOf S * addOrderOf R :=
        AddCommute.addOrderOf_add_eq_mul_addOrderOf_of_coprime
          (AddCommute.all S R) hcoprime
      _ = 10 := by rw [hS_order, hR_order]
  have hfiveS : (5 : ℕ) • S = S := by
    simpa using nsmul_eq_mod_nsmul 5 hS_two
  have hfiveR : (5 : ℕ) • R = 0 := by
    rw [← hR_order]
    exact addOrderOf_nsmul_eq_zero R
  have hhalf : (5 : ℕ) • C = S := by
    dsimp only [C]
    rw [nsmul_add, hfiveS, hfiveR, add_zero]
  refine ⟨C, hC_order, ?_⟩
  apply
    IndependentCyclicGenerators.orderTwo_not_mem_zmultiples
      (targetOrigin a b) C 5 hT_order
  · simpa using hC_order
  · rw [hhalf]
    exact hS_origin.symm



end MazurTorsion.TwoIsogeny

end


/- Source module: MazurTorsion.EllipticCurve.TwoTorsionNormalization. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Normalizing a rational point of order two

Let `T` be a rational point of exact order two on a Weierstrass curve
`E/ℚ`.  This file packages the elementary admissible change of variables
which translates `T` to `(0,0)` and completes the square.  The transformed
curve has the form

`y² = x(x² + ax + b)`,

namely `TwoIsogeny.sourceCurve a b`.

The result is recorded as `Data E T`.  Besides the change of variables and
the two coefficients, the structure retains the nonsingularity proof for
the new origin, the equality with the standard source model, and the
point-group equivalence carrying the new origin back to `T`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.TwoTorsionNormalization

open WeierstrassCurve

/-- A checked normalization of a rational two-torsion point. -/
structure Data (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (T : E.toAffine.Point) where
  /-- The admissible change of variables carrying the curve to the normalized model. -/
  change : WeierstrassCurve.VariableChange ℚ
  /-- The linear coefficient of the normalized two-isogeny source model. -/
  a : ℚ
  /-- The quadratic coefficient of the normalized two-isogeny source model. -/
  b : ℚ
  originNonsingular :
    (change • E).toAffine.Nonsingular 0 0
  curve_eq :
    change • E = MazurTorsion.TwoIsogeny.sourceCurve a b
  map_origin :
    WeierstrassCurve.Affine.Point.equivVariableChange E change
        (.some 0 0 originNonsingular) = T

namespace Data

variable {E : WeierstrassCurve ℚ} [E.IsElliptic]
  {T : E.toAffine.Point}

/-- The point-group equivalence supplied by the normalization. -/
noncomputable def equiv (D : Data E T) :
    (D.change • E).toAffine.Point ≃+ E.toAffine.Point :=
  WeierstrassCurve.Affine.Point.equivVariableChange E D.change

/-- The normalized origin `(0,0)`. -/
def origin (D : Data E T) :
    (D.change • E).toAffine.Point :=
  .some 0 0 D.originNonsingular

@[simp] theorem equiv_origin (D : Data E T) :
    D.equiv D.origin = T :=
  D.map_origin

/-- Pull a point of the original curve back to the normalized model. -/
noncomputable def pullback (D : Data E T)
    (P : E.toAffine.Point) :
    (D.change • E).toAffine.Point :=
  D.equiv.symm P

@[simp] theorem equiv_pullback (D : Data E T)
    (P : E.toAffine.Point) :
    D.equiv (D.pullback P) = P :=
  D.equiv.apply_symm_apply P





/-- Ellipticity transported to the standard source curve. -/
theorem source_isElliptic (D : Data E T) :
    (MazurTorsion.TwoIsogeny.sourceCurve D.a D.b).IsElliptic := by
  rw [← D.curve_eq]
  infer_instance

/-- The normalization equivalence with its source written literally as
`TwoIsogeny.sourceCurve`. -/
noncomputable def sourceEquiv (D : Data E T) :
    letI := D.source_isElliptic
    (MazurTorsion.TwoIsogeny.sourceCurve D.a D.b).toAffine.Point ≃+
      E.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.equivOfEq D.curve_eq.symm).trans
    D.equiv

/-- Pull a point directly to the literal standard source curve. -/
noncomputable def sourcePullback (D : Data E T)
    (P : E.toAffine.Point) :
    letI := D.source_isElliptic
    (MazurTorsion.TwoIsogeny.sourceCurve D.a D.b).toAffine.Point :=
  D.sourceEquiv.symm P

@[simp] theorem sourceEquiv_sourcePullback (D : Data E T)
    (P : E.toAffine.Point) :
    letI := D.source_isElliptic
    D.sourceEquiv (D.sourcePullback P) = P :=
  D.sourceEquiv.apply_symm_apply P

theorem addOrderOf_sourcePullback (D : Data E T)
    (P : E.toAffine.Point) :
    letI := D.source_isElliptic
    addOrderOf (D.sourcePullback P) = addOrderOf P := by
  letI := D.source_isElliptic
  rw [← AddEquiv.addOrderOf_eq D.sourceEquiv]
  exact congrArg addOrderOf (D.sourceEquiv_sourcePullback P)

/-- A terminal relation `nP=T` becomes the literal source-origin relation
on `TwoIsogeny.sourceCurve`. -/
theorem nsmul_sourcePullback_eq_sourceOrigin
    (D : Data E T) (P : E.toAffine.Point) (n : ℕ)
    (h : n • P = T) :
    letI := D.source_isElliptic
    n • D.sourcePullback P =
      MazurTorsion.TwoIsogeny.sourceOrigin D.a D.b := by
  letI := D.source_isElliptic
  apply D.sourceEquiv.injective
  rw [map_nsmul, D.sourceEquiv_sourcePullback]
  calc
    n • P = T := h
    _ = D.equiv D.origin := D.equiv_origin.symm
    _ = D.equiv
        (WeierstrassCurve.Affine.Point.equivOfEq D.curve_eq.symm
          (MazurTorsion.TwoIsogeny.sourceOrigin D.a D.b)) := by
      apply congrArg D.equiv
      simp [Data.origin, MazurTorsion.TwoIsogeny.sourceOrigin,
        WeierstrassCurve.Affine.Point.equivOfEq_some]

end Data

/-- Every rational point of exact order two admits the standard
`y²=x(x²+ax+b)` normalization. -/
theorem exists_data_of_order_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (T : E.toAffine.Point) (hTorder : addOrderOf T = 2) :
    Nonempty (Data E T) := by
  have hT0 : T ≠ 0 := by
    intro hT0
    rw [hT0, addOrderOf_zero] at hTorder
    norm_num at hTorder
  have hTdouble : (2 : ℕ) • T = 0 := by
    rw [← hTorder]
    exact addOrderOf_nsmul_eq_zero T
  obtain ⟨theta, yT, hTns, hTxy⟩ :
      ∃ (x y : ℚ) (h : E.toAffine.Nonsingular x y),
        T = WeierstrassCurve.Affine.Point.some x y h := by
    cases hcase : T with
    | zero => exact (hT0 hcase).elim
    | some x y h => exact ⟨x, y, h, rfl⟩
  have hvertical : yT = E.toAffine.negY theta yT := by
    by_contra hne
    have hnonzero :
        WeierstrassCurve.Affine.Point.some theta yT hTns +
            WeierstrassCurve.Affine.Point.some theta yT hTns ≠ 0 := by
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne]
      exact WeierstrassCurve.Affine.Point.some_ne_zero _
    apply hnonzero
    rw [← two_nsmul, ← hTxy]
    exact hTdouble
  have hvertical' :
      E.a₃ + theta * E.a₁ + 2 * yT = 0 := by
    rw [WeierstrassCurve.Affine.negY] at hvertical
    linear_combination hvertical
  let C : WeierstrassCurve.VariableChange ℚ :=
    ⟨1, theta, -E.a₁ / 2, yT⟩
  let W : WeierstrassCurve ℚ := C • E
  have hWa₁ : W.a₁ = 0 := by
    dsimp [W, C]
    rw [WeierstrassCurve.variableChange_a₁]
    simp
    ring
  have hWa₃ : W.a₃ = 0 := by
    dsimp [W, C]
    rw [WeierstrassCurve.variableChange_a₃]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination hvertical'
  have hWa₆ : W.a₆ = 0 := by
    have heq := hTns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    dsimp [W, C]
    rw [WeierstrassCurve.variableChange_a₆]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  have h00 : W.toAffine.Nonsingular 0 0 := by
    apply W.toAffine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_zero]
    exact hWa₆
  let a : ℚ := W.a₂
  let b : ℚ := W.a₄
  have hWsource :
      W = MazurTorsion.TwoIsogeny.sourceCurve a b := by
    ext <;>
      simp [MazurTorsion.TwoIsogeny.sourceCurve,
        a, b, hWa₁, hWa₃, hWa₆]
  have hmapOrigin :
      WeierstrassCurve.Affine.Point.equivVariableChange E C
          (WeierstrassCurve.Affine.Point.some 0 0 h00) = T := by
    rw [WeierstrassCurve.Affine.Point.equivVariableChange_some,
      hTxy]
    exact WeierstrassCurve.Affine.Point.some_eq_some E
      (by simp [C]) (by simp [C])
  refine ⟨{
    change := C
    a := a
    b := b
    originNonsingular := ?_
    curve_eq := ?_
    map_origin := ?_ }⟩
  · simpa only [W] using h00
  · simpa only [W] using hWsource
  · simpa only [Data.origin] using hmapOrigin

end MazurTorsion.TwoTorsionNormalization

end


/- Source module: MazurTorsion.Arithmetic.ExceptionalProducts. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-! Boundary: transport a finite-source public torsion-subgroup exclusion to the
actual rational point group. Named downstream consumers: the order-twenty and
order-twenty-four two-isogeny arguments. No curve arithmetic is added here. -/
open scoped WeierstrassCurve.Affine
namespace MazurTorsion

theorem point_forbids_of_torsion_forbids
    {A : Type*} [AddCommGroup A] [Finite A]
    (E : WeierstrassCurve ℚ)
    (h : ForbidsEmbedding A (MazurCampaign.RationalTorsion E)) :
    ForbidsEmbedding A (E⁄ℚ).Point := by
  intro f hf
  let g : A →+ MazurCampaign.RationalTorsion E :=
    f.codRestrict (AddCommGroup.torsion (E⁄ℚ).Point)
      (fun a => AddMonoidHom.isOfFinAddOrder f (isOfFinAddOrder_of_finite a))
  apply h g
  intro a b hab
  exact hf (congrArg Subtype.val hab)

theorem forbidsEmbedding_zmod_two_prod_ten
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ForbidsEmbedding (ZMod 2 × ZMod 10) (E⁄ℚ).Point :=
  point_forbids_of_torsion_forbids E (MazurCampaign.no_two_ten E)



end MazurTorsion

end


/- Source module: MazurTorsion.Arithmetic.OrderTwentyTwentyFour. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Excluding rational points of orders twenty and twenty-four

For a point `Q` of exact order `2n`, its midpoint `nQ` has exact order
two.  Normalize that midpoint to `(0,0)` on

`y² = x(x² + ax + b)`.

The explicit two-isogeny then constructs on the target curve a point of
exact order `n` whose cyclic subgroup does not contain the visible target
two-torsion point.  These two independent generators embed
`ZMod 2 × ZMod n`.  The unconditional exceptional-product obstructions
rule this out for `n = 10` and `n = 12`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

open TwoIsogeny
open TwoTorsionNormalization

private lemma targetOrigin_addOrderOf
    (a b : ℚ) [(sourceCurve a b).IsElliptic] :
    addOrderOf (targetOrigin a b) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply addOrderOf_eq_prime
  · simpa only [two_nsmul] using targetOrigin_add_self a b
  · exact targetOrigin_ne_zero a b

/-- No elliptic curve over `ℚ` has a rational point of exact order
twenty. -/
theorem no_rational_point_of_order_twenty
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : E.toAffine.Point) :
    addOrderOf Q ≠ 20 := by
  intro hQ
  let T : E.toAffine.Point := (10 : ℕ) • Q
  have hTorder : addOrderOf T = 2 := by
    dsimp only [T]
    rw [addOrderOf_nsmul' Q (by norm_num), hQ]
    norm_num
  obtain ⟨D⟩ :=
    TwoTorsionNormalization.exists_data_of_order_two E T hTorder
  letI := D.source_isElliptic
  let Q₀ := D.sourcePullback Q
  have hQ₀order : addOrderOf Q₀ = 20 := by
    dsimp only [Q₀]
    rw [D.addOrderOf_sourcePullback, hQ]
  have hmid :
      (10 : ℕ) • Q₀ = sourceOrigin D.a D.b := by
    dsimp only [Q₀]
    apply D.nsmul_sourcePullback_eq_sourceOrigin
    rfl
  obtain ⟨C, hCorder, hindependent⟩ :=
    exists_order_ten_image_independent Q₀ hQ₀order hmid
  obtain ⟨f, hf⟩ :=
    IndependentCyclicGenerators.exists_embedding
      (targetOrigin D.a D.b) C
      (targetOrigin_addOrderOf D.a D.b) 10 hCorder
      hindependent
  exact
    (forbidsEmbedding_zmod_two_prod_ten
      (targetCurve D.a D.b)) f hf



/-- The order-twenty obstruction on the canonical rational base change
used by `RationalTorsion`. -/
theorem rationalPoint_addOrderOf_ne_twenty
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) :
    addOrderOf Q ≠ 20 := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  exact no_rational_point_of_order_twenty (E⁄ℚ) Q



end MazurTorsion.Kubert

end

open scoped WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 20 := by
  intro x hx
  have horder : addOrderOf (x : (E⁄ℚ).Point) = addOrderOf x :=
    addOrderOf_injective (AddCommGroup.torsion (E⁄ℚ).Point).subtype
      (AddCommGroup.torsion (E⁄ℚ).Point).subtype_injective x
  exact MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_twenty E x (horder.trans hx)

example : ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (x : MazurCampaign.RationalTorsion E), addOrderOf x ≠ 20 := solution
#print axioms solution
