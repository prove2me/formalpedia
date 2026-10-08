-- Prove2me | solution 1 for MazurTransfer.order18_from_genus_two_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T13:36:16.441686+00:00
-- url     : https://prove2.me/submissions/ce73745e-86e8-4875-8788-c3428aaded5c

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_MazurReduction_PointTransport
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Mathlib.RingTheory.RamificationInertia.Ramification

/- Retain the namespace opened by the source after its unused declarations are pruned. -/
namespace MazurTorsion.XOneEighteenQuotientRankZero
end MazurTorsion.XOneEighteenQuotientRankZero


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



section Decidable

variable [DecidableEq F]













end Decidable









section Decidable

variable [DecidableEq F]





end Decidable

section Height

open Height

variable [AdmissibleAbsValues F]







variable (W)



variable [W.toAffine.IsElliptic]





variable [Northcott (logHeight₁ (K := F))]
variable [DecidableEq F]





end Height

end WeierstrassCurve.Affine

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


/- Source module: MazurTorsion.Kubert.OrderEighteenReduction. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Reduction of a point of order eighteen

If `Q` has exact order eighteen, then `2Q` has exact order nine and `9Q`
has exact order two.  Normalize the order-nine point to the marked point on
Tate normal form.  The first fact gives `orderNinePolynomial b c = 0`;
the transported order-two point supplies a rational root of the explicit
two-division cubic.

This is the denominator-safe common entry to the usual genus-two model for
`X₁(18)`.  The elimination and rational-point classification are kept as a
separate boundary.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- The duplication denominator on Tate normal form. Its rational roots are
the abscissas of the nonzero rational points killed by two. -/
def tateTwoDivisionPolynomial (b c r : ℚ) : ℚ :=
  4 * r ^ 3 + ((1 - c) ^ 2 - 4 * b) * r ^ 2 +
    2 * b * (c - 1) * r + b ^ 2

private lemma tateTwoDivisionPolynomial_eq_zero_of_order_two
    (b c r s : ℚ)
    (hrs : (tateNormalCurve b c).toAffine.Nonsingular r s)
    (horder :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some r s hrs :
          (tateNormalCurve b c).toAffine.Point) = 2) :
    tateTwoDivisionPolynomial b c r = 0 := by
  let W := tateNormalCurve b c
  let P : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some r s hrs
  have hdouble : P + P = 0 := by
    rw [← two_nsmul, ← horder]
    exact addOrderOf_nsmul_eq_zero P
  have hvertical : s = W.toAffine.negY r s := by
    by_contra hne
    have hnonzero : P + P ≠ 0 := by
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne]
      exact WeierstrassCurve.Affine.Point.some_ne_zero _
    exact hnonzero hdouble
  have hden :=
    (WeierstrassCurve.Affine.den_duplication_eq_zero_iff hrs.1).mpr
      hvertical
  simp only [tateNormalCurve, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hden
  simp only [tateTwoDivisionPolynomial]
  linear_combination hden

/-- A rational point of exact order eighteen produces simultaneous
order-nine and rational-two-torsion equations on one Tate normal form,
with the original discriminant scale retained. -/
theorem exists_tateOrderEighteen_certificate
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 18) :
    ∃ b c u r : ℚ,
      u ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧
      orderNinePolynomial b c = 0 ∧
      tateTwoDivisionPolynomial b c r = 0 ∧
      u ^ 12 * E.Δ = (tateNormalCurve b c).Δ := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  let R : (E⁄ℚ).Point := (2 : ℕ) • Q
  let T : (E⁄ℚ).Point := (9 : ℕ) • Q
  have hRorder : addOrderOf R = 9 := by
    dsimp [R]
    rw [addOrderOf_nsmul' Q (by norm_num), hQ]
    norm_num
  have hTorder : addOrderOf T = 2 := by
    dsimp [T]
    rw [addOrderOf_nsmul' Q (by norm_num), hQ]
    norm_num
  have hR2 : R + R ≠ 0 := by
    intro h
    have hdvd : addOrderOf R ∣ 2 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [two_nsmul]
        exact h)
    rw [hRorder] at hdvd
    norm_num at hdvd
  have hR3 : R + R + R ≠ 0 := by
    intro h
    have hdvd : addOrderOf R ∣ 3 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr (by
        rw [show (3 : ℕ) • R = R + R + R by abel]
        exact h)
    rw [hRorder] at hdvd
    norm_num at hdvd
  obtain ⟨b, c, u, hu, hb, h00, e, heR, hdisc, -, -⟩ :=
    exists_tateNormalCurve_scaled (E⁄ℚ) R hR2 hR3
  have hmarked :
      addOrderOf
        (WeierstrassCurve.Affine.Point.some 0 0 h00 :
          (tateNormalCurve b c).toAffine.Point) = 9 := by
    rw [← heR, AddEquiv.addOrderOf_eq]
    exact hRorder
  have hc :=
    c_ne_zero_of_marked_order_nine b c hb h00 hmarked
  have hbc :=
    parameters_ne_of_marked_order_nine b c hb h00 hmarked
  have hnine :=
    orderNinePolynomial_eq_zero_of_marked_order
      b c hb h00 hmarked
  have hTmarked : addOrderOf (e T) = 2 := by
    rw [AddEquiv.addOrderOf_eq]
    exact hTorder
  cases hTcase : e T with
  | zero =>
      rw [hTcase] at hTmarked
      change
        addOrderOf
          (0 : (tateNormalCurve b c).toAffine.Point) = 2
        at hTmarked
      rw [addOrderOf_zero] at hTmarked
      omega
  | some r s hrs =>
      have htwo :
          tateTwoDivisionPolynomial b c r = 0 :=
        tateTwoDivisionPolynomial_eq_zero_of_order_two
          b c r s hrs (by simpa [hTcase] using hTmarked)
      refine ⟨b, c, u, r, hu, hb, hc, hbc, hnine, htwo, ?_⟩
      have hbase : (E⁄ℚ).Δ = E.Δ := by
        simp [WeierstrassCurve.baseChange]
      rwa [← hbase]

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

/-- The auxiliary coordinate obtained from a root of the Tate two-division
polynomial. -/
def orderEighteenAuxiliaryS (b c r : ℚ) : ℚ :=
  ((1 - c) * r - b) / (2 * r * c)

/-- The equation in the order-nine parameter and the auxiliary
two-division coordinate. -/
def orderEighteenAuxiliaryPolynomial (d s : ℚ) : ℚ :=
  (2 * s + 1) *
      (d ^ 2 * (d - 1) * s ^ 2 - (d ^ 2 - d + 1)) -
    s ^ 2

/-- The abscissa in the standard genus-two model for `X₁(18)`. -/
def orderEighteenModelX (d s : ℚ) : ℚ :=
  (d - s + 2 * d * s) / (1 + d * s)

/-- The ordinate in the standard genus-two model for `X₁(18)`. -/
def orderEighteenModelY (d s : ℚ) : ℚ :=
  let X := orderEighteenModelX d s
  2 * X * d - (X ^ 3 - 2 * X ^ 2 + 3 * X - 1)

/-- The sextic defining the standard genus-two model for `X₁(18)`. -/
def orderEighteenHyperellipticPolynomial (X : ℚ) : ℚ :=
  X ^ 6 - 4 * X ^ 5 + 10 * X ^ 4 - 10 * X ^ 3 +
    5 * X ^ 2 - 2 * X + 1

lemma orderNinePolynomial_eq_difference_form (b c : ℚ) :
    orderNinePolynomial b c =
      c ^ 5 - (b - c) * c ^ 3 - (b - c) ^ 3 := by
  simp only [orderNinePolynomial]
  ring

lemma orderNineParameterD_ne_zero
    (b c : ℚ) (hc : c ≠ 0) (hbc : b ≠ c) :
    orderNineParameterD b c ≠ 0 := by
  exact div_ne_zero (pow_ne_zero 2 hc) (sub_ne_zero.mpr hbc)

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

lemma orderNineParameterD_ne_one
    (b c : ℚ) (hc : c ≠ 0) (hbc : b ≠ c)
    (hnine : orderNinePolynomial b c = 0) :
    orderNineParameterD b c ≠ 1 := by
  intro hd1
  have hcparam :=
    (orderNine_parameterization b c hc hbc hnine).1
  rw [hd1] at hcparam
  norm_num at hcparam
  exact hc hcparam

lemma root_ne_zero_of_tateTwoDivisionPolynomial
    (b c r : ℚ) (hb : b ≠ 0)
    (htwo : tateTwoDivisionPolynomial b c r = 0) :
    r ≠ 0 := by
  intro hr
  subst r
  simp [tateTwoDivisionPolynomial, hb] at htwo

/-- After the order-nine parametrization, a root of the two-division
polynomial gives the displayed auxiliary equation. -/
theorem orderEighteenAuxiliaryPolynomial_eq_zero
    (b c r d : ℚ) (hc : c ≠ 0) (hr : r ≠ 0)
    (hcparam : c = d ^ 2 * (d - 1))
    (hbparam : b = c * (d ^ 2 - d + 1))
    (htwo : tateTwoDivisionPolynomial b c r = 0) :
    orderEighteenAuxiliaryPolynomial d
        (orderEighteenAuxiliaryS b c r) = 0 := by
  calc
    orderEighteenAuxiliaryPolynomial d
          (orderEighteenAuxiliaryS b c r) =
        -(d ^ 2 - d + 1) *
            tateTwoDivisionPolynomial b c r /
          (4 * r ^ 3 * c) := by
      simp only [orderEighteenAuxiliaryPolynomial,
        orderEighteenAuxiliaryS, tateTwoDivisionPolynomial]
      field_simp [hr, hc]
      rw [hbparam, hcparam]
      ring
    _ = 0 := by rw [htwo]; simp

/-- The denominator in the genus-two change of variables cannot vanish on
the nondegenerate auxiliary curve. -/
lemma one_add_mul_ne_zero_of_orderEighteenAuxiliary
    (d s : ℚ) (hd : d ≠ 0) (hd1 : d ≠ 1)
    (haux : orderEighteenAuxiliaryPolynomial d s = 0) :
    1 + d * s ≠ 0 := by
  intro hden
  have hs : s = -1 / d := by
    field_simp [hd]
    linear_combination hden
  have hspecial :
      orderEighteenAuxiliaryPolynomial d (-1 / d) =
        -(d - 1) ^ 4 / d ^ 2 := by
    simp only [orderEighteenAuxiliaryPolynomial]
    field_simp [hd]
    ring
  rw [hs, hspecial] at haux
  have hpow : (d - 1) ^ 4 = 0 := by
    field_simp [hd] at haux
    exact neg_eq_zero.mp (by simpa using haux)
  exact (pow_ne_zero 4 (sub_ne_zero.mpr hd1)) hpow

/-- The rational change of variables sends the auxiliary equation to the
standard sextic model. -/
theorem orderEighteenModel_equation
    (d s : ℚ) (hden : 1 + d * s ≠ 0)
    (haux : orderEighteenAuxiliaryPolynomial d s = 0) :
    orderEighteenModelY d s ^ 2 =
      orderEighteenHyperellipticPolynomial
        (orderEighteenModelX d s) := by
  have hidentity :
      orderEighteenModelY d s ^ 2 -
          orderEighteenHyperellipticPolynomial
            (orderEighteenModelX d s) =
        4 * (d - 1) ^ 2 *
            (2 * d * s + d - s) *
            orderEighteenAuxiliaryPolynomial d s /
          (1 + d * s) ^ 4 := by
    simp only [orderEighteenModelY, orderEighteenModelX,
      orderEighteenHyperellipticPolynomial,
      orderEighteenAuxiliaryPolynomial]
    field_simp [hden]
    ring
  apply sub_eq_zero.mp
  calc
    orderEighteenModelY d s ^ 2 -
          orderEighteenHyperellipticPolynomial
            (orderEighteenModelX d s) =
        4 * (d - 1) ^ 2 *
            (2 * d * s + d - s) *
            orderEighteenAuxiliaryPolynomial d s /
          (1 + d * s) ^ 4 := hidentity
    _ = 0 := by rw [haux]; simp

/-- A nondegenerate point of the auxiliary curve does not map to the
affine point with abscissa zero. -/
lemma orderEighteenModelX_ne_zero
    (d s : ℚ) (hd1 : d ≠ 1)
    (hden : 1 + d * s ≠ 0)
    (haux : orderEighteenAuxiliaryPolynomial d s = 0) :
    orderEighteenModelX d s ≠ 0 := by
  intro hX
  have hnum : d - s + 2 * d * s = 0 := by
    simp only [orderEighteenModelX] at hX
    field_simp [hden] at hX
    simpa [mul_comm, mul_left_comm, mul_assoc] using hX
  have hcoef : 2 * d - 1 ≠ 0 := by
    intro hcoef
    have hdhalf : d = 1 / 2 := by linarith
    rw [hdhalf] at hnum
    norm_num at hnum
  have hs : s = -d / (2 * d - 1) := by
    apply (eq_div_iff hcoef).2
    linear_combination hnum
  have hspecial :
      orderEighteenAuxiliaryPolynomial d
          (-d / (2 * d - 1)) =
        -(d - 1) ^ 5 / (2 * d - 1) ^ 3 := by
    simp only [orderEighteenAuxiliaryPolynomial]
    field_simp [hcoef]
    ring
  rw [hs, hspecial] at haux
  have hpow : (d - 1) ^ 5 = 0 := by
    rcases (div_eq_zero_iff.mp haux) with hneg | hdenzero
    · exact neg_eq_zero.mp hneg
    · exact (pow_ne_zero 3 hcoef hdenzero).elim
  exact (pow_ne_zero 5 (sub_ne_zero.mpr hd1)) hpow

/-- A nondegenerate point of the auxiliary curve does not map to the
affine point with abscissa one. -/
lemma orderEighteenModelX_ne_one
    (d s : ℚ) (hd : d ≠ 0) (hd1 : d ≠ 1)
    (hden : 1 + d * s ≠ 0)
    (haux : orderEighteenAuxiliaryPolynomial d s = 0) :
    orderEighteenModelX d s ≠ 1 := by
  intro hX
  have hnum :
      d - s + 2 * d * s = 1 + d * s := by
    simp only [orderEighteenModelX] at hX
    field_simp [hden] at hX
    simpa [mul_comm, mul_left_comm, mul_assoc] using hX
  have hfac : (d - 1) * (s + 1) = 0 := by
    linear_combination hnum
  have hsadd : s + 1 = 0 := by
    rcases mul_eq_zero.mp hfac with hdsub | hsadd
    · exact (sub_ne_zero.mpr hd1 hdsub).elim
    · exact hsadd
  have hs : s = -1 := by linarith
  have hspecial :
      orderEighteenAuxiliaryPolynomial d (-1) =
        -d * (d - 1) ^ 2 := by
    simp only [orderEighteenAuxiliaryPolynomial]
    ring
  rw [hs, hspecial] at haux
  rcases mul_eq_zero.mp haux with hnegd | hpow
  · exact hd (neg_eq_zero.mp hnegd)
  · exact (pow_ne_zero 2 (sub_ne_zero.mpr hd1)) hpow

/-- A point of exact order eighteen supplies a nondegenerate rational point
on the explicit genus-two model, together with all Tate parameters,
denominator conditions, source equations, and the original discriminant
scale.

This is only a reduction theorem.  It does not classify the rational
points of the genus-two curve. -/
theorem exists_orderEighteen_genusTwo_certificate
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point) (hQ : addOrderOf Q = 18) :
    ∃ b c u r d s : ℚ,
      u ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ b ≠ c ∧ r ≠ 0 ∧
      d = orderNineParameterD b c ∧ d ≠ 0 ∧ d ≠ 1 ∧
      c = d ^ 2 * (d - 1) ∧
      b = c * (d ^ 2 - d + 1) ∧
      s = orderEighteenAuxiliaryS b c r ∧
      orderNinePolynomial b c = 0 ∧
      tateTwoDivisionPolynomial b c r = 0 ∧
      orderEighteenAuxiliaryPolynomial d s = 0 ∧
      1 + d * s ≠ 0 ∧
      orderEighteenModelX d s ≠ 0 ∧
      orderEighteenModelX d s ≠ 1 ∧
      orderEighteenModelY d s ^ 2 =
        orderEighteenHyperellipticPolynomial
          (orderEighteenModelX d s) ∧
      u ^ 12 * E.Δ = (tateNormalCurve b c).Δ := by
  obtain ⟨b, c, u, r, hu, hb, hc, hbc, hnine, htwo, hdisc⟩ :=
    exists_tateOrderEighteen_certificate E Q hQ
  let d := orderNineParameterD b c
  let s := orderEighteenAuxiliaryS b c r
  have hd : d ≠ 0 :=
    orderNineParameterD_ne_zero b c hc hbc
  have hd1 : d ≠ 1 :=
    orderNineParameterD_ne_one b c hc hbc hnine
  obtain ⟨hcparam, hbparam⟩ :=
    orderNine_parameterization b c hc hbc hnine
  have hr : r ≠ 0 :=
    root_ne_zero_of_tateTwoDivisionPolynomial b c r hb htwo
  have haux : orderEighteenAuxiliaryPolynomial d s = 0 :=
    orderEighteenAuxiliaryPolynomial_eq_zero
      b c r d hc hr hcparam hbparam htwo
  have hden : 1 + d * s ≠ 0 :=
    one_add_mul_ne_zero_of_orderEighteenAuxiliary
      d s hd hd1 haux
  have hX0 : orderEighteenModelX d s ≠ 0 :=
    orderEighteenModelX_ne_zero d s hd1 hden haux
  have hX1 : orderEighteenModelX d s ≠ 1 :=
    orderEighteenModelX_ne_one d s hd hd1 hden haux
  have hmodel :
      orderEighteenModelY d s ^ 2 =
        orderEighteenHyperellipticPolynomial
          (orderEighteenModelX d s) :=
    orderEighteenModel_equation d s hden haux
  exact
    ⟨b, c, u, r, d, s, hu, hb, hc, hbc, hr, rfl, hd, hd1,
      hcparam, hbparam, rfl, hnine, htwo, haux, hden, hX0, hX1,
      hmodel, hdisc⟩

/-- A route-neutral exclusion of noncuspidal rational points on the
hyperelliptic model rules out exact rational order eighteen. -/
theorem rationalPoint_addOrderOf_ne_eighteen_of_noNoncuspidalPoint
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point)
    (hNoNoncuspidal :
      ∀ x y : ℚ, x ≠ 0 → x ≠ 1 →
        y ^ 2 = orderEighteenHyperellipticPolynomial x → False) :
    addOrderOf Q ≠ 18 := by
  intro hQ
  obtain ⟨_b, _c, _u, _r, d, s, _hu, _hb, _hc, _hbc, _hr,
    _hd, _hd0, _hd1, _hcparam, _hbparam, _hs, _hnine, _htwo,
    _haux, _hden, hX0, hX1, hcurve, _hdisc⟩ :=
    exists_orderEighteen_genusTwo_certificate E Q hQ
  exact hNoNoncuspidal
    (orderEighteenModelX d s) (orderEighteenModelY d s)
    hX0 hX1 hcurve

end MazurTorsion.Kubert

end

open scoped WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Q : (E⁄ℚ).Point)
    (hNoNoncuspidal : ∀ x y : ℚ, x ≠ 0 → x ≠ 1 →
      y ^ 2 = x ^ 6 - 4 * x ^ 5 + 10 * x ^ 4 - 10 * x ^ 3 + 5 * x ^ 2 - 2 * x + 1 → False) :
    addOrderOf Q ≠ 18 := by
  apply MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_eighteen_of_noNoncuspidalPoint E Q
  simpa only [MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial] using hNoNoncuspidal
#print axioms solution
