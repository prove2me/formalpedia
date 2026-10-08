-- Prove2me | solution 1 for MazurCampaign.no_order_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T09:00:36.70189+00:00
-- url     : https://prove2.me/submissions/3b1d52e3-f0a3-4bfc-a1eb-64977d63e5d9

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints


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


/- Source module: MazurTorsion.NumberTheory.QuarticDifferenceDescent. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Fermat's quartic-difference descent

This file proves that a nonzero square cannot be the difference of two nonzero
fourth powers:

`x ^ 4 - y ^ 4 ≠ z ^ 2` when `x`, `y`, and `z` are all nonzero integers.

The hypothesis on `z` is essential: when `z = 0`, the choices `x = y ≠ 0`
give a degenerate family of solutions.

The proof is the classical infinite descent.  A least solution is primitive.
The equation makes `(y², z, x²)` a primitive Pythagorean triple.  When `y` is
odd, its parametrization immediately produces a smaller quartic-difference
solution.  When `y` is even, parametrizing twice and extracting squares from
coprime products produces the smaller solution.
-/


namespace MazurTorsion.QuarticDifference

/-- A nondegenerate integral solution of `x⁴ - y⁴ = z²`. -/
private def IsSolution (x y z : ℤ) : Prop :=
  x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x ^ 4 - y ^ 4 = z ^ 2

private theorem IsSolution.mul {x y z k : ℤ} (hk : k ≠ 0) :
    IsSolution x y z ↔ IsSolution (k * x) (k * y) (k ^ 2 * z) := by
  unfold IsSolution
  constructor
  · rintro ⟨hx, hy, hz, h⟩
    refine ⟨mul_ne_zero hk hx, mul_ne_zero hk hy, mul_ne_zero (pow_ne_zero 2 hk) hz, ?_⟩
    linear_combination k ^ 4 * h
  · rintro ⟨hx, hy, hz, h⟩
    refine ⟨right_ne_zero_of_mul hx, right_ne_zero_of_mul hy,
      right_ne_zero_of_mul hz, ?_⟩
    apply (mul_left_inj' (pow_ne_zero 4 hk)).mp
    linear_combination h

/-- A solution is minimal when the square of the absolute value of its first
coordinate is least among all nondegenerate solutions. -/
private def IsMinimal (x y z : ℤ) : Prop :=
  IsSolution x y z ∧
    ∀ x' y' z' : ℤ, IsSolution x' y' z' →
      Int.natAbs (x ^ 2) ≤ Int.natAbs (x' ^ 2)

private theorem exists_minimal {x y z : ℤ} (h : IsSolution x y z) :
    ∃ x₀ y₀ z₀ : ℤ, IsMinimal x₀ y₀ z₀ := by
  classical
  let S : Set ℕ :=
    {n | ∃ s : ℤ × ℤ × ℤ, IsSolution s.1 s.2.1 s.2.2 ∧
      n = Int.natAbs (s.1 ^ 2)}
  have hS : S.Nonempty := by
    refine ⟨Int.natAbs (x ^ 2), ?_⟩
    exact ⟨(x, y, z), h, rfl⟩
  let m := Nat.find hS
  obtain ⟨s, hs, hm⟩ := Nat.find_spec hS
  refine ⟨s.1, s.2.1, s.2.2, hs, ?_⟩
  intro x' y' z' h'
  rw [← hm]
  apply Nat.find_min'
  exact ⟨(x', y', z'), h', rfl⟩

private theorem coprime_of_minimal {x y z : ℤ} (h : IsMinimal x y z) :
    IsCoprime x y := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hxy
  obtain ⟨p, hp, hpx, hpy⟩ := Nat.Prime.not_coprime_iff_dvd.mp hxy
  obtain ⟨x₁, hx₁⟩ := Int.natCast_dvd.mpr hpx
  obtain ⟨y₁, hy₁⟩ := Int.natCast_dvd.mpr hpy
  have hpz : (p : ℤ) ^ 2 ∣ z := by
    rw [← Int.pow_dvd_pow_iff two_ne_zero, ← h.1.2.2.2]
    refine ⟨x₁ ^ 4 - y₁ ^ 4, ?_⟩
    rw [hx₁, hy₁]
    ring
  obtain ⟨z₁, hz₁⟩ := hpz
  have h₁ : IsSolution x₁ y₁ z₁ := by
    apply (IsSolution.mul (Int.natCast_ne_zero.mpr hp.ne_zero)).mpr
    simpa only [hx₁, hy₁, hz₁]
      using h.1
  have hle := h.2 x₁ y₁ z₁ h₁
  have hlt : Int.natAbs (x₁ ^ 2) < Int.natAbs (x ^ 2) := by
    rw [hx₁, show ((p : ℤ) * x₁) ^ 2 = (p : ℤ) ^ 2 * x₁ ^ 2 by ring,
      Int.natAbs_mul, lt_mul_iff_one_lt_left, Int.natAbs_pow,
      Int.natAbs_natCast]
    · exact Nat.one_lt_pow two_ne_zero hp.one_lt
    · exact Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr (pow_ne_zero 2 h₁.1))
  omega

private theorem square_and_third_coprime
    {x y z : ℤ} (hcop : IsCoprime x y)
    (hcurve : x ^ 4 - y ^ 4 = z ^ 2) :
    IsCoprime (y ^ 2) z := by
  rw [Int.isCoprime_iff_gcd_eq_one] at hcop ⊢
  by_contra hnot
  obtain ⟨p, hp, hpy, hpz⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  rw [← Int.natCast_dvd] at hpy hpz
  have hpxpow : (p : ℤ) ∣ x ^ 4 := by
    have hrewrite : x ^ 4 = y ^ 4 + z ^ 2 := by
      linear_combination hcurve
    rw [hrewrite]
    exact dvd_add (by
      rw [show y ^ 4 = y ^ 2 * y ^ 2 by ring]
      exact hpy.mul_right _) (by
      rw [show z ^ 2 = z * z by ring]
      exact hpz.mul_right _)
  have hpx : p ∣ Int.natAbs x :=
    Int.Prime.dvd_pow hp hpxpow
  have hpy' : p ∣ Int.natAbs y :=
    Int.Prime.dvd_pow hp hpy
  apply hp.not_dvd_one
  rw [← hcop]
  exact Nat.dvd_gcd hpx hpy'

private theorem square_measure_lt_of_sq_add_sq
    {a b x : ℤ} (hb : b ≠ 0) (h : x ^ 2 = a ^ 2 + b ^ 2) :
    Int.natAbs (a ^ 2) < Int.natAbs (x ^ 2) := by
  apply Int.ofNat_lt.mp
  rw [Int.natAbs_of_nonneg (sq_nonneg a),
    Int.natAbs_of_nonneg (sq_nonneg x), h]
  exact lt_add_of_pos_right _ (sq_pos_of_ne_zero hb)

private theorem positive_coprime_factors_of_square
    {a b c : ℤ} (ha : 0 < a) (hb : 0 < b) (hcop : IsCoprime a b)
    (hmul : a * b = c ^ 2) :
    ∃ r s : ℤ, a = r ^ 2 ∧ b = s ^ 2 ∧ r ≠ 0 ∧ s ≠ 0 := by
  obtain ⟨r, hr⟩ := Int.sq_of_isCoprime hcop hmul
  have hr' : a = r ^ 2 := Or.resolve_right hr (by
    intro hneg
    have := sq_nonneg r
    nlinarith)
  have hmul' : b * a = c ^ 2 := by simpa only [mul_comm] using hmul
  obtain ⟨s, hs⟩ := Int.sq_of_isCoprime hcop.symm hmul'
  have hs' : b = s ^ 2 := Or.resolve_right hs (by
    intro hneg
    have := sq_nonneg s
    nlinarith)
  exact ⟨r, s, hr', hs',
    fun hr0 ↦ by rw [hr0, zero_pow two_ne_zero] at hr'; omega,
    fun hs0 ↦ by rw [hs0, zero_pow two_ne_zero] at hs'; omega⟩

private theorem even_factor_of_twice_product_square
    {a b q : ℤ} (ha : 0 < a) (hb : 0 < b) (hcop : IsCoprime a b)
    (haeven : a % 2 = 0) (hsq : q ^ 2 = 2 * a * b) :
    ∃ r s : ℤ, a = 2 * r ^ 2 ∧ b = s ^ 2 ∧ r ≠ 0 ∧ s ≠ 0 := by
  have htwoa : (2 : ℤ) ∣ a := Int.dvd_of_emod_eq_zero haeven
  obtain ⟨a', ha'⟩ := htwoa
  have htwoq : (2 : ℤ) ∣ q := by
    apply Int.Prime.dvd_pow' Nat.prime_two
    rw [hsq]
    exact ⟨a * b, by ring⟩
  obtain ⟨q', hq'⟩ := htwoq
  have hcop' : IsCoprime a' b := by
    rw [ha'] at hcop
    exact hcop.of_mul_left_right
  have ha'pos : 0 < a' := by nlinarith
  have hsq' : a' * b = q' ^ 2 := by
    rw [hq', ha'] at hsq
    nlinarith
  obtain ⟨r, s, hr, hs, hr0, hs0⟩ :=
    positive_coprime_factors_of_square ha'pos hb hcop' hsq'
  exact ⟨r, s, by rw [ha', hr], hs, hr0, hs0⟩

private theorem descend_from_even_parameter
    {x evenParam oddParam r s : ℤ}
    (hx : x ≠ 0) (hcop : IsCoprime oddParam evenParam)
    (hoddParity : oddParam % 2 = 1)
    (heven : evenParam = 2 * r ^ 2) (hodd : oddParam = s ^ 2)
    (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hxsum : x ^ 2 = evenParam ^ 2 + oddParam ^ 2) :
    ∃ x' y' z' : ℤ, IsSolution x' y' z' ∧
      Int.natAbs (x' ^ 2) < Int.natAbs (x ^ 2) := by
  have ht : PythagoreanTriple oddParam evenParam |x| := by
    unfold PythagoreanTriple
    rw [show oddParam * oddParam = oddParam ^ 2 by ring,
      show evenParam * evenParam = evenParam ^ 2 by ring,
      show |x| * |x| = x ^ 2 by rw [← sq, sq_abs]]
    rw [add_comm, ← hxsum]
  have hcopGcd : Int.gcd oddParam evenParam = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp hcop
  obtain ⟨u, v, hodduv, hevenuv, hxuv, huvcop, _, hunonneg⟩ :=
    ht.coprime_classification' hcopGcd hoddParity (abs_pos.mpr hx)
  have huv : u * v = r ^ 2 := by
    rw [heven] at hevenuv
    nlinarith
  have huvpos : 0 < u * v := by
    rw [huv]
    exact sq_pos_of_ne_zero hr0
  have hvpos : 0 < v :=
    pos_of_mul_pos_right huvpos hunonneg
  have hupos : 0 < u :=
    pos_of_mul_pos_left huvpos (le_of_lt hvpos)
  obtain ⟨a, b, hua, hvb, ha0, hb0⟩ :=
    positive_coprime_factors_of_square hupos hvpos
      (Int.isCoprime_iff_gcd_eq_one.mpr huvcop) huv
  have hnew : IsSolution a b s := by
    refine ⟨ha0, hb0, hs0, ?_⟩
    calc
      a ^ 4 - b ^ 4 = u ^ 2 - v ^ 2 := by rw [hua, hvb]; ring
      _ = oddParam := hodduv.symm
      _ = s ^ 2 := hodd
  have hux : u < x ^ 2 := by
    have huabs : u < |x| := by
      rw [hxuv]
      exact lt_of_le_of_lt (Int.le_self_sq u)
        (lt_add_of_pos_right _ (sq_pos_of_ne_zero (ne_of_gt hvpos)))
    have habsx : |x| ≤ x ^ 2 := by
      simpa only [Int.natCast_natAbs] using Int.natAbs_le_self_sq x
    exact huabs.trans_le habsx
  have hmeasure : Int.natAbs (a ^ 2) < Int.natAbs (x ^ 2) := by
    apply Int.ofNat_lt.mp
    rw [Int.natAbs_of_nonneg (sq_nonneg a),
      Int.natAbs_of_nonneg (sq_nonneg x), ← hua]
    exact hux
  exact ⟨a, b, s, hnew, hmeasure⟩

private theorem descend_of_odd
    {x y z : ℤ} (h : IsSolution x y z) (hcop : IsCoprime x y)
    (hyodd : y % 2 = 1) :
    ∃ x' y' z' : ℤ, IsSolution x' y' z' ∧
      Int.natAbs (x' ^ 2) < Int.natAbs (x ^ 2) := by
  have ht : PythagoreanTriple (y ^ 2) z (x ^ 2) := by
    unfold PythagoreanTriple
    rw [show y ^ 2 * y ^ 2 = y ^ 4 by ring,
      show z * z = z ^ 2 by ring, show x ^ 2 * x ^ 2 = x ^ 4 by ring]
    linear_combination -h.2.2.2
  have hlegs : Int.gcd (y ^ 2) z = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp
      (square_and_third_coprime hcop h.2.2.2)
  have hypar : y ^ 2 % 2 = 1 := by
    rw [sq, Int.mul_emod, hyodd]
    decide
  obtain ⟨m, n, hymn, hzmn, hxmn, hmncop, _, hmnonneg⟩ :=
    ht.coprime_classification' hlegs hypar (sq_pos_of_ne_zero h.1)
  have hm0 : m ≠ 0 := by
    intro hm
    apply h.2.2.1
    rw [hzmn, hm]
    ring
  have hn0 : n ≠ 0 := by
    intro hn
    apply h.2.2.1
    rw [hzmn, hn]
    ring
  have hnew : IsSolution m n (x * y) := by
    refine ⟨hm0, hn0, mul_ne_zero h.1 h.2.1, ?_⟩
    calc
      m ^ 4 - n ^ 4 = (m ^ 2 - n ^ 2) * (m ^ 2 + n ^ 2) := by ring
      _ = y ^ 2 * x ^ 2 := by rw [← hymn, ← hxmn]
      _ = (x * y) ^ 2 := by ring
  exact ⟨m, n, x * y, hnew,
    square_measure_lt_of_sq_add_sq hn0 hxmn⟩

private theorem descend_of_even
    {x y z : ℤ} (h : IsSolution x y z) (hcop : IsCoprime x y)
    (hyeven : y % 2 = 0) :
    ∃ x' y' z' : ℤ, IsSolution x' y' z' ∧
      Int.natAbs (x' ^ 2) < Int.natAbs (x ^ 2) := by
  have ht : PythagoreanTriple (y ^ 2) z (x ^ 2) := by
    unfold PythagoreanTriple
    rw [show y ^ 2 * y ^ 2 = y ^ 4 by ring,
      show z * z = z ^ 2 by ring, show x ^ 2 * x ^ 2 = x ^ 4 by ring]
    linear_combination -h.2.2.2
  have hlegs : Int.gcd (y ^ 2) z = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp
      (square_and_third_coprime hcop h.2.2.2)
  have hypar : y ^ 2 % 2 = 0 := by
    rw [sq, Int.mul_emod, hyeven]
    decide
  have hzodd : z % 2 = 1 := by
    rcases ht.even_odd_of_coprime hlegs with hpar | hpar
    · exact hpar.2
    · rw [hypar] at hpar
      exact (zero_ne_one hpar.1).elim
  have hlegs' : Int.gcd z (y ^ 2) = 1 := by
    rw [Int.gcd_comm]
    exact hlegs
  obtain ⟨m, n, hzmn, hymn, hxmn, hmncop, hmnpar, hmnonneg⟩ :=
    ht.symm.coprime_classification' hlegs' hzodd (sq_pos_of_ne_zero h.1)
  have hm0 : m ≠ 0 := by
    intro hm
    apply h.2.1
    apply sq_eq_zero_iff.mp
    rw [hymn, hm]
    ring
  have hmpos : 0 < m :=
    lt_of_le_of_ne hmnonneg (Ne.symm hm0)
  have hmnpos : 0 < m * n := by
    have hypos : 0 < y ^ 2 := sq_pos_of_ne_zero h.2.1
    nlinarith [hymn]
  have hnpos : 0 < n :=
    pos_of_mul_pos_right hmnpos hmnonneg
  have hmncop' : IsCoprime m n :=
    Int.isCoprime_iff_gcd_eq_one.mpr hmncop
  rcases hmnpar with hpar | hpar
  · obtain ⟨r, s, hm, hn, hr0, hs0⟩ :=
      even_factor_of_twice_product_square hmpos hnpos hmncop'
        hpar.1 hymn
    exact descend_from_even_parameter h.1 hmncop'.symm hpar.2
      hm hn hr0 hs0 hxmn
  · have hymn' : y ^ 2 = 2 * n * m := by
      simpa only [mul_comm, mul_left_comm] using hymn
    obtain ⟨r, s, hn, hm, hr0, hs0⟩ :=
      even_factor_of_twice_product_square hnpos hmpos hmncop'.symm
        hpar.2 hymn'
    have hxmn' : x ^ 2 = n ^ 2 + m ^ 2 := by
      simpa only [add_comm] using hxmn
    exact descend_from_even_parameter h.1 hmncop' hpar.1
      hn hm hr0 hs0 hxmn'

/--
Fermat's quartic-difference theorem: a nonzero square is not the difference
of two nonzero fourth powers.

The assumption `hz` is necessary.  Without it, `x = y ≠ 0` gives the
degenerate identity `x⁴ - y⁴ = 0²`.
-/
theorem sq_ne_quartic_sub_quartic
    {x y z : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    x ^ 4 - y ^ 4 ≠ z ^ 2 := by
  intro hcurve
  obtain ⟨x₀, y₀, z₀, hmin⟩ :=
    exists_minimal (show IsSolution x y z from ⟨hx, hy, hz, hcurve⟩)
  have hcop : IsCoprime x₀ y₀ :=
    coprime_of_minimal hmin
  obtain hyeven | hyodd := Int.emod_two_eq_zero_or_one y₀
  · obtain ⟨x', y', z', hnew, hlt⟩ :=
      descend_of_even hmin.1 hcop hyeven
    exact (not_lt_of_ge (hmin.2 x' y' z' hnew)) hlt
  · obtain ⟨x', y', z', hnew, hlt⟩ :=
      descend_of_odd hmin.1 hcop hyodd
    exact (not_lt_of_ge (hmin.2 x' y' z' hnew)) hlt

end MazurTorsion.QuarticDifference

end


/- Source module: MazurTorsion.Kubert.OrderSixteenReduction. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Elimination of a rational point of order sixteen

The elementary part of the order-sixteen argument ends on the hyperelliptic
curve

`v² = (u² - 1)(u² + 1)(u² + 2u - 1)`.

This file first proves the arithmetic obstruction for this curve.  The proof
clears denominators and splits according to their parity.  Opposite parity
produces a nonzero square which is a difference of fourth powers; odd/odd
parity produces a forbidden solution of `a⁴ + b⁴ = c²`.

The second part records the duplication identities which connect an
order-sixteen chain

`R, 2R, 4R, 8R`

on a normalized Weierstrass equation `Y² = X³ + aX² + bX` to the displayed
curve.
-/

namespace MazurTorsion.Kubert

open scoped WeierstrassCurve.Affine

/-- The short model used after translating the final two-torsion point to
the origin and completing the square. -/
def normalizedCurve (a b : ℚ) : WeierstrassCurve ℚ :=
  ⟨0, a, 0, b, 0⟩

private lemma normalized_curve_equation
    {a b x y : ℚ}
    (h : (normalizedCurve a b).toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 + a * x ^ 2 + b * x := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simpa [normalizedCurve] using heq

private lemma normalized_duplication_identity_algebra
    {a b x y x₂ : ℚ} (hy : y ≠ 0)
    (hcurve : y ^ 2 = x ^ 3 + a * x ^ 2 + b * x)
    (hx₂ :
      x₂ =
        ((3 * x ^ 2 + 2 * a * x + b) / (2 * y)) ^ 2 -
          a - 2 * x) :
    x₂ * (2 * y) ^ 2 = (x ^ 2 - b) ^ 2 := by
  rw [hx₂]
  field_simp [hy]
  linear_combination -4 * (a + 2 * x) * hcurve

/-- The denominator-free duplication identity on `normalizedCurve`. -/
lemma normalized_duplication_identity_of_double
    {a b x y x₂ y₂ : ℚ}
    [_hE : (normalizedCurve a b).IsElliptic]
    (hP : (normalizedCurve a b).toAffine.Nonsingular x y)
    (hP₂ : (normalizedCurve a b).toAffine.Nonsingular x₂ y₂)
    (hdouble :
      (2 : ℕ) •
          WeierstrassCurve.Affine.Point.some x y hP =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂) :
    x₂ * (2 * y) ^ 2 = (x ^ 2 - b) ^ 2 := by
  let W := normalizedCurve a b
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    have hzero :
        (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 := by
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
    rw [hzero] at hdouble
    exact WeierstrassCurve.Affine.Point.some_ne_zero hP₂ hdouble.symm
  have hy0 : y ≠ 0 := by
    intro hy0
    apply hy
    simp [W, normalizedCurve, WeierstrassCurve.Affine.negY, hy0]
  let ℓ := W.toAffine.slope x x y y
  have hadd :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne
      (W := W.toAffine) (h₁ := hP) hy
  have hx₂ : W.toAffine.addX x x ℓ = x₂ := by
    have hsum :
        WeierstrassCurve.Affine.Point.some x y hP +
            WeierstrassCurve.Affine.Point.some x y hP =
          WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
      simpa [two_nsmul] using hdouble
    exact (WeierstrassCurve.Affine.Point.some.inj
      (hadd.symm.trans hsum)).1
  have hℓ :
      ℓ = (3 * x ^ 2 + 2 * a * x + b) / (2 * y) := by
    dsimp [ℓ]
    rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hy]
    simp only [WeierstrassCurve.Affine.negY]
    simp [W, normalizedCurve]
    ring
  apply normalized_duplication_identity_algebra hy0
    (normalized_curve_equation hP)
  rw [← hx₂]
  simp only [WeierstrassCurve.Affine.addX]
  rw [hℓ]
  simp [W, normalizedCurve]
  ring

private lemma isCoprime_sub_sq_left
    {m n : ℤ} (hmn : IsCoprime m n) :
    IsCoprime (m ^ 2 - n ^ 2) n := by
  have hsq : IsCoprime (m ^ 2) n := hmn.pow_left
  simpa only [pow_two, sub_eq_add_neg, mul_neg] using
    (hsq.add_mul_left_left (-n))

private lemma isCoprime_add_sq_left
    {m n : ℤ} (hmn : IsCoprime m n) :
    IsCoprime (m ^ 2 + n ^ 2) n := by
  have hsq : IsCoprime (m ^ 2) n := hmn.pow_left
  simpa [pow_two] using
    (hsq.add_mul_left_left n)

private lemma odd_sq_sub_sq_of_opposite_parity
    {m n : ℤ}
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨
      (m % 2 = 1 ∧ n % 2 = 0)) :
    Odd (m ^ 2 - n ^ 2) := by
  rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · obtain ⟨m₀, hm₀⟩ := Int.dvd_of_emod_eq_zero hm
    obtain ⟨n₀, hn₀⟩ :=
      exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hn)
    rw [sub_eq_iff_eq_add] at hn₀
    rw [Int.odd_iff]
    have hform :
        m ^ 2 - n ^ 2 =
          2 * (2 * m₀ ^ 2 - 2 * n₀ ^ 2 - 2 * n₀ - 1) + 1 := by
      rw [hm₀, hn₀]
      ring
    rw [hform]
    omega
  · obtain ⟨n₀, hn₀⟩ := Int.dvd_of_emod_eq_zero hn
    obtain ⟨m₀, hm₀⟩ :=
      exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hm)
    rw [sub_eq_iff_eq_add] at hm₀
    rw [Int.odd_iff]
    have hform :
        m ^ 2 - n ^ 2 =
          2 * (2 * m₀ ^ 2 + 2 * m₀ - 2 * n₀ ^ 2) + 1 := by
      rw [hm₀, hn₀]
      ring
    rw [hform]
    omega

private lemma odd_sq_add_sq_of_opposite_parity
    {m n : ℤ}
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨
      (m % 2 = 1 ∧ n % 2 = 0)) :
    Odd (m ^ 2 + n ^ 2) := by
  rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · obtain ⟨m₀, hm₀⟩ := Int.dvd_of_emod_eq_zero hm
    obtain ⟨n₀, hn₀⟩ :=
      exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hn)
    rw [sub_eq_iff_eq_add] at hn₀
    rw [Int.odd_iff]
    have hform :
        m ^ 2 + n ^ 2 =
          2 * (2 * m₀ ^ 2 + 2 * n₀ ^ 2 + 2 * n₀) + 1 := by
      rw [hm₀, hn₀]
      ring
    rw [hform]
    omega
  · obtain ⟨n₀, hn₀⟩ := Int.dvd_of_emod_eq_zero hn
    obtain ⟨m₀, hm₀⟩ :=
      exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hm)
    rw [sub_eq_iff_eq_add] at hm₀
    rw [Int.odd_iff]
    have hform :
        m ^ 2 + n ^ 2 =
          2 * (2 * m₀ ^ 2 + 2 * m₀ + 2 * n₀ ^ 2) + 1 := by
      rw [hm₀, hn₀]
      ring
    rw [hform]
    omega

private lemma odd_sub_of_opposite_parity
    {m n : ℤ}
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨
      (m % 2 = 1 ∧ n % 2 = 0)) :
    Odd (m - n) := by
  rcases hpar with ⟨hm, hn⟩ | ⟨hm, hn⟩
  · obtain ⟨m₀, hm₀⟩ := Int.dvd_of_emod_eq_zero hm
    obtain ⟨n₀, hn₀⟩ :=
      exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hn)
    rw [sub_eq_iff_eq_add] at hn₀
    refine ⟨m₀ - n₀ - 1, ?_⟩
    rw [hm₀, hn₀]
    ring
  · obtain ⟨n₀, hn₀⟩ := Int.dvd_of_emod_eq_zero hn
    obtain ⟨m₀, hm₀⟩ :=
      exists_eq_mul_left_of_dvd (Int.dvd_self_sub_of_emod_eq hm)
    rw [sub_eq_iff_eq_add] at hm₀
    refine ⟨m₀ - n₀, ?_⟩
    rw [hm₀, hn₀]
    ring

private lemma opposite_parity_pairwise_coprime
    {m n : ℤ} (hmn : IsCoprime m n)
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨
      (m % 2 = 1 ∧ n % 2 = 0)) :
    IsCoprime (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) ∧
      IsCoprime (m ^ 2 - n ^ 2) (m ^ 2 + 2 * m * n - n ^ 2) ∧
      IsCoprime (m ^ 2 + n ^ 2) (m ^ 2 + 2 * m * n - n ^ 2) := by
  have hAq : IsCoprime (m ^ 2 - n ^ 2) n :=
    isCoprime_sub_sq_left hmn
  have hAp : IsCoprime (m ^ 2 - n ^ 2) m := by
    have h := isCoprime_sub_sq_left hmn.symm
    simpa only [neg_sub] using h.neg_left
  have hA2 : IsCoprime (m ^ 2 - n ^ 2) 2 :=
    Int.isCoprime_two_right.mpr
      (odd_sq_sub_sq_of_opposite_parity hpar)
  have hA2q2 : IsCoprime (m ^ 2 - n ^ 2) (2 * n ^ 2) :=
    hA2.mul_right hAq.pow_right
  have hAB : IsCoprime (m ^ 2 - n ^ 2) (m ^ 2 + n ^ 2) := by
    have h := hA2q2.add_mul_left_right 1
    rw [show 2 * n ^ 2 + (m ^ 2 - n ^ 2) * 1 =
      m ^ 2 + n ^ 2 by ring] at h
    exact h
  have hA2mn : IsCoprime (m ^ 2 - n ^ 2) (2 * m * n) :=
    (hA2.mul_right hAp).mul_right hAq
  have hAC :
    IsCoprime (m ^ 2 - n ^ 2) (m ^ 2 + 2 * m * n - n ^ 2) := by
    have h := hA2mn.add_mul_left_right 1
    rw [show 2 * m * n + (m ^ 2 - n ^ 2) * 1 =
      m ^ 2 + 2 * m * n - n ^ 2 by ring] at h
    exact h
  have hBq : IsCoprime (m ^ 2 + n ^ 2) n :=
    isCoprime_add_sq_left hmn
  have hB2 : IsCoprime (m ^ 2 + n ^ 2) 2 :=
    Int.isCoprime_two_right.mpr
      (odd_sq_add_sq_of_opposite_parity hpar)
  have hDq : IsCoprime (m - n) n := by
    have h := hmn.add_mul_left_left (-1)
    rw [show m + n * (-1) = m - n by ring] at h
    exact h
  have hD2 : IsCoprime (m - n) 2 :=
    Int.isCoprime_two_right.mpr (odd_sub_of_opposite_parity hpar)
  have hD2q2 : IsCoprime (m - n) (2 * n ^ 2) :=
    hD2.mul_right hDq.pow_right
  have hBD : IsCoprime (m ^ 2 + n ^ 2) (m - n) := by
    have h := hD2q2.symm.add_mul_left_left (m + n)
    rw [show 2 * n ^ 2 + (m - n) * (m + n) =
      m ^ 2 + n ^ 2 by ring] at h
    exact h
  have hB2qD : IsCoprime (m ^ 2 + n ^ 2) (2 * n * (m - n)) :=
    (hB2.mul_right hBq).mul_right hBD
  have hBC :
      IsCoprime (m ^ 2 + n ^ 2) (m ^ 2 + 2 * m * n - n ^ 2) := by
    have h := hB2qD.add_mul_left_right 1
    rw [show 2 * n * (m - n) + (m ^ 2 + n ^ 2) * 1 =
      m ^ 2 + 2 * m * n - n ^ 2 by ring] at h
    exact h
  exact ⟨hAB, hAC, hBC⟩

private theorem no_opposite_parity_certificate
    {m n z : ℤ} (hmn : IsCoprime m n) (hm : m ≠ 0) (hn : n ≠ 0)
    (hA : m ^ 2 - n ^ 2 ≠ 0)
    (hpar : (m % 2 = 0 ∧ n % 2 = 1) ∨
      (m % 2 = 1 ∧ n % 2 = 0))
    (hprod :
      (m ^ 2 - n ^ 2) * (m ^ 2 + n ^ 2) *
        (m ^ 2 + 2 * m * n - n ^ 2) = z ^ 2) :
    False := by
  obtain ⟨hAB, hAC, hBC⟩ :=
    opposite_parity_pairwise_coprime hmn hpar
  obtain ⟨a, ha⟩ : ∃ a : ℤ,
      m ^ 2 - n ^ 2 = a ^ 2 ∨ m ^ 2 - n ^ 2 = -a ^ 2 := by
    apply Int.sq_of_isCoprime (hAB.mul_right hAC) (c := z)
    linear_combination hprod
  obtain ⟨b, hb⟩ : ∃ b : ℤ,
      m ^ 2 + n ^ 2 = b ^ 2 ∨ m ^ 2 + n ^ 2 = -b ^ 2 := by
    apply Int.sq_of_isCoprime (hAB.symm.mul_right hBC) (c := z)
    linear_combination hprod
  have hBpos : 0 < m ^ 2 + n ^ 2 := by
    positivity
  have hbpos : m ^ 2 + n ^ 2 = b ^ 2 := by
    rcases hb with hb | hb
    · exact hb
    · nlinarith [sq_nonneg b]
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    rcases ha with ha | ha <;> norm_num at ha <;> exact hA ha
  have hb0 : b ≠ 0 := by
    intro hb0
    subst b
    norm_num at hbpos
    nlinarith [sq_pos_of_ne_zero hm, sq_pos_of_ne_zero hn]
  have hmn0 : 2 * m * n ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hm) hn
  apply MazurTorsion.QuarticDifference.sq_ne_quartic_sub_quartic
    hb0 ha0 hmn0
  calc
    b ^ 4 - a ^ 4 = (b ^ 2) ^ 2 - (a ^ 2) ^ 2 := by ring
    _ = (m ^ 2 + n ^ 2) ^ 2 - (m ^ 2 - n ^ 2) ^ 2 := by
      rcases ha with ha | ha
      · rw [← hbpos, ← ha]
      · rw [← hbpos, ha]
        ring
    _ = (2 * m * n) ^ 2 := by ring

private lemma opposite_parity_of_odd_sum
    {r s : ℤ} (hodd : Odd (r + s)) :
    (r % 2 = 0 ∧ s % 2 = 1) ∨
      (r % 2 = 1 ∧ s % 2 = 0) := by
  rw [Int.odd_iff] at hodd
  rcases Int.emod_two_eq_zero_or_one r with hr | hr <;>
    rcases Int.emod_two_eq_zero_or_one s with hs | hs <;> omega

private theorem no_odd_odd_certificate
    {m n z : ℤ} (hmn : IsCoprime m n)
    (hmOdd : Odd m) (hnOdd : Odd n)
    (hA : m ^ 2 - n ^ 2 ≠ 0)
    (hprod :
      (m ^ 2 - n ^ 2) * (m ^ 2 + n ^ 2) *
        (m ^ 2 + 2 * m * n - n ^ 2) = z ^ 2) :
    False := by
  obtain ⟨m₀, hm₀⟩ :=
    exists_eq_mul_left_of_dvd
      (Int.dvd_self_sub_of_emod_eq (Int.odd_iff.mp hmOdd))
  obtain ⟨n₀, hn₀⟩ :=
    exists_eq_mul_left_of_dvd
      (Int.dvd_self_sub_of_emod_eq (Int.odd_iff.mp hnOdd))
  rw [sub_eq_iff_eq_add] at hm₀ hn₀
  let r : ℤ := m₀ + n₀ + 1
  let s : ℤ := m₀ - n₀
  have hmrs : m = r + s := by
    rw [hm₀]
    simp only [r, s]
    ring
  have hnrs : n = r - s := by
    rw [hn₀]
    simp only [r, s]
    ring
  have hrs : IsCoprime r s := by
    obtain ⟨u, v, huv⟩ := hmn
    refine ⟨u + v, u - v, ?_⟩
    rw [hmrs, hnrs] at huv
    linear_combination huv
  have hrsParity :
      (r % 2 = 0 ∧ s % 2 = 1) ∨
        (r % 2 = 1 ∧ s % 2 = 0) := by
    apply opposite_parity_of_odd_sum
    rw [← hmrs]
    exact hmOdd
  have hpair := opposite_parity_pairwise_coprime hrs hrsParity
  have hKrs :
      IsCoprime (r ^ 2 + s ^ 2) (r * s) :=
    Int.isCoprime_of_sq_sum' hrs
  have hKr : IsCoprime (r ^ 2 + s ^ 2) r :=
    hKrs.of_mul_right_left
  have hKs : IsCoprime (r ^ 2 + s ^ 2) s :=
    hKrs.of_mul_right_right
  have hDr :
      IsCoprime (r ^ 2 + 2 * r * s - s ^ 2) r := by
    have h :=
      (hrs.symm.pow_left (m := 2)).neg_left.add_mul_left_left (r + 2 * s)
    rw [show -(s ^ 2) + r * (r + 2 * s) =
      r ^ 2 + 2 * r * s - s ^ 2 by ring] at h
    exact h
  have hDs :
      IsCoprime (r ^ 2 + 2 * r * s - s ^ 2) s := by
    have h := (hrs.pow_left (m := 2)).add_mul_left_left (2 * r - s)
    rw [show r ^ 2 + s * (2 * r - s) =
      r ^ 2 + 2 * r * s - s ^ 2 by ring] at h
    exact h
  have hKD :
      IsCoprime (r ^ 2 + s ^ 2) (r ^ 2 + 2 * r * s - s ^ 2) :=
    hpair.2.2
  have hscaled :
      16 * (r * s * (r ^ 2 + s ^ 2) *
        (r ^ 2 + 2 * r * s - s ^ 2)) = z ^ 2 := by
    rw [← hprod, hmrs, hnrs]
    ring
  have hfourPow : (4 : ℤ) ^ 2 ∣ z ^ 2 := by
    refine ⟨r * s * (r ^ 2 + s ^ 2) *
      (r ^ 2 + 2 * r * s - s ^ 2), ?_⟩
    rw [← hscaled]
    ring
  have hfour : (4 : ℤ) ∣ z :=
    (Int.pow_dvd_pow_iff two_ne_zero).mp hfourPow
  obtain ⟨w, hw⟩ := hfour
  have hsmall :
      r * s * (r ^ 2 + s ^ 2) *
        (r ^ 2 + 2 * r * s - s ^ 2) = w ^ 2 := by
    rw [hw] at hscaled
    nlinarith
  have hrD :
      IsCoprime r (r ^ 2 + 2 * r * s - s ^ 2) :=
    hDr.symm
  have hsD :
      IsCoprime s (r ^ 2 + 2 * r * s - s ^ 2) :=
    hDs.symm
  have hrK : IsCoprime r (r ^ 2 + s ^ 2) := hKr.symm
  have hsK : IsCoprime s (r ^ 2 + s ^ 2) := hKs.symm
  obtain ⟨a, ha⟩ : ∃ a : ℤ, r = a ^ 2 ∨ r = -a ^ 2 := by
    apply Int.sq_of_isCoprime
      ((hrs.mul_right hrK).mul_right hrD) (c := w)
    linear_combination hsmall
  obtain ⟨b, hb⟩ : ∃ b : ℤ, s = b ^ 2 ∨ s = -b ^ 2 := by
    apply Int.sq_of_isCoprime
      ((hrs.symm.mul_right hsK).mul_right hsD) (c := w)
    linear_combination hsmall
  obtain ⟨c, hc⟩ : ∃ c : ℤ,
      r ^ 2 + s ^ 2 = c ^ 2 ∨ r ^ 2 + s ^ 2 = -c ^ 2 := by
    apply Int.sq_of_isCoprime
      ((hKr.mul_right hKs).mul_right hKD) (c := w)
    linear_combination hsmall
  have hrs0 : r * s ≠ 0 := by
    intro hrs0
    apply hA
    rw [hmrs, hnrs]
    rcases mul_eq_zero.mp hrs0 with hr0 | hs0
    · simp [hr0]
    · simp [hs0]
  have hr0 : r ≠ 0 := fun hr0 ↦ hrs0 (by simp [hr0])
  have hs0 : s ≠ 0 := fun hs0 ↦ hrs0 (by simp [hs0])
  have hKpos : 0 < r ^ 2 + s ^ 2 := by
    nlinarith [sq_pos_of_ne_zero hr0, sq_pos_of_ne_zero hs0]
  have hcpos : r ^ 2 + s ^ 2 = c ^ 2 := by
    rcases hc with hc | hc
    · exact hc
    · nlinarith [sq_nonneg c]
  have ha0 : a ≠ 0 := by
    intro ha0
    subst a
    rcases ha with ha | ha <;> norm_num at ha <;> exact hr0 ha
  have hb0 : b ≠ 0 := by
    intro hb0
    subst b
    rcases hb with hb | hb <;> norm_num at hb <;> exact hs0 hb
  apply not_fermat_42 ha0 hb0
  calc
    a ^ 4 + b ^ 4 = (a ^ 2) ^ 2 + (b ^ 2) ^ 2 := by ring
    _ = r ^ 2 + s ^ 2 := by
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · rw [← ha, ← hb]
      · rw [← ha, hb]
        ring
      · rw [ha, ← hb]
        ring
      · rw [ha, hb]
        ring
    _ = c ^ 2 := hcpos

/-- Clearing denominators on the `X₁(16)` sextic gives the integral
three-factor certificate used by both parity branches. -/
lemma integral_certificate_of_sextic_solution
    {u v : ℚ}
    (hcurve :
      v ^ 2 = (u ^ 2 - 1) * (u ^ 2 + 1) *
        (u ^ 2 + 2 * u - 1)) :
    IsSquare
      ((u.num ^ 2 - (u.den : ℤ) ^ 2) *
        (u.num ^ 2 + (u.den : ℤ) ^ 2) *
        (u.num ^ 2 + 2 * u.num * (u.den : ℤ) -
          (u.den : ℤ) ^ 2)) := by
  let m : ℤ := u.num
  let n : ℤ := u.den
  let A : ℤ := m ^ 2 - n ^ 2
  let B : ℤ := m ^ 2 + n ^ 2
  let C : ℤ := m ^ 2 + 2 * m * n - n ^ 2
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast u.den_ne_zero
  have hu : u = (m : ℚ) / n := u.num_div_den.symm
  have hscaled :
      (v * (n : ℚ) ^ 3) ^ 2 = (((A * B * C : ℤ) : ℚ)) := by
    calc
      (v * (n : ℚ) ^ 3) ^ 2 = v ^ 2 * (n : ℚ) ^ 6 := by ring
      _ = (((m : ℚ) ^ 2 - (n : ℚ) ^ 2) *
          ((m : ℚ) ^ 2 + (n : ℚ) ^ 2) *
          ((m : ℚ) ^ 2 + 2 * (m : ℚ) * n - (n : ℚ) ^ 2)) := by
        rw [hcurve, hu]
        field_simp [hn0]
      _ = (((A * B * C : ℤ) : ℚ)) := by
        dsimp [A, B, C]
        push_cast
        ring
  have hsquareRat : IsSquare (((A * B * C : ℤ) : ℚ)) :=
    ⟨v * (n : ℚ) ^ 3, by simpa [pow_two] using hscaled.symm⟩
  rw [← Rat.isSquare_intCast_iff]
  simpa [A, B, C, m, n] using hsquareRat

/-- The noncuspidal part of the rational `X₁(16)` sextic has no points.

The excluded equality `u² = 1` is exactly the degenerate numerator factor.
It is the nondegeneracy condition supplied by the order-eight and order-four
members of the duplication chain. -/
theorem no_nondegenerate_sextic_solution
    {u v : ℚ} (hu : u ≠ 0) (huOne : u ^ 2 ≠ 1) :
    v ^ 2 ≠
      (u ^ 2 - 1) * (u ^ 2 + 1) *
        (u ^ 2 + 2 * u - 1) := by
  intro hcurve
  let m : ℤ := u.num
  let n : ℤ := u.den
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den u
  have hm : m ≠ 0 := by
    dsimp [m]
    exact Rat.num_ne_zero.mpr hu
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast u.den_ne_zero
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have huFrac : u = (m : ℚ) / n := u.num_div_den.symm
  have hA : m ^ 2 - n ^ 2 ≠ 0 := by
    intro hA0
    apply huOne
    rw [huFrac]
    field_simp [hnq]
    exact_mod_cast (sub_eq_zero.mp hA0)
  obtain ⟨z, hz⟩ :=
    integral_certificate_of_sextic_solution hcurve
  have hprod :
      (m ^ 2 - n ^ 2) * (m ^ 2 + n ^ 2) *
        (m ^ 2 + 2 * m * n - n ^ 2) = z ^ 2 := by
    simpa [m, n, pow_two] using hz
  rcases Int.emod_two_eq_zero_or_one m with hmEven | hmOdd
  · rcases Int.emod_two_eq_zero_or_one n with hnEven | hnOdd
    · have htwoM : (2 : ℤ) ∣ m := Int.dvd_of_emod_eq_zero hmEven
      have htwoN : (2 : ℤ) ∣ n := Int.dvd_of_emod_eq_zero hnEven
      have hunit : IsUnit (2 : ℤ) :=
        hmn.isUnit_of_dvd' htwoM htwoN
      exact (by norm_num [Int.isUnit_iff] at hunit)
    · exact no_opposite_parity_certificate hmn hm hn hA
        (Or.inl ⟨hmEven, hnOdd⟩) hprod
  · rcases Int.emod_two_eq_zero_or_one n with hnEven | hnOdd
    · exact no_opposite_parity_certificate hmn hm hn hA
        (Or.inr ⟨hmOdd, hnEven⟩) hprod
    · exact no_odd_odd_certificate hmn
        (Int.odd_iff.mpr hmOdd) (Int.odd_iff.mpr hnOdd) hA hprod

private lemma sextic_solution_of_square_relation
    {n ξ : ℚ} (hn : n ≠ 0) (hξ : ξ ≠ 0) (hnOne : n ^ 2 ≠ 1)
    (hsquare :
      (n * (ξ ^ 2 + 1) - 2 * n ^ 3 * ξ) ^ 2 =
        (ξ * (n ^ 4 - 1)) ^ 2) :
    ∃ N V : ℚ, N ≠ 0 ∧ N ^ 2 ≠ 1 ∧
      V ^ 2 =
        (N ^ 2 - 1) * (N ^ 2 + 1) *
          (N ^ 2 + 2 * N - 1) := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hplus | hminus
  · have hnPlus : n + 1 ≠ 0 := by
      intro hnPlus
      apply hnOne
      have hnNeg : n = -1 := by linarith
      rw [hnNeg]
      norm_num
    have hlinear :
        n * (ξ ^ 2 + 1) =
          ξ * (2 * n ^ 3 + n ^ 4 - 1) := by
      linear_combination hplus
    refine ⟨n, n * (ξ ^ 2 - 1) / (ξ * (n + 1)),
      hn, hnOne, ?_⟩
    field_simp [hξ, hnPlus]
    linear_combination
      (n * (ξ ^ 2 + 1) +
        ξ * (2 * n ^ 3 + n ^ 4 - 1)) * hlinear
  · have hnMinus : 1 - n ≠ 0 := by
      intro hnMinus
      apply hnOne
      have hnPos : n = 1 := by linarith
      rw [hnPos]
      norm_num
    have hlinear :
        n * (ξ ^ 2 + 1) =
          ξ * (2 * n ^ 3 - n ^ 4 + 1) := by
      linear_combination hminus
    refine ⟨-n, (-n) * (ξ ^ 2 - 1) / (ξ * (1 - n)),
      neg_ne_zero.mpr hn, ?_, ?_⟩
    · simpa only [neg_sq] using hnOne
    · field_simp [hξ, hnMinus]
      linear_combination
        (n * (ξ ^ 2 + 1) +
          ξ * (2 * n ^ 3 - n ^ 4 + 1)) * hlinear

/-- The two scaled duplication equations imply the difference-of-squares
identity from which the `X₁(16)` sextic is read off. -/
lemma square_relation_of_scaled_duplication
    {n s ξ : ℚ}
    (hP : 4 * s ^ 2 * n ^ 4 = (n ^ 2 - 1) ^ 4)
    (hR :
      4 * n ^ 2 * (ξ ^ 3 + (s ^ 2 - 2) * ξ ^ 2 + ξ) =
        (ξ ^ 2 - 1) ^ 2) :
    (n * (ξ ^ 2 + 1) - 2 * n ^ 3 * ξ) ^ 2 =
      (ξ * (n ^ 4 - 1)) ^ 2 := by
  linear_combination ξ ^ 2 * hP - n ^ 2 * hR

/-- Arithmetic endpoint for a normalized order-sixteen duplication chain.

These are precisely the two equations obtained after writing the successive
square `X`-coordinates as `X(4R)=g²`, `X(2R)=g²n²`, and scaling
`X(R)=g²ξ`. -/
theorem no_scaled_duplication_chain
    {n s ξ : ℚ} (hn : n ≠ 0) (hξ : ξ ≠ 0)
    (hnOne : n ^ 2 ≠ 1)
    (hP : 4 * s ^ 2 * n ^ 4 = (n ^ 2 - 1) ^ 4)
    (hR :
      4 * n ^ 2 * (ξ ^ 3 + (s ^ 2 - 2) * ξ ^ 2 + ξ) =
        (ξ ^ 2 - 1) ^ 2) :
    False := by
  have hsquare :=
    square_relation_of_scaled_duplication hP hR
  obtain ⟨N, V, hN, hNOne, hV⟩ :=
    sextic_solution_of_square_relation hn hξ hnOne hsquare
  exact no_nondegenerate_sextic_solution hN hNOne hV

private lemma first_scaled_identity
    {n s t : ℚ}
    (hcurve : t ^ 2 = n ^ 6 + (s ^ 2 - 2) * n ^ 4 + n ^ 2)
    (hdup : 4 * t ^ 2 = (n ^ 4 - 1) ^ 2) :
    4 * s ^ 2 * n ^ 4 = (n ^ 2 - 1) ^ 4 := by
  nlinarith [hcurve, hdup]

private lemma second_scaled_identity
    {n s ξ η : ℚ}
    (hcurve : η ^ 2 = ξ ^ 3 + (s ^ 2 - 2) * ξ ^ 2 + ξ)
    (hdup : 4 * n ^ 2 * η ^ 2 = (ξ ^ 2 - 1) ^ 2) :
    4 * n ^ 2 * (ξ ^ 3 + (s ^ 2 - 2) * ξ ^ 2 + ξ) =
      (ξ ^ 2 - 1) ^ 2 := by
  linear_combination -4 * n ^ 2 * hcurve + hdup

private lemma quotient_square_of_duplication
    {b x y x₂ : ℚ} (hy : y ≠ 0)
    (hdup : x₂ * (2 * y) ^ 2 = (x ^ 2 - b) ^ 2) :
    ((x ^ 2 - b) / (2 * y)) ^ 2 = x₂ := by
  field_simp [hy]
  nlinarith [hdup]

private theorem no_normalized_coordinate_duplication_chain_aux
    {a b xR yR xP yP xQ yQ f g : ℚ}
    (hRcurve : yR ^ 2 = xR ^ 3 + a * xR ^ 2 + b * xR)
    (hPcurve : yP ^ 2 = xP ^ 3 + a * xP ^ 2 + b * xP)
    (hQcurve : yQ ^ 2 = xQ ^ 3 + a * xQ ^ 2 + b * xQ)
    (hRP : xP * (2 * yR) ^ 2 = (xR ^ 2 - b) ^ 2)
    (hPQ : xQ * (2 * yP) ^ 2 = (xP ^ 2 - b) ^ 2)
    (hb : b = xQ ^ 2)
    (hf : f ^ 2 = xP) (hg : g ^ 2 = xQ)
    (hxR : xR ≠ 0) (hxP : xP ≠ 0) (hxQ : xQ ≠ 0)
    (hxPQ : xP ≠ xQ) :
    False := by
  have hf0 : f ≠ 0 := by
    intro hf0
    apply hxP
    rw [← hf, hf0]
    norm_num
  have hg0 : g ≠ 0 := by
    intro hg0
    apply hxQ
    rw [← hg, hg0]
    norm_num
  have hbg : b = g ^ 4 := by
    rw [hb, ← hg]
    ring
  let n : ℚ := f / g
  let s : ℚ := yQ / g ^ 3
  let ξ : ℚ := xR / g ^ 2
  let t : ℚ := yP / g ^ 3
  let η : ℚ := yR / g ^ 3
  have hn : n ≠ 0 := div_ne_zero hf0 hg0
  have hξ : ξ ≠ 0 := div_ne_zero hxR (pow_ne_zero 2 hg0)
  have hnOne : n ^ 2 ≠ 1 := by
    intro hnOne
    apply hxPQ
    rw [← hf, ← hg]
    dsimp [n] at hnOne
    field_simp [hg0] at hnOne
    exact hnOne
  have haScaled : a = g ^ 2 * (s ^ 2 - 2) := by
    dsimp [s]
    field_simp [hg0]
    rw [← hg, hbg] at hQcurve
    nlinarith [hQcurve]
  have hsCoeff : s ^ 2 - 2 = a / g ^ 2 := by
    rw [haScaled]
    field_simp [hg0]
  have hPscaled :
      t ^ 2 = n ^ 6 + (s ^ 2 - 2) * n ^ 4 + n ^ 2 := by
    rw [hsCoeff]
    dsimp [t, n]
    field_simp [hg0]
    rw [← hf, hbg] at hPcurve
    nlinarith [hPcurve]
  have hPQscaled :
      4 * t ^ 2 = (n ^ 4 - 1) ^ 2 := by
    dsimp [t, n]
    field_simp [hg0]
    rw [← hg, ← hf, hbg] at hPQ
    nlinarith [hPQ]
  have hPidentity : 4 * s ^ 2 * n ^ 4 = (n ^ 2 - 1) ^ 4 :=
    first_scaled_identity hPscaled hPQscaled
  have hRscaled :
      η ^ 2 = ξ ^ 3 + (s ^ 2 - 2) * ξ ^ 2 + ξ := by
    rw [hsCoeff]
    dsimp [η, ξ]
    field_simp [hg0]
    rw [hbg] at hRcurve
    nlinarith [hRcurve]
  have hRPscaled :
      4 * n ^ 2 * η ^ 2 = (ξ ^ 2 - 1) ^ 2 := by
    dsimp [n, η, ξ]
    field_simp [hg0]
    rw [← hf, hbg] at hRP
    ring_nf at hRP ⊢
    exact hRP
  have hRidentity :
      4 * n ^ 2 * (ξ ^ 3 + (s ^ 2 - 2) * ξ ^ 2 + ξ) =
        (ξ ^ 2 - 1) ^ 2 :=
    second_scaled_identity hRscaled hRPscaled
  exact no_scaled_duplication_chain hn hξ hnOne hPidentity hRidentity

/-- A coordinate-level normalized duplication chain cannot exist.

The three displayed square identities are the `X`-coordinate duplication
formula

`X(2S) (2Y(S))² = (X(S)² - b)²`

for `S = R, 2R, 4R`; in the last identity `X(8R)=0`.  Keeping this theorem
purely algebraic makes the substantial descent independent of the details of
mathlib's affine-point addition API. -/
theorem no_normalized_coordinate_duplication_chain
    {a b xR yR xP yP xQ yQ : ℚ}
    (hRcurve : yR ^ 2 = xR ^ 3 + a * xR ^ 2 + b * xR)
    (hPcurve : yP ^ 2 = xP ^ 3 + a * xP ^ 2 + b * xP)
    (hQcurve : yQ ^ 2 = xQ ^ 3 + a * xQ ^ 2 + b * xQ)
    (hRP : xP * (2 * yR) ^ 2 = (xR ^ 2 - b) ^ 2)
    (hPQ : xQ * (2 * yP) ^ 2 = (xP ^ 2 - b) ^ 2)
    (hQT : (xQ ^ 2 - b) ^ 2 = 0)
    (hxR : xR ≠ 0) (hxP : xP ≠ 0) (hxQ : xQ ≠ 0)
    (hyR : yR ≠ 0) (hyP : yP ≠ 0)
    (hxPQ : xP ≠ xQ) :
    False := by
  have hb : b = xQ ^ 2 := by
    nlinarith [sq_nonneg (xQ ^ 2 - b)]
  have hf :
      ((xR ^ 2 - b) / (2 * yR)) ^ 2 = xP :=
    quotient_square_of_duplication hyR hRP
  have hg :
      ((xP ^ 2 - b) / (2 * yP)) ^ 2 = xQ :=
    quotient_square_of_duplication hyP hPQ
  exact no_normalized_coordinate_duplication_chain_aux
    hRcurve hPcurve hQcurve hRP hPQ hb hf hg
    hxR hxP hxQ hxPQ

private lemma normalized_point_eq_origin_of_x_eq_zero
    {a b x y : ℚ}
    (h : (normalizedCurve a b).toAffine.Nonsingular x y)
    (h00 : (normalizedCurve a b).toAffine.Nonsingular 0 0)
    (hx : x = 0) :
    WeierstrassCurve.Affine.Point.some x y h =
      WeierstrassCurve.Affine.Point.some 0 0 h00 := by
  have hcurve := normalized_curve_equation h
  have hy : y = 0 := by
    rw [hx] at hcurve
    norm_num at hcurve
    nlinarith [sq_nonneg y]
  exact WeierstrassCurve.Affine.Point.some_eq_some
    (normalizedCurve a b) hx hy

private lemma normalized_origin_double_eq_zero
    {a b : ℚ} [_hEll : (normalizedCurve a b).IsElliptic]
    (h00 : (normalizedCurve a b).toAffine.Nonsingular 0 0) :
    (2 : ℕ) •
        WeierstrassCurve.Affine.Point.some 0 0 h00 = 0 := by
  rw [two_nsmul,
    WeierstrassCurve.Affine.Point.add_self_of_Y_eq]
  simp [normalizedCurve, WeierstrassCurve.Affine.negY]

/-- There is no point of order sixteen on a normalized curve whose eighth
multiple is the distinguished two-torsion point `(0,0)`. -/
theorem normalizedCurve_no_order_sixteen
    (a b : ℚ) [hEll : (normalizedCurve a b).IsElliptic]
    (h00 : (normalizedCurve a b).toAffine.Nonsingular 0 0)
    (R : (normalizedCurve a b).toAffine.Point)
    (hRorder : addOrderOf R = 16)
    (hlast :
      (8 : ℕ) • R =
        WeierstrassCurve.Affine.Point.some 0 0 h00) :
    False := by
  let W := normalizedCurve a b
  let T : W.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some 0 0 h00
  let P : W.toAffine.Point := (2 : ℕ) • R
  let Q : W.toAffine.Point := (2 : ℕ) • P
  have hPorder : addOrderOf P = 8 := by
    dsimp [P]
    rw [addOrderOf_nsmul' R (by norm_num), hRorder]
    norm_num
  have hQorder : addOrderOf Q = 4 := by
    dsimp [Q]
    rw [addOrderOf_nsmul' P (by norm_num), hPorder]
    norm_num
  have hR0 : R ≠ 0 := by
    intro hR0
    rw [hR0, addOrderOf_zero] at hRorder
    norm_num at hRorder
  have hP0 : P ≠ 0 := by
    intro hP0
    rw [hP0, addOrderOf_zero] at hPorder
    norm_num at hPorder
  have hQ0 : Q ≠ 0 := by
    intro hQ0
    rw [hQ0, addOrderOf_zero] at hQorder
    norm_num at hQorder
  have hPQne : P ≠ Q := by
    intro hPQ
    rw [hPQ, hQorder] at hPorder
    norm_num at hPorder
  have hQTpoint : (2 : ℕ) • Q = T := by
    dsimp [Q, P, T]
    calc
      (2 : ℕ) • ((2 : ℕ) • ((2 : ℕ) • R)) =
          (8 : ℕ) • R := by abel
      _ = WeierstrassCurve.Affine.Point.some 0 0 h00 := hlast
  have hTdouble : (2 : ℕ) • T = 0 := by
    dsimp [T, W]
    exact normalized_origin_double_eq_zero h00
  obtain ⟨xR, yR, hRns, hRxy⟩ :
      ∃ (x y : ℚ) (h : W.toAffine.Nonsingular x y),
        R = WeierstrassCurve.Affine.Point.some x y h := by
    cases hcase : R with
    | zero => exact (hR0 hcase).elim
    | some x y h => exact ⟨x, y, h, rfl⟩
  obtain ⟨xP, yP, hPns, hPxy⟩ :
      ∃ (x y : ℚ) (h : W.toAffine.Nonsingular x y),
        P = WeierstrassCurve.Affine.Point.some x y h := by
    cases hcase : P with
    | zero => exact (hP0 hcase).elim
    | some x y h => exact ⟨x, y, h, rfl⟩
  obtain ⟨xQ, yQ, hQns, hQxy⟩ :
      ∃ (x y : ℚ) (h : W.toAffine.Nonsingular x y),
        Q = WeierstrassCurve.Affine.Point.some x y h := by
    cases hcase : Q with
    | zero => exact (hQ0 hcase).elim
    | some x y h => exact ⟨x, y, h, rfl⟩
  have hRPpoint :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some xR yR hRns =
        WeierstrassCurve.Affine.Point.some xP yP hPns := by
    have hdef : (2 : ℕ) • R = P := rfl
    simpa only [hRxy, hPxy] using hdef
  have hPQpoint :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some xP yP hPns =
        WeierstrassCurve.Affine.Point.some xQ yQ hQns := by
    have hdef : (2 : ℕ) • P = Q := rfl
    simpa only [hPxy, hQxy] using hdef
  have hQTcoord :
      (2 : ℕ) • WeierstrassCurve.Affine.Point.some xQ yQ hQns =
        WeierstrassCurve.Affine.Point.some 0 0 h00 := by
    simpa only [hQxy, T] using hQTpoint
  have hxR : xR ≠ 0 := by
    intro hxR
    have hsome :=
      normalized_point_eq_origin_of_x_eq_zero hRns h00 hxR
    have hRT : R = T := by
      dsimp [T]
      rw [hRxy]
      exact hsome
    apply hP0
    dsimp [P]
    rw [hRT, hTdouble]
  have hxP : xP ≠ 0 := by
    intro hxP
    have hsome :=
      normalized_point_eq_origin_of_x_eq_zero hPns h00 hxP
    have hPT : P = T := by
      dsimp [T]
      rw [hPxy]
      exact hsome
    apply hQ0
    dsimp [Q]
    rw [hPT, hTdouble]
  have hxQ : xQ ≠ 0 := by
    intro hxQ
    have hsome :=
      normalized_point_eq_origin_of_x_eq_zero hQns h00 hxQ
    have hQT : Q = T := by
      dsimp [T]
      rw [hQxy]
      exact hsome
    have hbad := hQTpoint
    rw [hQT, hTdouble] at hbad
    exact WeierstrassCurve.Affine.Point.some_ne_zero h00 hbad.symm
  have hyR : yR ≠ 0 := by
    intro hyR
    have hvertical : yR = W.toAffine.negY xR yR := by
      simp [W, normalizedCurve, WeierstrassCurve.Affine.negY, hyR]
    have hzero :
        (2 : ℕ) •
            WeierstrassCurve.Affine.Point.some xR yR hRns = 0 := by
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_eq hvertical]
    rw [hRPpoint] at hzero
    exact WeierstrassCurve.Affine.Point.some_ne_zero hPns hzero
  have hyP : yP ≠ 0 := by
    intro hyP
    have hvertical : yP = W.toAffine.negY xP yP := by
      simp [W, normalizedCurve, WeierstrassCurve.Affine.negY, hyP]
    have hzero :
        (2 : ℕ) •
            WeierstrassCurve.Affine.Point.some xP yP hPns = 0 := by
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_eq hvertical]
    rw [hPQpoint] at hzero
    exact WeierstrassCurve.Affine.Point.some_ne_zero hQns hzero
  have hxPQ : xP ≠ xQ := by
    intro hxPQ
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq
        hPns.1 hQns.1 hxPQ with hy | hy
    · apply hPQne
      rw [hPxy, hQxy]
      exact WeierstrassCurve.Affine.Point.some_eq_some W hxPQ hy
    · have hPnegQ : P = -Q := by
        rw [hPxy, hQxy,
          WeierstrassCurve.Affine.Point.neg_some]
        exact WeierstrassCurve.Affine.Point.some_eq_some W hxPQ hy
      rw [hPnegQ, addOrderOf_neg, hQorder] at hPorder
      norm_num at hPorder
  have hRcurve := normalized_curve_equation hRns
  have hPcurve := normalized_curve_equation hPns
  have hQcurve := normalized_curve_equation hQns
  have hRP :=
    normalized_duplication_identity_of_double hRns hPns hRPpoint
  have hPQ :=
    normalized_duplication_identity_of_double hPns hQns hPQpoint
  have hQT :
      (xQ ^ 2 - b) ^ 2 = 0 := by
    have h :=
      normalized_duplication_identity_of_double hQns h00 hQTcoord
    simpa only [zero_mul] using h.symm
  exact no_normalized_coordinate_duplication_chain
    hRcurve hPcurve hQcurve hRP hPQ hQT
    hxR hxP hxQ hyR hyP hxPQ

/-- A rational elliptic curve has no rational point of exact order sixteen.

Starting with `T = 8R`, the admissible change

`x_old = x_new + x(T)`,
`y_old = y_new - a₁ x_new / 2 + y(T)`

sends `T` to `(0,0)` and turns the equation into
`Y² = X³ + aX² + bX`.  The induced point-group equivalence then reduces
the assertion to `normalizedCurve_no_order_sixteen`. -/
theorem no_rational_point_of_order_sixteen
    (E : WeierstrassCurve ℚ) [hEll : E.IsElliptic]
    (R : E.toAffine.Point) (hRorder : addOrderOf R = 16) :
    False := by
  let T : E.toAffine.Point := (8 : ℕ) • R
  have hTorder : addOrderOf T = 2 := by
    dsimp [T]
    rw [addOrderOf_nsmul' R (by norm_num), hRorder]
    norm_num
  have hT0 : T ≠ 0 := by
    intro hT0
    rw [hT0, addOrderOf_zero] at hTorder
    norm_num at hTorder
  have hTdouble : (2 : ℕ) • T = 0 := by
    rw [← hTorder]
    exact addOrderOf_nsmul_eq_zero T
  obtain ⟨θ, yT, hTns, hTxy⟩ :
      ∃ (x y : ℚ) (h : E.toAffine.Nonsingular x y),
        T = WeierstrassCurve.Affine.Point.some x y h := by
    cases hcase : T with
    | zero => exact (hT0 hcase).elim
    | some x y h => exact ⟨x, y, h, rfl⟩
  have hvertical : yT = E.toAffine.negY θ yT := by
    by_contra hne
    have hnonzero :
        WeierstrassCurve.Affine.Point.some θ yT hTns +
            WeierstrassCurve.Affine.Point.some θ yT hTns ≠ 0 := by
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne]
      exact WeierstrassCurve.Affine.Point.some_ne_zero _
    apply hnonzero
    rw [← two_nsmul, ← hTxy]
    exact hTdouble
  have hvertical' : E.a₃ + θ * E.a₁ + 2 * yT = 0 := by
    rw [WeierstrassCurve.Affine.negY] at hvertical
    linear_combination hvertical
  set C : WeierstrassCurve.VariableChange ℚ :=
    ⟨1, θ, -E.a₁ / 2, yT⟩ with hC
  let W : WeierstrassCurve ℚ := C • E
  have hWa₁ : W.a₁ = 0 := by
    dsimp [W]
    rw [WeierstrassCurve.variableChange_a₁, hC]
    simp
    ring
  have hWa₃ : W.a₃ = 0 := by
    dsimp [W]
    rw [WeierstrassCurve.variableChange_a₃, hC]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination hvertical'
  have hWa₆ : W.a₆ = 0 := by
    have heq := hTns.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    dsimp [W]
    rw [WeierstrassCurve.variableChange_a₆, hC]
    simp only [inv_one, Units.val_one, one_pow, one_mul]
    linear_combination -heq
  have h00 : W.toAffine.Nonsingular 0 0 := by
    apply W.toAffine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_zero]
    exact hWa₆
  let e : W.toAffine.Point ≃+ E.toAffine.Point :=
    WeierstrassCurve.Affine.Point.equivVariableChange E C
  have hmapOrigin :
      e (WeierstrassCurve.Affine.Point.some 0 0 h00) = T := by
    dsimp [e]
    rw [WeierstrassCurve.Affine.Point.equivVariableChange_some, hTxy]
    exact WeierstrassCurve.Affine.Point.some_eq_some E
      (by simp [hC]) (by simp [hC])
  let R₀ : W.toAffine.Point := e.symm R
  have hR₀order : addOrderOf R₀ = 16 := by
    dsimp [R₀]
    rw [AddEquiv.addOrderOf_eq]
    exact hRorder
  have hlast₀ :
      (8 : ℕ) • R₀ =
        WeierstrassCurve.Affine.Point.some 0 0 h00 := by
    apply e.injective
    calc
      e ((8 : ℕ) • R₀) = (8 : ℕ) • R := by simp [R₀]
      _ = T := rfl
      _ = e (WeierstrassCurve.Affine.Point.some 0 0 h00) :=
        hmapOrigin.symm
  let a : ℚ := W.a₂
  let b : ℚ := W.a₄
  have hWnorm : W = normalizedCurve a b := by
    ext <;> simp [normalizedCurve, a, b, hWa₁, hWa₃, hWa₆]
  let eNorm :
      W.toAffine.Point ≃+
        (normalizedCurve a b).toAffine.Point :=
    WeierstrassCurve.Affine.Point.equivOfEq hWnorm
  let S : (normalizedCurve a b).toAffine.Point := eNorm R₀
  let h00Norm :
      (normalizedCurve a b).toAffine.Nonsingular 0 0 :=
    hWnorm ▸ h00
  letI : (normalizedCurve a b).IsElliptic :=
    hWnorm ▸ (inferInstance : W.IsElliptic)
  have hSorder : addOrderOf S = 16 := by
    dsimp [S]
    rw [AddEquiv.addOrderOf_eq]
    exact hR₀order
  have hlastS :
      (8 : ℕ) • S =
        WeierstrassCurve.Affine.Point.some 0 0 h00Norm := by
    calc
      (8 : ℕ) • S = eNorm ((8 : ℕ) • R₀) := by
        rw [map_nsmul]
      _ = eNorm (WeierstrassCurve.Affine.Point.some 0 0 h00) := by
        rw [hlast₀]
      _ = WeierstrassCurve.Affine.Point.some 0 0 h00Norm := by
        dsimp [eNorm, h00Norm]
        rw [WeierstrassCurve.Affine.Point.equivOfEq_some]
  exact normalizedCurve_no_order_sixteen
    a b h00Norm S hSorder hlastS

/-- Obstruction-form restatement of `no_rational_point_of_order_sixteen`. -/
theorem point_addOrderOf_ne_sixteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (R : E.toAffine.Point) :
    addOrderOf R ≠ 16 :=
  no_rational_point_of_order_sixteen E R

/-- The order-sixteen obstruction on the canonical rational base change
used by `RationalTorsion`. -/
theorem rationalPoint_addOrderOf_ne_sixteen
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (R : (E⁄ℚ).Point) :
    addOrderOf R ≠ 16 := by
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ ℚ)).IsElliptic
  exact point_addOrderOf_ne_sixteen (E⁄ℚ) R

end MazurTorsion.Kubert

end

open scoped WeierstrassCurve.Affine

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 16 := by
  intro x hx
  have hcoe : addOrderOf (x : (E⁄ℚ).Point) = addOrderOf x :=
    addOrderOf_injective (AddCommGroup.torsion (E⁄ℚ).Point).subtype
      (AddCommGroup.torsion (E⁄ℚ).Point).subtype_injective x
  exact MazurTorsion.Kubert.rationalPoint_addOrderOf_ne_sixteen E
    (x : (E⁄ℚ).Point) (hcoe.trans hx)
#print axioms solution
