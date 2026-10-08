-- Prove2me | solution 1 for MazurTransfer.order18_no_noncuspidal_of_finite_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T14:18:27.173613+00:00
-- url     : https://prove2.me/submissions/4ddc6733-eb6b-4cf1-9387-ca448a82728a

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Definitions.Def_WeierstrassCurve_ReduceHom
import Definitions.Def_MazurReduction_PointTransport
import Theorems.Thm_WeierstrassCurve_Affine_Point_nsmul_some_eq_zero_iff_eval_prePsi
import Mathlib.RingTheory.RamificationInertia.Ramification


import Definitions.Def_MazurTransfer_Order18RealCubicPolynomialData
import Definitions.Def_MazurTransfer_Order18RealCubicQuotientData
import Theorems.Thm_MazurTransfer_order18_real_cubic_polynomial_irreducible
import Theorems.Thm_MazurTransfer_order18_real_cubic_quotient_isElliptic
/- Retain the namespace opened by the source after its unused declarations are pruned. -/
namespace MazurTorsion.XOneEighteenQuotientRankZero
end MazurTorsion.XOneEighteenQuotientRankZero

open scoped WeierstrassCurve WeierstrassCurve.Affine
namespace MazurTorsion.XOneEighteenRealCubicQuotient
theorem cubicPolynomial_irreducible : Irreducible cubicPolynomial :=
  MazurTransfer.order18_real_cubic_polynomial_irreducible
instance quotientCurve_isElliptic : quotientCurve.IsElliptic :=
  MazurTransfer.order18_real_cubic_quotient_isElliptic
end MazurTorsion.XOneEighteenRealCubicQuotient

namespace MazurTorsion.XOneEighteenTwoDivisionClassNumber
end MazurTorsion.XOneEighteenTwoDivisionClassNumber

namespace MazurTorsion.XOneEighteenQuotientReductionAtSeventeen
end MazurTorsion.XOneEighteenQuotientReductionAtSeventeen


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



end Point

end WeierstrassCurve.Affine

end

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



end Point

end WeierstrassCurve.Affine

end

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











/-- The sextic defining the standard genus-two model for `X₁(18)`. -/
def orderEighteenHyperellipticPolynomial (X : ℚ) : ℚ :=
  X ^ 6 - 4 * X ^ 5 + 10 * X ^ 4 - 10 * X ^ 3 +
    5 * X ^ 2 - 2 * X + 1

























end MazurTorsion.Kubert

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenRealCubicQuotient. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The real-cubic elliptic quotient of the `X₁(18)` sextic

This file records an explicit elliptic quotient of the standard genus-two
model for `X₁(18)`.  Its coefficient field is the totally real cubic field
generated by a root `tau` of

`T³ - 3T - 1`.

Only the algebraic point map is proved here.  In particular, this file makes
no assertion about the Mordell--Weil rank or the rational points of the
elliptic curve.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenRealCubicQuotient

noncomputable section

/-! ## The cubic coefficient field -/























/-- The defining cubic relation in `K`. -/
theorem tau_cubic : tau ^ 3 = 3 * tau + 1 := by
  have h : AdjoinRoot.mk cubicPolynomial cubicPolynomial = 0 :=
    AdjoinRoot.mk_self
  change
    AdjoinRoot.mk cubicPolynomial (X ^ 3 - 3 * X - 1 : Polynomial ℚ) = 0 at h
  rw [map_sub, map_sub, map_pow, map_mul,
    map_ofNat, map_one, AdjoinRoot.mk_X] at h
  have h' : tau ^ 3 - 3 * tau - 1 = 0 := by
    simpa only [tau] using h
  linear_combination h'

private theorem tau_pow_four : tau ^ 4 = 3 * tau ^ 2 + tau := by
  calc
    tau ^ 4 = tau * tau ^ 3 := by ring
    _ = 3 * tau ^ 2 + tau := by rw [tau_cubic]; ring

private theorem tau_pow_five : tau ^ 5 = tau ^ 2 + 9 * tau + 3 := by
  calc
    tau ^ 5 = tau * tau ^ 4 := by ring
    _ = tau * (3 * tau ^ 2 + tau) := by rw [tau_pow_four]
    _ = 3 * tau ^ 3 + tau ^ 2 := by ring
    _ = tau ^ 2 + 9 * tau + 3 := by rw [tau_cubic]; ring

private theorem tau_pow_six : tau ^ 6 = 9 * tau ^ 2 + 6 * tau + 1 := by
  calc
    tau ^ 6 = tau * tau ^ 5 := by ring
    _ = tau * (tau ^ 2 + 9 * tau + 3) := by rw [tau_pow_five]
    _ = tau ^ 3 + 9 * tau ^ 2 + 3 * tau := by ring
    _ = 9 * tau ^ 2 + 6 * tau + 1 := by rw [tau_cubic]; ring

private theorem tau_pow_seven : tau ^ 7 = 6 * tau ^ 2 + 28 * tau + 9 := by
  calc
    tau ^ 7 = tau * tau ^ 6 := by ring
    _ = tau * (9 * tau ^ 2 + 6 * tau + 1) := by rw [tau_pow_six]
    _ = 9 * tau ^ 3 + 6 * tau ^ 2 + tau := by ring
    _ = 6 * tau ^ 2 + 28 * tau + 9 := by rw [tau_cubic]; ring

private theorem tau_pow_eight : tau ^ 8 = 28 * tau ^ 2 + 27 * tau + 6 := by
  calc
    tau ^ 8 = tau * tau ^ 7 := by ring
    _ = tau * (6 * tau ^ 2 + 28 * tau + 9) := by rw [tau_pow_seven]
    _ = 6 * tau ^ 3 + 28 * tau ^ 2 + 9 * tau := by ring
    _ = 28 * tau ^ 2 + 27 * tau + 6 := by rw [tau_cubic]; ring

private theorem tau_pow_nine : tau ^ 9 = 27 * tau ^ 2 + 90 * tau + 28 := by
  calc
    tau ^ 9 = tau * tau ^ 8 := by ring
    _ = tau * (28 * tau ^ 2 + 27 * tau + 6) := by rw [tau_pow_eight]
    _ = 28 * tau ^ 3 + 27 * tau ^ 2 + 6 * tau := by ring
    _ = 27 * tau ^ 2 + 90 * tau + 28 := by rw [tau_cubic]; ring

private theorem tau_pow_ten : tau ^ 10 = 90 * tau ^ 2 + 109 * tau + 27 := by
  calc
    tau ^ 10 = tau * tau ^ 9 := by ring
    _ = tau * (27 * tau ^ 2 + 90 * tau + 28) := by rw [tau_pow_nine]
    _ = 27 * tau ^ 3 + 90 * tau ^ 2 + 28 * tau := by ring
    _ = 90 * tau ^ 2 + 109 * tau + 27 := by rw [tau_cubic]; ring

private theorem tau_pow_eleven : tau ^ 11 = 109 * tau ^ 2 + 297 * tau + 90 := by
  calc
    tau ^ 11 = tau * tau ^ 10 := by ring
    _ = tau * (90 * tau ^ 2 + 109 * tau + 27) := by rw [tau_pow_ten]
    _ = 90 * tau ^ 3 + 109 * tau ^ 2 + 27 * tau := by ring
    _ = 109 * tau ^ 2 + 297 * tau + 90 := by rw [tau_cubic]; ring

private theorem tau_pow_twelve : tau ^ 12 = 297 * tau ^ 2 + 417 * tau + 109 := by
  calc
    tau ^ 12 = tau * tau ^ 11 := by ring
    _ = tau * (109 * tau ^ 2 + 297 * tau + 90) := by rw [tau_pow_eleven]
    _ = 109 * tau ^ 3 + 297 * tau ^ 2 + 90 * tau := by ring
    _ = 297 * tau ^ 2 + 417 * tau + 109 := by rw [tau_cubic]; ring

private theorem tau_pow_thirteen : tau ^ 13 = 417 * tau ^ 2 + 1000 * tau + 297 := by
  calc
    tau ^ 13 = tau * tau ^ 12 := by ring
    _ = tau * (297 * tau ^ 2 + 417 * tau + 109) := by rw [tau_pow_twelve]
    _ = 297 * tau ^ 3 + 417 * tau ^ 2 + 109 * tau := by ring
    _ = 417 * tau ^ 2 + 1000 * tau + 297 := by rw [tau_cubic]; ring

private theorem tau_pow_fourteen : tau ^ 14 = 1000 * tau ^ 2 + 1548 * tau + 417 := by
  calc
    tau ^ 14 = tau * tau ^ 13 := by ring
    _ = tau * (417 * tau ^ 2 + 1000 * tau + 297) := by rw [tau_pow_thirteen]
    _ = 417 * tau ^ 3 + 1000 * tau ^ 2 + 297 * tau := by ring
    _ = 1000 * tau ^ 2 + 1548 * tau + 417 := by rw [tau_cubic]; ring

private theorem tau_pow_fifteen : tau ^ 15 = 1548 * tau ^ 2 + 3417 * tau + 1000 := by
  calc
    tau ^ 15 = tau * tau ^ 14 := by ring
    _ = tau * (1000 * tau ^ 2 + 1548 * tau + 417) := by rw [tau_pow_fourteen]
    _ = 1000 * tau ^ 3 + 1548 * tau ^ 2 + 417 * tau := by ring
    _ = 1548 * tau ^ 2 + 3417 * tau + 1000 := by rw [tau_cubic]; ring

private theorem tau_pow_sixteen : tau ^ 16 = 3417 * tau ^ 2 + 5644 * tau + 1548 := by
  calc
    tau ^ 16 = tau * tau ^ 15 := by ring
    _ = tau * (1548 * tau ^ 2 + 3417 * tau + 1000) := by rw [tau_pow_fifteen]
    _ = 1548 * tau ^ 3 + 3417 * tau ^ 2 + 1000 * tau := by ring
    _ = 3417 * tau ^ 2 + 5644 * tau + 1548 := by rw [tau_cubic]; ring

private theorem tau_pow_seventeen : tau ^ 17 = 5644 * tau ^ 2 + 11799 * tau + 3417 := by
  calc
    tau ^ 17 = tau * tau ^ 16 := by ring
    _ = tau * (3417 * tau ^ 2 + 5644 * tau + 1548) := by rw [tau_pow_sixteen]
    _ = 3417 * tau ^ 3 + 5644 * tau ^ 2 + 1548 * tau := by ring
    _ = 5644 * tau ^ 2 + 11799 * tau + 3417 := by rw [tau_cubic]; ring

private theorem tau_pow_eighteen : tau ^ 18 = 11799 * tau ^ 2 + 20349 * tau + 5644 := by
  calc
    tau ^ 18 = tau * tau ^ 17 := by ring
    _ = tau * (5644 * tau ^ 2 + 11799 * tau + 3417) := by rw [tau_pow_seventeen]
    _ = 5644 * tau ^ 3 + 11799 * tau ^ 2 + 3417 * tau := by ring
    _ = 11799 * tau ^ 2 + 20349 * tau + 5644 := by rw [tau_cubic]; ring

/-! ## The elliptic quotient and its point map -/







/-- The repeated affine numerator in the quotient formula. -/
def quotientD (x : ℚ) : K :=
  (x : K) + 2 * tau ^ 2 - tau - 6

/-- The abscissa of the elliptic quotient. -/
def quotientX (x : ℚ) : K :=
  ((2 * tau + 1) ^ 2 / 12) *
      (quotientD x / ((x : K) + tau)) ^ 2 -
    (4 * tau ^ 2 + 4 * tau - 11) / 12

/-- The ordinate of the elliptic quotient. -/
def quotientY (x y : ℚ) : K :=
  -(tau * (tau + 1) / 2) * (y : K) / ((x : K) + tau) ^ 3 -
    (quotientX x + tau ^ 2 + tau - 1) / 2

/-- A rational scalar cannot cancel the cubic generator. -/
theorem rational_add_tau_ne_zero (x : ℚ) : (x : K) + tau ≠ 0 := by
  intro h
  have htau : tau = -(x : K) := eq_neg_of_add_eq_zero_right h
  have htauc : tau ^ 3 - 3 * tau - 1 = 0 := by
    linear_combination tau_cubic
  rw [htau] at htauc
  have hxrel : (-x) ^ 3 - 3 * (-x) - 1 = 0 := by
    exact_mod_cast htauc
  have hroot : cubicPolynomial.IsRoot (-x) := by
    simpa [cubicPolynomial, Polynomial.IsRoot] using hxrel
  have hdegree : cubicPolynomial.natDegree = 3 := by
    simp only [cubicPolynomial]
    compute_degree!
  exact cubicPolynomial_irreducible.not_isRoot_of_natDegree_ne_one
    (by omega) hroot

/-- Direct substitution into the elliptic quotient equation, with the
nonvanishing denominator exposed as an explicit hypothesis. -/
theorem quotient_equation_of_den_ne
    {x y : ℚ} (hden : (x : K) + tau ≠ 0)
    (hcurve : y ^ 2 =
      MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    quotientY x y ^ 2 + quotientX x * quotientY x y +
        (tau ^ 2 + tau - 1) * quotientY x y =
      quotientX x ^ 3 + (tau ^ 2 + tau - 3) * quotientX x ^ 2 +
        (-tau ^ 2 + 4) * quotientX x - tau - 2 := by
  simp only [MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial] at hcurve
  have hcurveK : (y : K) ^ 2 =
      1 - (x : K) * 2 + (x : K) ^ 2 * 5 - (x : K) ^ 3 * 10 +
        (x : K) ^ 4 * 10 - (x : K) ^ 5 * 4 + (x : K) ^ 6 := by
    have hcurveK' := congrArg (algebraMap ℚ K) hcurve
    push_cast at hcurveK'
    ring_nf at hcurveK' ⊢
    exact hcurveK'
  unfold quotientY quotientX quotientD
  field_simp [hden]
  ring_nf
  rw [hcurveK]
  simp only [tau_pow_eighteen, tau_pow_sixteen,
    tau_pow_fifteen, tau_pow_fourteen, tau_pow_thirteen, tau_pow_twelve,
    tau_pow_eleven, tau_pow_ten, tau_pow_nine, tau_pow_eight,
    tau_pow_seven, tau_pow_six, tau_pow_five, tau_pow_four, tau_cubic]
  ring

/-- Every rational point on the standard `X₁(18)` sextic satisfies the
elliptic quotient equation. -/
theorem quotient_equation
    {x y : ℚ}
    (hcurve : y ^ 2 =
      MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    quotientY x y ^ 2 + quotientX x * quotientY x y +
        (tau ^ 2 + tau - 1) * quotientY x y =
      quotientX x ^ 3 + (tau ^ 2 + tau - 3) * quotientX x ^ 2 +
        (-tau ^ 2 + 4) * quotientX x - tau - 2 :=
  quotient_equation_of_den_ne (rational_add_tau_ne_zero x) hcurve

/-- The genuine affine point on the quotient attached to a rational sextic
point. -/
def quotientPoint (x y : ℚ)
    (hcurve : y ^ 2 =
      MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    quotientCurve.toAffine.Point :=
  WeierstrassCurve.Affine.Point.some (quotientX x) (quotientY x y) <|
    quotientCurve.toAffine.equation_iff_nonsingular.mp <| by
      rw [WeierstrassCurve.Affine.equation_iff]
      simpa [quotientCurve, sub_eq_add_neg, add_assoc] using quotient_equation hcurve

/-! ## Change to the rational-coefficient model -/

/-- The rational-coefficient model `[1,-1,1,25,1]`, base-changed to `K`. -/
def rationalModel : WeierstrassCurve K :=
  ⟨1, -1, 1, 25, 1⟩









end

end MazurTorsion.XOneEighteenRealCubicQuotient

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenQuotientSevenTorsion. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The visible seven-torsion on the `X₁(18)` elliptic quotient

The point `(1,0)` on the real-cubic quotient has exact order seven.  This
file checks its first four multiples directly in the affine group law.  In
particular, every affine point in the generated subgroup has abscissa among
`1`, `3-τ²`, and `1-τ`.

No assertion that this subgroup exhausts the Mordell--Weil group is made
here.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenQuotientSevenTorsion

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient

private theorem tau_ne_zero : tau ≠ 0 := by
  intro h
  have := tau_cubic
  rw [h] at this
  norm_num at this

private theorem tau_add_one_ne_zero : tau + 1 ≠ 0 := by
  intro h
  have ht : tau = -1 := by
    calc
      tau = tau + 1 - 1 := by ring
      _ = -1 := by rw [h]; ring
  have := tau_cubic
  rw [ht] at this
  norm_num at this

private theorem tau_sq_add_tau_ne_zero : tau ^ 2 + tau ≠ 0 := by
  rw [show tau ^ 2 + tau = tau * (tau + 1) by ring]
  exact mul_ne_zero tau_ne_zero tau_add_one_ne_zero

private theorem tau_sq_ne_two : tau ^ 2 ≠ 2 := by
  intro h
  have ht3 : tau ^ 3 = 2 * tau := by
    calc
      tau ^ 3 = tau * tau ^ 2 := by ring
      _ = 2 * tau := by rw [h]; ring
  have hadd : tau + 1 = 0 := by
    calc
      tau + 1 = (3 * tau + 1) - 2 * tau := by ring
      _ = tau ^ 3 - tau ^ 3 := by rw [← tau_cubic, ← ht3]
      _ = 0 := sub_self _
  exact tau_add_one_ne_zero hadd

private theorem tau_pow_four : tau ^ 4 = 3 * tau ^ 2 + tau := by
  calc
    tau ^ 4 = tau * tau ^ 3 := by ring
    _ = 3 * tau ^ 2 + tau := by rw [tau_cubic]; ring

private theorem tau_pow_five : tau ^ 5 = tau ^ 2 + 9 * tau + 3 := by
  calc
    tau ^ 5 = tau * tau ^ 4 := by ring
    _ = tau * (3 * tau ^ 2 + tau) := by rw [tau_pow_four]
    _ = 3 * tau ^ 3 + tau ^ 2 := by ring
    _ = tau ^ 2 + 9 * tau + 3 := by rw [tau_cubic]; ring

private theorem tau_pow_six : tau ^ 6 = 9 * tau ^ 2 + 6 * tau + 1 := by
  calc
    tau ^ 6 = tau * tau ^ 5 := by ring
    _ = tau * (tau ^ 2 + 9 * tau + 3) := by rw [tau_pow_five]
    _ = tau ^ 3 + 9 * tau ^ 2 + 3 * tau := by ring
    _ = 9 * tau ^ 2 + 6 * tau + 1 := by rw [tau_cubic]; ring

private theorem nonsingular_of_equation {x y : K}
    (h : y ^ 2 + x * y + (tau ^ 2 + tau - 1) * y =
      x ^ 3 + (tau ^ 2 + tau - 3) * x ^ 2 +
        (-tau ^ 2 + 4) * x - tau - 2) :
    quotientCurve.toAffine.Nonsingular x y := by
  apply quotientCurve.toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simpa [quotientCurve, sub_eq_add_neg, add_assoc] using h

private theorem generator_nonsingular :
    quotientCurve.toAffine.Nonsingular 1 0 := by
  apply nonsingular_of_equation
  ring_nf

private theorem pointTwo_nonsingular :
    quotientCurve.toAffine.Nonsingular (3 - tau ^ 2) (2 - tau ^ 2) := by
  apply nonsingular_of_equation
  ring_nf
  simp only [tau_pow_five, tau_pow_four, tau_cubic]
  ring

private theorem pointThree_nonsingular :
    quotientCurve.toAffine.Nonsingular (1 - tau) (-tau ^ 2 + tau) := by
  apply nonsingular_of_equation
  ring_nf
  simp only [tau_pow_four, tau_cubic]
  ring

private theorem pointFour_nonsingular :
    quotientCurve.toAffine.Nonsingular (1 - tau) (-tau) := by
  apply nonsingular_of_equation
  ring_nf
  simp only [tau_pow_four, tau_cubic]
  ring

/-- The visible generator `(1,0)`. -/
def generator : quotientCurve.toAffine.Point :=
  .some 1 0 generator_nonsingular

/-- The displayed double of `generator`. -/
def pointTwo : quotientCurve.toAffine.Point :=
  .some (3 - tau ^ 2) (2 - tau ^ 2) pointTwo_nonsingular

/-- The displayed triple of `generator`. -/
def pointThree : quotientCurve.toAffine.Point :=
  .some (1 - tau) (-tau ^ 2 + tau) pointThree_nonsingular

/-- The displayed fourth multiple, equal to `-pointThree`. -/
def pointFour : quotientCurve.toAffine.Point :=
  .some (1 - tau) (-tau) pointFour_nonsingular

private theorem generator_not_vertical :
    ¬((1 : K) = 1 ∧
      (0 : K) = quotientCurve.toAffine.negY 1 0) := by
  rintro ⟨-, h⟩
  simp only [WeierstrassCurve.Affine.negY, quotientCurve] at h
  apply tau_sq_add_tau_ne_zero
  linear_combination h

private theorem two_add_generator_x_ne : (3 - tau ^ 2 : K) ≠ 1 := by
  intro h
  apply tau_sq_ne_two
  calc
    tau ^ 2 = 3 - (3 - tau ^ 2) := by ring
    _ = 3 - 1 := by rw [h]
    _ = 2 := by ring

private theorem three_add_generator_x_ne : (1 - tau : K) ≠ 1 := by
  intro h
  apply tau_ne_zero
  calc
    tau = 1 - (1 - tau) := by ring
    _ = 1 - 1 := by rw [h]
    _ = 0 := by ring

private theorem two_sub_tau_sq_ne_zero : (2 - tau ^ 2 : K) ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm tau_sq_ne_two)

private theorem generator_slope :
    quotientCurve.toAffine.slope 1 1 0 0 = tau ^ 2 - 2 := by
  rw [quotientCurve.toAffine.slope_of_Y_ne rfl (fun h ↦
    generator_not_vertical ⟨rfl, h⟩)]
  simp only [WeierstrassCurve.Affine.negY, quotientCurve,
    WeierstrassCurve.toAffine]
  rw [show 3 * (1 : K) ^ 2 + 2 * (tau ^ 2 + tau - 3) * 1 +
      (-tau ^ 2 + 4) - 1 * 0 = tau ^ 2 + 2 * tau + 1 by ring,
    show (0 : K) - (-0 - 1 * 1 - (tau ^ 2 + tau - 1)) =
      tau ^ 2 + tau by ring]
  rw [div_eq_iff tau_sq_add_tau_ne_zero]
  ring_nf
  simp only [tau_pow_four, tau_cubic]
  ring

private theorem pointTwo_generator_slope :
    quotientCurve.toAffine.slope (3 - tau ^ 2) 1 (2 - tau ^ 2) 0 = 1 := by
  rw [quotientCurve.toAffine.slope_of_X_ne two_add_generator_x_ne]
  rw [show (2 - tau ^ 2 : K) - 0 = 2 - tau ^ 2 by ring,
    show (3 - tau ^ 2 : K) - 1 = 2 - tau ^ 2 by ring]
  exact div_self two_sub_tau_sq_ne_zero

private theorem pointThree_generator_slope :
    quotientCurve.toAffine.slope (1 - tau) 1 (-tau ^ 2 + tau) 0 =
      tau - 1 := by
  rw [quotientCurve.toAffine.slope_of_X_ne three_add_generator_x_ne]
  rw [show (-tau ^ 2 + tau : K) - 0 = -tau ^ 2 + tau by ring,
    show (1 - tau : K) - 1 = -tau by ring]
  rw [div_eq_iff (neg_ne_zero.mpr tau_ne_zero)]
  ring

private theorem two_nsmul_generator : (2 : ℕ) • generator = pointTwo := by
  rw [two_nsmul]
  unfold generator pointTwo
  rw [WeierstrassCurve.Affine.Point.add_some generator_not_vertical]
  apply WeierstrassCurve.Affine.Point.some_eq_some quotientCurve
  · rw [generator_slope]
    simp only [WeierstrassCurve.Affine.addX, quotientCurve,
      WeierstrassCurve.toAffine]
    ring_nf
    simp only [tau_pow_four]
    ring
  · rw [generator_slope]
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY,
      quotientCurve, WeierstrassCurve.toAffine]
    ring_nf
    simp only [tau_pow_six, tau_pow_four, tau_cubic]
    ring

private theorem three_nsmul_generator : (3 : ℕ) • generator = pointThree := by
  rw [show (3 : ℕ) • generator = (2 : ℕ) • generator + generator by abel,
    two_nsmul_generator]
  unfold pointTwo generator pointThree
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne two_add_generator_x_ne]
  apply WeierstrassCurve.Affine.Point.some_eq_some quotientCurve
  · rw [pointTwo_generator_slope]
    simp only [WeierstrassCurve.Affine.addX, quotientCurve,
      WeierstrassCurve.toAffine]
    ring_nf
  · rw [pointTwo_generator_slope]
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY,
      quotientCurve, WeierstrassCurve.toAffine]
    ring_nf

private theorem four_nsmul_generator : (4 : ℕ) • generator = pointFour := by
  rw [show (4 : ℕ) • generator = (3 : ℕ) • generator + generator by abel,
    three_nsmul_generator]
  unfold pointThree generator pointFour
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne three_add_generator_x_ne]
  apply WeierstrassCurve.Affine.Point.some_eq_some quotientCurve
  · rw [pointThree_generator_slope]
    simp only [WeierstrassCurve.Affine.addX, quotientCurve,
      WeierstrassCurve.toAffine]
    ring_nf
  · rw [pointThree_generator_slope]
    simp only [WeierstrassCurve.Affine.addY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.Affine.negAddY,
      quotientCurve, WeierstrassCurve.toAffine]
    ring_nf

private theorem pointFour_eq_neg_pointThree : pointFour = -pointThree := by
  unfold pointFour pointThree
  rw [WeierstrassCurve.Affine.Point.neg_some]
  apply WeierstrassCurve.Affine.Point.some_eq_some quotientCurve rfl
  simp only [WeierstrassCurve.Affine.negY, quotientCurve,
    WeierstrassCurve.toAffine]
  ring

/-- The visible generator is killed by seven. -/
@[simp]
theorem seven_nsmul_generator : (7 : ℕ) • generator = 0 := by
  calc
    (7 : ℕ) • generator =
        (4 : ℕ) • generator + (3 : ℕ) • generator := by abel
    _ = pointFour + pointThree := by
      rw [four_nsmul_generator, three_nsmul_generator]
    _ = 0 := by rw [pointFour_eq_neg_pointThree]; exact neg_add_cancel pointThree

/-- The displayed point `pointTwo` is twice the visible generator. -/
theorem two_nsmul_generator_eq_pointTwo :
    (2 : ℕ) • generator = pointTwo :=
  two_nsmul_generator

/-- The displayed point `pointThree` is three times the visible generator. -/
theorem three_nsmul_generator_eq_pointThree :
    (3 : ℕ) • generator = pointThree :=
  three_nsmul_generator

/-- The displayed point `pointFour` is four times the visible generator. -/
theorem four_nsmul_generator_eq_pointFour :
    (4 : ℕ) • generator = pointFour :=
  four_nsmul_generator

/-- The fifth multiple is the negative of the displayed double. -/
theorem five_nsmul_generator_eq_neg_pointTwo :
    (5 : ℕ) • generator = -pointTwo := by
  calc
    (5 : ℕ) • generator = (7 : ℕ) • generator - (2 : ℕ) • generator := by abel
    _ = -pointTwo := by rw [seven_nsmul_generator, two_nsmul_generator]; simp

/-- The sixth multiple is the negative of the visible generator. -/
theorem six_nsmul_generator_eq_neg_generator :
    (6 : ℕ) • generator = -generator := by
  calc
    (6 : ℕ) • generator = (7 : ℕ) • generator - generator := by abel
    _ = -generator := by rw [seven_nsmul_generator]; simp

/-- The visible generator has exact additive order seven. -/
theorem addOrderOf_generator : addOrderOf generator = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  apply addOrderOf_eq_prime seven_nsmul_generator
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

end

end MazurTorsion.XOneEighteenQuotientSevenTorsion

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionArithmetic. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Exact arithmetic for the `X₁(18)` two-division algebra

This file records the exact algebraic-number certificates used by the
two-descent on the real-cubic elliptic quotient.  The rational cubic

`S³ - 3S - 10`

is proved irreducible by reduction modulo `11`.  We then form its relative
base change to the real cubic field `K = ℚ(τ)`.  All displayed relative
norm identities are checked in the kernel by the resultant formula for a
monogenic cubic algebra.

The relative object is deliberately called an algebra here: its field
structure is supplied only after a separate primitive-element certificate
proves that the two cubic fields are linearly disjoint.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic

noncomputable section

namespace Q

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K
abbrev tau := MazurTorsion.XOneEighteenRealCubicQuotient.tau
abbrev cubicPolynomial :=
  MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial
theorem cubicPolynomial_irreducible : Irreducible cubicPolynomial :=
  MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial_irreducible
theorem tau_cubic : tau ^ 3 = 3 * tau + 1 :=
  MazurTorsion.XOneEighteenRealCubicQuotient.tau_cubic

end Q



/-! ## The rational two-division cubic -/







































/-! ## The relative cubic algebra over the quotient field -/

























/-! ## Exact relative norm certificates -/

























end

end MazurTorsion.XOneEighteenTwoDivisionArithmetic

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenQuotientTwoDescentModel. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# A characteristic-not-two model of the `X₁(18)` elliptic quotient

This file puts the real-cubic elliptic quotient into the form used by the
`x-T` two-descent.  Both coordinate changes are genuine admissible changes
of Weierstrass variables, so the resulting point maps are additive
equivalences rather than equation-only substitutions.

The completed two-division cubic is also identified with the explicit
relative cubic algebra used by the arithmetic certificates.  No
Mordell--Weil or Selmer conclusion is asserted here.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenQuotientTwoDescentModel

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenTwoDivisionArithmetic

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K

private theorem tau_pow_four : tau ^ 4 = 3 * tau ^ 2 + tau := by
  calc
    tau ^ 4 = tau * tau ^ 3 := by ring
    _ = 3 * tau ^ 2 + tau := by rw [tau_cubic]; ring

private theorem tau_pow_five : tau ^ 5 = tau ^ 2 + 9 * tau + 3 := by
  calc
    tau ^ 5 = tau * tau ^ 4 := by ring
    _ = tau * (3 * tau ^ 2 + tau) := by rw [tau_pow_four]
    _ = 3 * tau ^ 3 + tau ^ 2 := by ring
    _ = tau ^ 2 + 9 * tau + 3 := by rw [tau_cubic]; ring

private theorem tau_pow_six : tau ^ 6 = 9 * tau ^ 2 + 6 * tau + 1 := by
  calc
    tau ^ 6 = tau * tau ^ 5 := by ring
    _ = tau * (tau ^ 2 + 9 * tau + 3) := by rw [tau_pow_five]
    _ = tau ^ 3 + 9 * tau ^ 2 + 3 * tau := by ring
    _ = 9 * tau ^ 2 + 6 * tau + 1 := by rw [tau_cubic]; ring

/-! ## Admissible point-group equivalences -/

/-- The change whose coordinate formula is
`(X,Y) ↦ (9X+3τ²+3τ-8, 27Y+9X+12τ²+12τ-10)`. -/
def quotientToRationalChange : VariableChange K :=
  VariableChange.mk (Units.mk0 (3 : K) (by norm_num))
    (3 * tau ^ 2 + 3 * tau - 8) 1
    (12 * tau ^ 2 + 12 * tau - 10)

/-- The displayed quotient-to-rational coordinate change is an identity of
Weierstrass curves. -/
theorem quotientToRationalChange_smul :
    quotientToRationalChange • rationalModel = quotientCurve := by
  ext <;>
    norm_num [quotientToRationalChange, rationalModel, quotientCurve,
      WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆] <;>
    ring_nf <;>
    simp only [tau_pow_six, tau_pow_five, tau_pow_four, tau_cubic] <;>
    ring



private instance rationalModel_isElliptic : rationalModel.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [rationalModel, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]







/-- Additive equivalence from the original quotient to its
rational-coefficient model. -/
def quotientToRationalEquiv :
    quotientCurve.toAffine.Point ≃+ rationalModel.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.equivOfEq
      quotientToRationalChange_smul.symm).trans
    (WeierstrassCurve.Affine.Point.equivVariableChange
      rationalModel quotientToRationalChange)





/-! ## The completed two-division cubic -/







end

end MazurTorsion.XOneEighteenQuotientTwoDescentModel

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionSmallPrimes. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Small rational primes in the `X₁(18)` two-division compositum

This file gives the tame part of a class-number certificate for the
degree-nine two-division compositum.  For each rational prime between `5`
and `31`, one of the two cubic subfields is inert.  Contraction to that
subfield and multiplicativity of inertia degrees therefore show that every
prime of the compositum above it has inertia degree at least three.

The use of Kummer--Dedekind is unconditional: the two exact rational
power-basis discriminants are first put in the relevant conductors, which
proves that the Kummer--Dedekind exponents are prime to every prime under
consideration.  No maximal-order or class-number computation is assumed.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-! ## The two rational cubic power bases -/

theorem coefficientPolynomial_monic : Q.cubicPolynomial.Monic := by
  simp only [Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
  monicity <;> norm_num

/-- The rational power basis of the real cubic coefficient field. -/
def _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis : PowerBasis ℚ Q.K :=
  AdjoinRoot.powerBasis' coefficientPolynomial_monic





theorem coefficientPowerBasis_minpolyGen :
    _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.minpolyGen = Q.cubicPolynomial := by
  rw [PowerBasis.minpolyGen_eq]
  have hroot : Polynomial.aeval Q.tau Q.cubicPolynomial = 0 := by
    simp only [Q.cubicPolynomial,
      MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
      map_sub, map_pow, aeval_X, map_mul, map_ofNat, map_one]
    linear_combination Q.tau_cubic
  exact (minpoly.eq_of_irreducible_of_monic Q.cubicPolynomial_irreducible
    hroot coefficientPolynomial_monic).symm



theorem _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim : _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.dim = 3 := by
  rw [_root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis, AdjoinRoot.powerBasis'_dim]
  simp only [MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
  compute_degree!



private theorem norm_cubic_derivative
    {L : Type*} [CommRing L] [Algebra ℚ L]
    (pb : PowerBasis ℚ L) (hdim : pb.dim = 3) (d : ℚ)
    (hmin : pb.minpolyGen = X ^ 3 - 3 * X - C d) :
    Algebra.norm ℚ (3 * pb.gen ^ 2 - 3) = 27 * (d ^ 2 - 4) := by
  rw [Algebra.norm_eq_matrix_det pb.basis]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  rw [pb.leftMulMatrix, hmin]
  let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
  let companion : Matrix (Fin pb.dim) (Fin pb.dim) ℚ :=
    fun i j ↦ if (j : ℕ) + 1 = pb.dim then
      -(X ^ 3 - 3 * X - C d).coeff i
    else if (i : ℕ) = j + 1 then 1 else 0
  change Matrix.det
    (algebraMap ℚ (Matrix (Fin pb.dim) (Fin pb.dim) ℚ) 3 *
        companion ^ 2 -
      algebraMap ℚ (Matrix (Fin pb.dim) (Fin pb.dim) ℚ) 3) = _
  have hcompanion :
      Matrix.reindexAlgEquiv ℚ ℚ e companion =
        !![0, 0, d; 1, 0, 3; 0, 1, 0] := by
    ext i j
    change companion (e.symm i) (e.symm j) = _
    fin_cases i <;> fin_cases j <;>
      simp [companion, e, hdim, coeff_sub, coeff_X_pow, coeff_X]
  conv_lhs => rw [← Matrix.det_reindexAlgEquiv ℚ (R := ℚ) e]
  rw [map_sub, map_mul, map_pow]
  rw [(Matrix.reindexAlgEquiv ℚ ℚ e).commutes 3, hcompanion]
  rw [Matrix.det_fin_three]
  simp [Matrix.algebraMap_matrix_apply, Matrix.mul_apply, pow_two]
  ring

/-- The exact rational power-basis discriminant of the coefficient cubic. -/
theorem coefficientPowerBasis_discriminant :
    Algebra.discr ℚ _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.basis = 81 := by
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [_root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.finrank, _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim,
    ← PowerBasis.minpolyGen_eq, coefficientPowerBasis_minpolyGen]
  simp only [Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
    derivative_sub, derivative_pow, derivative_X, derivative_mul,
    derivative_ofNat, derivative_one, mul_one, Nat.cast_ofNat,
    zero_mul, sub_zero]
  rw [show _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.gen = Q.tau by rfl]
  have hnorm := norm_cubic_derivative _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis
    _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim 1 (by
      simpa only [Q.cubicPolynomial,
        MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
        C_1] using coefficientPowerBasis_minpolyGen)
  rw [show _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.gen = Q.tau by rfl] at hnorm
  norm_num at hnorm ⊢
  rw [map_ofNat]
  rw [hnorm]
  norm_num



/-! ## Integral generators and their conductors -/

/-- The integral polynomial `X³ - 3X - 1`. -/
def coefficientPolynomialInt : Polynomial ℤ := X ^ 3 - 3 * X - 1

theorem coefficientPolynomialInt_monic : coefficientPolynomialInt.Monic := by
  simp only [coefficientPolynomialInt]
  monicity <;> norm_num



private theorem coefficientPolynomialInt_aeval_tau :
    Polynomial.aeval Q.tau coefficientPolynomialInt = 0 := by
  simp only [coefficientPolynomialInt, map_sub, map_pow, aeval_X,
    map_mul, map_ofNat, map_one]
  linear_combination Q.tau_cubic

/-- The coefficient-field generator as an algebraic integer. -/
def coefficientInteger : 𝓞 Q.K :=
  ⟨Q.tau, ⟨coefficientPolynomialInt, coefficientPolynomialInt_monic,
    coefficientPolynomialInt_aeval_tau⟩⟩

theorem coefficientInteger_minpoly :
    minpoly ℤ coefficientInteger = coefficientPolynomialInt := by
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  have hfield := minpoly.isIntegrallyClosed_eq_field_fractions ℚ Q.K
    coefficientInteger.isIntegral
  have hmin := coefficientPowerBasis_minpolyGen
  rw [PowerBasis.minpolyGen_eq] at hmin
  change minpoly ℚ Q.tau = Q.cubicPolynomial at hmin
  rw [← hfield]
  change minpoly ℚ Q.tau = _
  rw [hmin]
  norm_num [coefficientInteger, coefficientPolynomialInt, Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]













private theorem integer_discriminant_mem_conductor
    {L : Type*} [Field L] [NumberField L]
    (B : PowerBasis ℚ L) (theta : 𝓞 L)
    (hgen : B.gen = (theta : L)) (d : ℤ)
    (hdisc : Algebra.discr ℚ B.basis = (d : ℚ)) :
    (d : 𝓞 L) ∈ conductor ℤ theta := by
  have hfield :
      algebraMap (𝓞 L) L (d : 𝓞 L) ∈
        IsLocalization.coeSubmodule L (conductor ℤ theta) := by
    rw [mem_coeSubmodule_conductor]
    intro z
    have hz := Algebra.discr_mul_isIntegral_mem_adjoin ℚ
      (B := B) (by simpa only [hgen] using theta.isIntegral_coe)
      z.isIntegral_coe
    rw [hdisc] at hz
    simpa only [RingOfIntegers.coe_eq_algebraMap, map_intCast,
      hgen, Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ ℚ L] using hz
  obtain ⟨z, hz, hzmap⟩ :=
    (IsLocalization.mem_coeSubmodule L (conductor ℤ theta)).mp hfield
  have hz' : z = (d : 𝓞 L) := RingOfIntegers.coe_injective hzmap
  simpa only [hz'] using hz

/-- The integer `81` lies in the conductor of `ℤ[τ]` in the coefficient
field's full ring of integers. -/
theorem coefficient_discriminant_mem_conductor :
    (81 : 𝓞 Q.K) ∈ conductor ℤ coefficientInteger := by
  apply integer_discriminant_mem_conductor _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis
    coefficientInteger (by rfl) 81
  exact coefficientPowerBasis_discriminant





/-! ## Exact finite-field irreducibility certificates -/

def coefficientPolynomialMod (p : ℕ) : Polynomial (ZMod p) :=
  X ^ 3 - 3 * X - 1



theorem coefficientPolynomialInt_map_zmod (p : ℕ) :
    coefficientPolynomialInt.map (Int.castRingHom (ZMod p)) =
      coefficientPolynomialMod p := by
  norm_num [coefficientPolynomialInt, coefficientPolynomialMod]











































/-! ## Kummer--Dedekind and inertia in the compositum -/



















end

end MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

end


/- Source module: EllipticCurves.Mathlib.AdicValuation. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


/-!
# The residue map on `v`-integral elements of the fraction field

Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.

Let `R` be a Dedekind domain with fraction field `K` and let `v` be a height-one prime of `R`.
An element of `K` of `v`-adic valuation at most `1` is congruent to an element of `R` modulo
elements of valuation `< 1` (`exists_valuation_sub_lt_of_integer`), and the class in
`R ⧸ v.asIdeal` of such an approximant does not depend on its choice.  This file packages the
resulting *residue map* as a ring homomorphism
`residueHom : (v.valuation K).integer →+* R ⧸ v.asIdeal`
on the subring of `v`-integral elements of `K`, extending `Ideal.Quotient.mk v.asIdeal`
(`residueHom_algebraMap`); an unfolding requires only *some* approximant (`residueHom_eq`).

It also provides the `R`-algebra structure on `(v.valuation K).integer` and the `Field`
instance on `R ⧸ v.asIdeal` (the ideal is maximal).
-/

section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/- Implementation note (upstreaming): Mathlib deliberately keeps `Ideal.Quotient.field` a *local*
instance (cf. `RingTheory/DedekindDomain/Different.lean`, `RingTheory/Artinian/Module.lean`),
since maximality of a general ideal is not inferable.  Here the ideal is `v.asIdeal` for a
height-one prime `v` of a Dedekind domain, whose maximality is an instance
(`HeightOneSpectrum.isMaximal`), so the `Field` instance is keyed on `v` and safe to make global;
be prepared to demote it to a local instance if upstream review prefers that. -/
noncomputable instance instFieldQuotientHeightOneIdeal : Field (R ⧸ v.asIdeal) :=
  Ideal.Quotient.field _

noncomputable instance instAlgebraIntegerValuationSubring : Algebra R (v.valuation K).integer :=
  ((algebraMap R K).codRestrict (v.valuation K).integer fun r ↦ v.valuation_le_one r).toAlgebra



@[simp] lemma coe_algebraMap_integer (r : R) :
    ((algebraMap R (v.valuation K).integer r : (v.valuation K).integer) : K)
      = algebraMap R K r := rfl

/-- The distinguished `R`-approximant of a `v`-integral element of `K` (an element of `R`
congruent to it modulo valuation `< 1`).  Implementation detail of `residueHom`; use that (and
`residueHom_eq`) instead. -/
noncomputable def residueAux (x : (v.valuation K).integer) : R :=
  (v.exists_valuation_sub_lt_of_integer x.2 1).choose

private lemma valuation_sub_residueAux_lt (x : (v.valuation K).integer) :
    v.valuation K (algebraMap R K (residueAux v x) - x) < 1 :=
  lt_of_lt_of_eq (v.exists_valuation_sub_lt_of_integer x.2 1).choose_spec Units.val_one

/-- Two `R`-approximants of the same `v`-integral element agree modulo `v`. -/
private lemma mk_eq_mk_of_close {x : (v.valuation K).integer} {a b : R}
    (ha : v.valuation K (algebraMap R K a - x) < 1)
    (hb : v.valuation K (algebraMap R K b - x) < 1) :
    Ideal.Quotient.mk v.asIdeal a = Ideal.Quotient.mk v.asIdeal b := by
  rw [Ideal.Quotient.eq, ← intValuation_lt_one_iff_mem, ← valuation_of_algebraMap (K := K),
    Algebra.cast, map_sub (algebraMap R K)]
  calc v.valuation K (algebraMap R K a - algebraMap R K b)
      = v.valuation K ((algebraMap R K a - x) - (algebraMap R K b - x)) := by ring_nf
    _ ≤ max (v.valuation K (algebraMap R K a - x)) (v.valuation K (algebraMap R K b - x)) :=
        Valuation.map_sub _ _ _
    _ < 1 := max_lt ha hb

/-- An approximant of a `v`-integral element is itself `v`-integral in `K`. -/
private lemma valuation_le_one_of_close {x : (v.valuation K).integer} {a : R}
    (ha : v.valuation K (algebraMap R K a - x) < 1) :
    v.valuation K (algebraMap R K a) ≤ 1 := by
  calc v.valuation K (algebraMap R K a)
      = v.valuation K ((algebraMap R K a - x) + x) := by ring_nf
    _ ≤ max (v.valuation K (algebraMap R K a - x)) (v.valuation K x) := Valuation.map_add _ _ _
    _ ≤ 1 := max_le ha.le x.2

/-- The **residue map** on the `v`-integral elements of `K`, with values in the residue field
`R ⧸ v.asIdeal`: the class of any `R`-approximant within valuation `< 1`.  It extends
`Ideal.Quotient.mk v.asIdeal` (`residueHom_algebraMap`). -/
noncomputable def residueHom : (v.valuation K).integer →+* R ⧸ v.asIdeal where
  toFun x := Ideal.Quotient.mk v.asIdeal (residueAux v x)
  map_one' := by
    rw [mk_eq_mk_of_close v (valuation_sub_residueAux_lt v 1) (b := 1) (by simp), map_one]
  map_mul' x y := by
    rw [← map_mul]
    refine mk_eq_mk_of_close v (valuation_sub_residueAux_lt v (x * y)) ?_
    have hx := valuation_sub_residueAux_lt v x
    have hy := valuation_sub_residueAux_lt v y
    calc v.valuation K (algebraMap R K (residueAux v x * residueAux v y) - (x * y : _))
        = v.valuation K (algebraMap R K (residueAux v x) * (algebraMap R K (residueAux v y) - y)
            + (y : K) * (algebraMap R K (residueAux v x) - x)) := by push_cast; ring_nf
      _ ≤ max (v.valuation K (algebraMap R K (residueAux v x)
              * (algebraMap R K (residueAux v y) - y)))
            (v.valuation K ((y : K) * (algebraMap R K (residueAux v x) - x))) :=
          Valuation.map_add _ _ _
      _ < 1 := by
          rw [map_mul, map_mul]
          refine max_lt (lt_of_le_of_lt (mul_le_of_le_one_left' ?_) hy)
            (lt_of_le_of_lt (mul_le_of_le_one_left' y.2) hx)
          exact valuation_le_one_of_close v hx
  map_zero' := by
    rw [mk_eq_mk_of_close v (valuation_sub_residueAux_lt v 0) (b := 0) (by simp), map_zero]
  map_add' x y := by
    rw [← map_add]
    refine mk_eq_mk_of_close v (valuation_sub_residueAux_lt v (x + y)) ?_
    have hx := valuation_sub_residueAux_lt v x
    have hy := valuation_sub_residueAux_lt v y
    calc v.valuation K (algebraMap R K (residueAux v x + residueAux v y) - (x + y : _))
        = v.valuation K ((algebraMap R K (residueAux v x) - x)
            + (algebraMap R K (residueAux v y) - y)) := by push_cast; ring_nf
      _ ≤ _ := Valuation.map_add _ _ _
      _ < 1 := max_lt hx hy

/-- Unfolding lemma for `residueHom`: the residue of `x` is the class of *any* `R`-approximant
of `x` within valuation `< 1`. -/
lemma _root_.IsDedekindDomain.HeightOneSpectrum.residueHom_eq {x : (v.valuation K).integer} {a : R}
    (h : v.valuation K (algebraMap R K a - x) < 1) :
    residueHom v x = Ideal.Quotient.mk v.asIdeal a :=
  mk_eq_mk_of_close v (valuation_sub_residueAux_lt v x) h

@[simp] lemma residueHom_algebraMap (r : R) :
    residueHom v (algebraMap R (v.valuation K).integer r) = Ideal.Quotient.mk v.asIdeal r :=
  _root_.IsDedekindDomain.HeightOneSpectrum.residueHom_eq v (by simp)

end IsDedekindDomain.HeightOneSpectrum

end

end


/- Source module: MazurReduction.DedekindResidue. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Uses Michael Stoll's residueHom as integrated in MazurTheorem, with its
original Apache-2.0 attribution retained in the imported source module.
-/


open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
namespace MazurReduction

/-- Boundary: identify the canonical valuation-ring residue field with the
Dedekind residue field, compatibly with Stoll's explicit residue map.
Named downstream consumer: the order-18 cubic-field point-count bound. -/
theorem dedekind_residue_equiv
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    ∃ e : ResidueField (v.valuation K).valuationSubring ≃+* (R ⧸ v.asIdeal),
      e.toRingHom.comp (residue (v.valuation K).valuationSubring) = residueHom v := by
  let w := v.valuation K
  let A := w.valuationSubring
  let f : A →+* (R ⧸ v.asIdeal) := residueHom v
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨⟨algebraMap R K r, v.valuation_le_one r⟩, ?_⟩
    exact residueHom_algebraMap v r
  have hker : RingHom.ker f = maximalIdeal A := by
    ext a
    rw [RingHom.mem_ker, w.mem_maximalIdeal_iff]
    obtain ⟨r, hr⟩ := v.exists_valuation_sub_lt_of_integer a.property 1
    have hclose : w (algebraMap R K r - (a : K)) < 1 := hr
    change residueHom v a = 0 ↔ w (a : K) < 1
    rw [_root_.IsDedekindDomain.HeightOneSpectrum.residueHom_eq v hclose, Ideal.Quotient.eq_zero_iff_mem,
      ← v.valuation_lt_one_iff_mem (K := K)]
    constructor
    · intro h
      calc
        w (a : K) = w (algebraMap R K r - (algebraMap R K r - a)) := by congr 1; ring
        _ ≤ max (w (algebraMap R K r)) (w (algebraMap R K r - a)) := w.map_sub _ _
        _ < 1 := max_lt h hclose
    · intro h
      calc
        w (algebraMap R K r) = w ((algebraMap R K r - a) + a) := by congr 1; ring
        _ ≤ max (w (algebraMap R K r - a)) (w (a : K)) := w.map_add _ _
        _ < 1 := max_lt hclose h
  let e := (Ideal.quotEquivOfEq hker.symm).trans (f.quotientKerEquivOfSurjective hf)
  refine ⟨e, ?_⟩
  ext a
  change e (Ideal.Quotient.mk (maximalIdeal A) a) = f a
  simp [e]

end MazurReduction
#print axioms MazurReduction.dedekind_residue_equiv

end


/- Source module: MazurReduction.DiscreteValuationCoordinates. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin

Uses the generic integral-coordinate lemmas of Anthropic's FLT,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/


open WithZero
namespace MazurReduction

/-- Boundary: discrete valuation coordinates for integral Weierstrass models
over any field. Named downstream consumer: the unramified torsion-kernel
bound for the cubic-field quotient used in the order-18 exclusion. -/
theorem discrete_abscissa_valuation_ge_two
    {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    (W : WeierstrassCurve v.valuationSubring) {x y : K}
    (h : (W.map v.valuationSubring.subtype).toAffine.Equation x y)
    (hx : x ∉ v.valuationSubring) : exp (2 : ℤ) ≤ v x := by
  let A := v.valuationSubring
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ A.zero_mem)
  have hy0 : y ≠ 0 := WeierstrassCurve.Affine.Y_ne_zero_of_X_notMem W h hx
  obtain ⟨hr, hrnot⟩ := WeierstrassCurve.Affine.X_cubed_div_Y_sq_notMem_nonunits W h hx
  have hr0 : x ^ 3 / y ^ 2 ≠ 0 := div_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hy0)
  have hrv : v (x ^ 3 / y ^ 2) = 1 := by
    apply le_antisymm
    · exact hr
    · apply (inv_le_one₀ (show 0 < v (x ^ 3 / y ^ 2) from
        (zero_lt_iff).mpr ((map_ne_zero v).mpr hr0))).mp
      rw [← map_inv₀]
      exact A.inv_mem_of_notMem_nonunits hrnot
  have hex : exp (log (v x)) = v x := exp_log ((map_ne_zero v).mpr hx0)
  have hey : exp (log (v y)) = v y := exp_log ((map_ne_zero v).mpr hy0)
  have heq : 3 * log (v x) = 2 * log (v y) := by
    rw [map_div₀, map_pow, map_pow, ← hex, ← hey] at hrv
    simp only [← exp_nsmul, ← exp_sub, ← exp_zero, exp_inj, nsmul_eq_mul] at hrv
    omega
  have hxlt : 1 < v x := lt_of_not_ge hx
  rw [← hex, ← exp_zero, exp_lt_exp] at hxlt
  rw [← hex, exp_le_exp]
  omega

end MazurReduction
#print axioms MazurReduction.discrete_abscissa_valuation_ge_two

end


/- Source module: MazurReduction.PolynomialRootBound. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


namespace MazurReduction
open Polynomial

/-- Boundary: an integral-coefficient polynomial root outside a valuation ring
is bounded by its leading coefficient. Named downstream consumer:
the odd-prime division-polynomial kernel exclusion. -/
theorem leading_coefficient_root_bound
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (f : K[X]) {x : K}
    (hd : 0 < f.natDegree) (hc : ∀ i, v (f.coeff i) ≤ 1)
    (hr : f.eval x = 0) (hx : 1 < v x) :
    v f.leadingCoeff * v x ≤ 1 := by
  by_contra hn
  have hn' : 1 < v f.leadingCoeff * v x := lt_of_not_ge hn
  have hxpos : 0 < v x := zero_lt_one.trans hx
  have hlcpos : 0 < v f.leadingCoeff := by
    by_contra h
    have hz : v f.leadingCoeff = 0 := le_antisymm (le_of_not_gt h) zero_le
    simp [hz] at hn'
  have htoppos : 0 < v f.leadingCoeff * v x ^ f.natDegree :=
    mul_pos hlcpos (pow_pos hxpos _)
  have hstep : v x ^ (f.natDegree - 1) < v f.leadingCoeff * v x ^ f.natDegree := by
    have he : f.natDegree = (f.natDegree - 1) + 1 := by omega
    calc
      v x ^ (f.natDegree - 1) = 1 * v x ^ (f.natDegree - 1) := (one_mul _).symm
      _ < (v f.leadingCoeff * v x) * v x ^ (f.natDegree - 1) :=
        mul_lt_mul_of_pos_right hn' (pow_pos hxpos _)
      _ = v f.leadingCoeff * v x ^ f.natDegree := by
        conv_rhs => rw [he, pow_add, pow_one]
        ac_rfl
  rw [eval_eq_sum_range, Finset.sum_range_succ, coeff_natDegree,
    add_eq_zero_iff_eq_neg] at hr
  apply_fun v at hr
  have hlt := v.map_sum_lt (s := Finset.range f.natDegree) htoppos.ne' (fun i hi => show
      v (f.coeff i * x ^ i) < v f.leadingCoeff * v x ^ f.natDegree from by
    rw [map_mul, map_pow]
    exact (mul_le_of_le_one_left zero_le (hc i)).trans_lt
      ((pow_le_pow_right₀ hx.le (by have := Finset.mem_range.mp hi; omega)).trans_lt hstep))
  exact (ne_of_lt hlt) (by simpa only [v.map_neg, map_mul, map_pow] using hr)

end MazurReduction
#print axioms MazurReduction.leading_coefficient_root_bound

end


/- Source module: MazurReduction.UnramifiedOddDivision. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


open WithZero
namespace MazurReduction

/-- Boundary: division-polynomial nonvanishing at an unramified odd prime
of any discretely valued field. Named downstream consumer: the order-18
cubic-field good-reduction torsion-kernel exclusion. -/
theorem unramified_odd_prime_division_nonzero
    {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰)
    (p : ℕ) [Fact p.Prime] (hp : 2 < p) (hv : v (p : K) = exp (-1 : ℤ))
    (W : WeierstrassCurve v.valuationSubring) {x y : K}
    (h : (W.map v.valuationSubring.subtype).toAffine.Equation x y)
    (hx : x ∉ v.valuationSubring) :
    ((W.map v.valuationSubring.subtype).preΨ' p).eval x ≠ 0 := by
  let Wk := W.map v.valuationSubring.subtype
  have hp0 : (p : K) ≠ 0 := by
    intro hz
    have he : exp (-1 : ℤ) = 0 := hv.symm.trans (by rw [hz, map_zero])
    exact exp_ne_zero he
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hlc : (Wk.preΨ' p).leadingCoeff = p := by
    rw [Wk.leadingCoeff_preΨ' hp0, if_neg (Nat.not_even_iff_odd.mpr hpodd)]
  have hc : ∀ i, v ((Wk.preΨ' p).coeff i) ≤ 1 := by
    intro i
    dsimp only [Wk]
    rw [W.map_preΨ', Polynomial.coeff_map]
    exact ((W.preΨ' p).coeff i).property
  intro hr
  have hb := leading_coefficient_root_bound v (Wk.preΨ' p)
    (Wk.natDegree_preΨ'_pos hp hp0) hc hr (lt_of_not_ge hx)
  rw [hlc, hv] at hb
  have he : exp (1 : ℤ) ≤ exp (-1 : ℤ) * v x := by
    calc
      exp (1 : ℤ) = exp (-1 : ℤ) * exp (2 : ℤ) := by rw [← exp_add]; norm_num
      _ ≤ exp (-1 : ℤ) * v x :=
        mul_le_mul_of_nonneg_left (discrete_abscissa_valuation_ge_two v W h hx) zero_le
  have hpos : 1 < exp (1 : ℤ) := by rw [← exp_zero, exp_lt_exp]; norm_num
  exact (not_le_of_gt (hpos.trans_le he)) hb

end MazurReduction
#print axioms MazurReduction.unramified_odd_prime_division_nonzero

end


/- Source module: MazurReduction.UnramifiedTorsionKernel. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


open WithZero IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine
namespace MazurReduction

/-- Boundary: good reduction at an unramified odd prime of a discretely
valued field kills no nonzero torsion point. Named downstream consumer:
the cubic-field reduction in the order-18 exclusion. -/
theorem unramified_torsion_kernel_zero
    {K : Type*} [Field K] [DecidableEq K]
    (v : Valuation K ℤᵐ⁰) (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (hv : v (p : K) = WithZero.exp (-1 : ℤ))
    [DecidableEq (ResidueField v.valuationSubring)]
    (W : WeierstrassCurve v.valuationSubring)
    [(W.map v.valuationSubring.subtype).IsElliptic]
    (hΔ : (W.map (residue v.valuationSubring)).Δ ≠ 0)
    (P : (W.map v.valuationSubring.subtype).toAffine.Point)
    (hP : IsOfFinAddOrder P)
    (hred : WeierstrassCurve.reduceHom hΔ P = 0) : P = 0 := by
  classical
  let A := v.valuationSubring
  let F := ResidueField A
  have hpzero : (p : F) = 0 := by
    have hm : (p : A) ∈ maximalIdeal A := by
      apply v.mem_maximalIdeal_iff.mpr
      change v (p : K) < 1
      rw [hv, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    have hz := (residue_eq_zero_iff (p : A)).mpr hm
    simpa only [map_natCast] using hz
  letI : CharP F p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hpzero
  by_contra hP0
  have hn0 : addOrderOf P ≠ 0 := hP.addOrderOf_pos.ne'
  have hn1 : addOrderOf P ≠ 1 := fun h => hP0 (AddMonoid.addOrderOf_eq_one_iff.mp h)
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hn1
  let Q := (addOrderOf P / q) • P
  have hQorder : addOrderOf Q = q := by
    exact orderOf_pow_orderOf_div (x := Multiplicative.ofAdd P) hn0 hqdvd
  have hQred : WeierstrassCurve.reduceHom hΔ Q = 0 := by
    dsimp only [Q]
    rw [map_nsmul, hred, nsmul_zero]
  have hQq : q • Q = 0 := by rw [← hQorder]; exact addOrderOf_nsmul_eq_zero Q
  generalize hQdef : Q = R at hQorder hQred hQq
  cases R with
  | zero =>
    have hz : addOrderOf (0 : (W.map A.subtype).toAffine.Point) = q := hQorder
    exact hq.ne_one (by simpa only [addOrderOf_zero] using hz.symm)
  | some x y h =>
    have hx : x ∉ A := by
      intro hx
      have hs : WeierstrassCurve.reduceHom hΔ (.some x y h) ≠ 0 := by
        change WeierstrassCurve.reducePoint hΔ (.some x y h) ≠ 0
        rw [WeierstrassCurve.reducePoint_some_of_mem hΔ h hx]
        exact Point.some_ne_zero _
      exact hs hQred
    by_cases hqp : q = p
    · rw [hqp] at hQq
      have hz := (Point.nsmul_some_eq_zero_iff_eval_prePsi
        (W.map A.subtype) ((Fact.out : p.Prime).odd_of_ne_two (by omega)) h).mp hQq
      exact unramified_odd_prime_division_nonzero v p hp hv W h.1 hx hz
    · have hqres : (q : F) ≠ 0 := by
        intro hz
        have hdiv := (CharP.cast_eq_zero_iff F p q).mp hz
        exact hqp ((Nat.dvd_prime hq).mp hdiv |>.resolve_left (Fact.out : p.Prime).ne_one).symm
      exact hx (WeierstrassCurve.X_mem_of_nsmul_eq_zero' W hqres h hQq)

end MazurReduction
#print axioms MazurReduction.unramified_torsion_kernel_zero

end


/- Source module: MazurReduction.DedekindBound. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open WeierstrassCurve WeierstrassCurve.Affine WithZero
open scoped WeierstrassCurve.Affine
namespace MazurReduction

/-- Boundary: full torsion over a fraction field injects into the finite
special fibre at an unramified odd prime. Named downstream consumer:
the order-18 cubic-field 21-point bound. -/
theorem dedekind_torsion_card_bound
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]
    (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (hv : v.valuation K (p : K) = exp (-1 : ℤ))
    (W : WeierstrassCurve R) [(W.map (algebraMap R K)).IsElliptic]
    [(W.map (algebraMap R (R ⧸ v.asIdeal))).IsElliptic] :
    Finite (AddCommGroup.torsion (W.map (algebraMap R K)).toAffine.Point) ∧
      Nat.card (AddCommGroup.torsion (W.map (algebraMap R K)).toAffine.Point) ∣
        Nat.card (W.map (algebraMap R (R ⧸ v.asIdeal))).toAffine.Point := by
  classical
  let w := v.valuation K
  let A := w.valuationSubring
  let F := ResidueField A
  let i : R →+* A := (algebraMap R K).codRestrict A.toSubring (fun r => v.valuation_le_one r)
  let WA := W.map i
  have hi : A.subtype.comp i = algebraMap R K := rfl
  have hWk : WA.map A.subtype = W.map (algebraMap R K) := by
    dsimp only [WA]
    rw [WeierstrassCurve.map_map, hi]
  letI : (WA.map A.subtype).IsElliptic := hWk.symm ▸ inferInstance
  obtain ⟨er, her⟩ := dedekind_residue_equiv (K := K) v
  let fR : A →+* (R ⧸ v.asIdeal) := residueHom v
  have hfi : fR.comp i = algebraMap R (R ⧸ v.asIdeal) := by
    ext r
    exact residueHom_algebraMap v r
  have hmod : (WA.map (residue A)).map er.toRingHom = W.map (algebraMap R (R ⧸ v.asIdeal)) := by
    dsimp only [WA]
    rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map,
      her, hfi]
  have hΔ : (WA.map (residue A)).Δ ≠ 0 := by
    intro hz
    have hg : (W.map (algebraMap R (R ⧸ v.asIdeal))).Δ ≠ 0 :=
      isUnit_iff_ne_zero.mp (W.map (algebraMap R (R ⧸ v.asIdeal))).isUnit_Δ
    apply hg
    rw [← hmod, WeierstrassCurve.map_Δ, hz, map_zero]
  letI : Algebra A (R ⧸ v.asIdeal) := fR.toAlgebra
  let σ : F ≃ₐ[A] (R ⧸ v.asIdeal) := AlgEquiv.ofRingEquiv (f := er) (by
    intro a
    exact DFunLike.congr_fun her a)
  let eF : (WA.map (residue A)).toAffine.Point ≃+
      (W.map (algebraMap R (R ⧸ v.asIdeal))).toAffine.Point :=
    (curvePointCongr (by ext <;> rfl)).trans
      ((pointBaseChangeEquiv WA.toAffine σ).trans
        (curvePointCongr (by
          change WA.map fR = W.map (algebraMap R (R ⧸ v.asIdeal))
          dsimp only [WA]
          rw [WeierstrassCurve.map_map, hfi])))
  let eK : (W.map (algebraMap R K)).toAffine.Point ≃+ (WA.map A.subtype).toAffine.Point :=
    curvePointCongr (congrArg WeierstrassCurve.toAffine hWk.symm)
  let f : AddCommGroup.torsion (W.map (algebraMap R K)).toAffine.Point →+
      (WA.map (residue A)).toAffine.Point :=
    (WeierstrassCurve.reduceHom hΔ).comp
      (eK.toAddMonoidHom.comp (AddCommGroup.torsion (W.map (algebraMap R K)).toAffine.Point).subtype)
  have hf : Function.Injective f := by
    intro P Q hPQ
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply eK.injective
    rw [map_zero]
    apply unramified_torsion_kernel_zero w p hp hv WA hΔ
    · exact eK.toAddMonoidHom.isOfFinAddOrder (P - Q).property
    · change f (P - Q) = 0
      rw [map_sub, hPQ, sub_self]
  letI : Finite (WA.map (residue A)).toAffine.Point :=
    Finite.of_equiv (W.map (algebraMap R (R ⧸ v.asIdeal))).toAffine.Point eF.symm.toEquiv
  refine ⟨Finite.of_injective f hf, ?_⟩
  rw [← Nat.card_congr eF.toEquiv]
  exact AddSubgroup.card_dvd_of_injective f hf

end MazurReduction
#print axioms MazurReduction.dedekind_torsion_card_bound

end


/- Source module: MazurReduction.UnramifiedAdicValuation. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace MazurReduction

/-- Boundary: translate a Dedekind ramification certificate into the discrete
valuation normalization consumed by the full torsion reduction bound.
Named downstream consumer: the order-18 prime above seventeen. -/
theorem adic_valuation_of_ramification_one
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra ℤ R] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (p : ℕ)
    [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] (hp0 : (p : R) ≠ 0)
    (hv : v.asIdeal.ramificationIdx ℤ = 1) :
    v.valuation K (algebraMap R K (p : R)) = exp (-1 : ℤ) := by
  have hmap : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ R) = Ideal.span {(p : R)} := by
    simp [Ideal.map_span]
  have hne : (Ideal.span {(p : ℤ)}).map (algebraMap ℤ R) ≠ ⊥ := by
    rw [hmap]
    exact Submodule.span_singleton_eq_bot.mp.mt hp0
  have hm := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
    (Ideal.span {(p : ℤ)}) v.asIdeal hne
  rw [hv, hmap] at hm
  rw [v.valuation_of_algebraMap, v.intValuation_eq_exp_neg_multiplicity hp0, ← hm]
  norm_num

end MazurReduction
#print axioms MazurReduction.adic_valuation_of_ramification_one

end


/- Source module: MazurTransfer.DedekindFinitePoint. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
namespace MazurTransfer
/-- Boundary: a finite point group equals its full torsion subgroup.
Named downstream consumer: the order-18 cubic-field 21-point bound. -/
noncomputable def finitePointTorsionEquivGeneral {K : Type*} [Field K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] [Finite W.toAffine.Point] :
    W.toAffine.Point ≃+ AddCommGroup.torsion W.toAffine.Point :=
  (AddEquiv.ofBijective (AddCommGroup.torsion W.toAffine.Point).subtype
    ⟨Subtype.val_injective, fun P => ⟨⟨P, isOfFinAddOrder_of_finite P⟩, rfl⟩⟩).symm
lemma finite_dedekind_point_card_dvd
    {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [DecidableEq K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) [Finite (R ⧸ v.asIdeal)]
    (p : ℕ) [Fact p.Prime] (hp : 2 < p)
    (hv : v.valuation K (p : K) = exp (-1 : ℤ))
    (W : WeierstrassCurve R) [(W.map (algebraMap R K)).IsElliptic]
    [(W.map (algebraMap R (R ⧸ v.asIdeal))).IsElliptic]
    [Finite (W.map (algebraMap R K)).toAffine.Point] :
    Nat.card (W.map (algebraMap R K)).toAffine.Point ∣
      Nat.card (W.map (algebraMap R (R ⧸ v.asIdeal))).toAffine.Point := by
  rw [Nat.card_congr (finitePointTorsionEquivGeneral (W.map (algebraMap R K))).toEquiv]
  exact (MazurReduction.dedekind_torsion_card_bound v p hp hv W).2
end MazurTransfer

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenQuotientThreeTorsion. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Excluding three-torsion on the `X₁(18)` elliptic quotient

The third division polynomial of the real-cubic quotient has a linear
factor and a cubic factor.  The linear factor would make `-3` a square in
the coefficient field.  After an exact translation, the cubic factor is
the rational cubic `Z³ + 6Z - 2`.  The coefficient field is the normal
cubic field generated by a root of `T³ - 3T - 1`; normality would make the
second cubic split there.  Its discriminant is `-972`, so this would again
put a square root of `-3` in a cubic field, contradicting the tower-degree
formula.

All arguments are internal algebraic certificates.  In particular, no
injectivity assertion for reduction of torsion is used.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenQuotientThreeTorsion

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient

private theorem tau_pow_four : tau ^ 4 = 3 * tau ^ 2 + tau := by
  calc
    tau ^ 4 = tau * tau ^ 3 := by ring
    _ = 3 * tau ^ 2 + tau := by rw [tau_cubic]; ring

private theorem tau_pow_five : tau ^ 5 = tau ^ 2 + 9 * tau + 3 := by
  calc
    tau ^ 5 = tau * tau ^ 4 := by ring
    _ = tau * (3 * tau ^ 2 + tau) := by rw [tau_pow_four]
    _ = 3 * tau ^ 3 + tau ^ 2 := by ring
    _ = tau ^ 2 + 9 * tau + 3 := by rw [tau_cubic]; ring

private theorem tau_pow_six : tau ^ 6 = 9 * tau ^ 2 + 6 * tau + 1 := by
  calc
    tau ^ 6 = tau * tau ^ 5 := by ring
    _ = tau * (tau ^ 2 + 9 * tau + 3) := by rw [tau_pow_five]
    _ = tau ^ 3 + 9 * tau ^ 2 + 3 * tau := by ring
    _ = 9 * tau ^ 2 + 6 * tau + 1 := by rw [tau_cubic]; ring

private theorem tau_pow_seven : tau ^ 7 = 6 * tau ^ 2 + 28 * tau + 9 := by
  calc
    tau ^ 7 = tau * tau ^ 6 := by ring
    _ = tau * (9 * tau ^ 2 + 6 * tau + 1) := by rw [tau_pow_six]
    _ = 9 * tau ^ 3 + 6 * tau ^ 2 + tau := by ring
    _ = 6 * tau ^ 2 + 28 * tau + 9 := by rw [tau_cubic]; ring

private theorem tau_pow_eight : tau ^ 8 = 28 * tau ^ 2 + 27 * tau + 6 := by
  calc
    tau ^ 8 = tau * tau ^ 7 := by ring
    _ = tau * (6 * tau ^ 2 + 28 * tau + 9) := by rw [tau_pow_seven]
    _ = 6 * tau ^ 3 + 28 * tau ^ 2 + 9 * tau := by ring
    _ = 28 * tau ^ 2 + 27 * tau + 6 := by rw [tau_cubic]; ring

/-! ## The normal coefficient cubic -/

private theorem coefficientPolynomial_map_factorization :
    cubicPolynomial.map (algebraMap ℚ K) =
      (X - C tau) * (X - C (tau ^ 2 - tau - 2)) *
        (X - C (-tau ^ 2 + 2)) := by
  change ((X ^ 3 - 3 * X - 1 : Polynomial ℚ).map
    (algebraMap ℚ K)) = _
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_ofNat, Polynomial.map_one, map_X]
  have hsum :
      tau + (tau ^ 2 - tau - 2) + (-tau ^ 2 + 2) = 0 := by
    ring
  have hpairs :
      tau * (tau ^ 2 - tau - 2) + tau * (-tau ^ 2 + 2) +
        (tau ^ 2 - tau - 2) * (-tau ^ 2 + 2) = -3 := by
    ring_nf
    simp only [tau_pow_four, tau_cubic]
    ring
  have hprod :
      tau * (tau ^ 2 - tau - 2) * (-tau ^ 2 + 2) = 1 := by
    ring_nf
    simp only [tau_pow_five, tau_pow_four, tau_cubic]
    ring
  calc
    (X ^ 3 - 3 * X - 1 : Polynomial K) =
        X ^ 3 - C (tau + (tau ^ 2 - tau - 2) + (-tau ^ 2 + 2)) * X ^ 2 +
          C (tau * (tau ^ 2 - tau - 2) + tau * (-tau ^ 2 + 2) +
            (tau ^ 2 - tau - 2) * (-tau ^ 2 + 2)) * X -
          C (tau * (tau ^ 2 - tau - 2) * (-tau ^ 2 + 2)) := by
      rw [hsum, hpairs, hprod]
      norm_num
      rw [C_ofNat]
      ring
    _ = (X - C tau) * (X - C (tau ^ 2 - tau - 2)) *
        (X - C (-tau ^ 2 + 2)) := by
      simp only [C_add, C_sub, C_neg, C_mul]
      ring

private theorem coefficientPolynomial_splits :
    (cubicPolynomial.map (algebraMap ℚ K)).Splits := by
  rw [coefficientPolynomial_map_factorization]
  exact ((Splits.X_sub_C tau).mul
    (Splits.X_sub_C (tau ^ 2 - tau - 2))).mul
      (Splits.X_sub_C (-tau ^ 2 + 2))

private theorem tau_mem_coefficientPolynomial_rootSet :
    tau ∈ cubicPolynomial.rootSet K := by
  rw [mem_rootSet_of_ne cubicPolynomial_irreducible.ne_zero]
  simp only [Polynomial.aeval_def, cubicPolynomial, eval₂_sub, eval₂_X_pow,
    eval₂_mul, eval₂_X, eval₂_ofNat, eval₂_one]
  linear_combination tau_cubic

private instance coefficientField_isSplittingField :
    Polynomial.IsSplittingField ℚ K cubicPolynomial where
  splits' := coefficientPolynomial_splits
  adjoin_rootSet' := by
    apply top_unique
    calc
      ⊤ = Algebra.adjoin ℚ ({tau} : Set K) :=
        (AdjoinRoot.adjoinRoot_eq_top (f := cubicPolynomial)).symm
      _ ≤ Algebra.adjoin ℚ (cubicPolynomial.rootSet K) := by
        apply Algebra.adjoin_mono
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        simpa only [hz] using tau_mem_coefficientPolynomial_rootSet

private instance coefficientField_normal : Normal ℚ K :=
  Normal.of_isSplittingField cubicPolynomial

private theorem finrank_coefficientField : Module.finrank ℚ K = 3 := by
  calc
    Module.finrank ℚ K = cubicPolynomial.natDegree :=
      (AdjoinRoot.powerBasis cubicPolynomial_irreducible.ne_zero).finrank
    _ = 3 := by
      simp only [cubicPolynomial]
      compute_degree!

/-! ## A cubic field has no quadratic subfield -/

private def negThreePolynomial : Polynomial ℚ :=
  X ^ 2 + 3

private theorem negThreePolynomial_monic : negThreePolynomial.Monic := by
  simp only [negThreePolynomial]
  monicity
  norm_num

private theorem negThreePolynomial_natDegree :
    negThreePolynomial.natDegree = 2 := by
  simp only [negThreePolynomial]
  compute_degree!

private theorem negThreePolynomial_irreducible :
    Irreducible negThreePolynomial := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (p := negThreePolynomial) ?_ ?_
  · rw [negThreePolynomial_natDegree]
    norm_num
  · intro z
    unfold Polynomial.IsRoot
    simp only [negThreePolynomial, eval_add, eval_pow, eval_X,
      eval_ofNat]
    nlinarith [sq_nonneg z]

private theorem no_square_root_neg_three (z : K) : z ^ 2 ≠ -3 := by
  intro hz
  have hsplits :
      (negThreePolynomial.map (algebraMap ℚ K)).Splits := by
    apply Splits.of_natDegree_eq_two (x := z)
    · rw [negThreePolynomial_monic.natDegree_map]
      exact negThreePolynomial_natDegree
    · rw [eval_map_algebraMap]
      simp only [negThreePolynomial, Polynomial.aeval_def, eval₂_add,
        eval₂_X_pow, eval₂_ofNat]
      linear_combination hz
  have hdvd :=
    negThreePolynomial_irreducible.natDegree_dvd_finrank hsplits
  rw [negThreePolynomial_natDegree, finrank_coefficientField] at hdvd
  norm_num at hdvd

/-! ## The translated cubic factor -/

private def depressedPolynomialInt : Polynomial ℤ :=
  X ^ 3 + 6 * X - 2

private theorem depressedPolynomialInt_monic :
    depressedPolynomialInt.Monic := by
  simp only [depressedPolynomialInt]
  monicity <;> norm_num

private theorem depressedPolynomialInt_mod_seven :
    depressedPolynomialInt.map (Int.castRingHom (ZMod 7)) =
      (X ^ 3 + 6 * X - 2 : Polynomial (ZMod 7)) := by
  norm_num [depressedPolynomialInt]

private theorem depressedPolynomial_mod_seven_irreducible :
    Irreducible (X ^ 3 + 6 * X - 2 : Polynomial (ZMod 7)) := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hdegree :
      (X ^ 3 + 6 * X - 2 : Polynomial (ZMod 7)).natDegree = 3 := by
    compute_degree <;> norm_num
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (p := (X ^ 3 + 6 * X - 2 : Polynomial (ZMod 7))) ?_ ?_
  · rw [hdegree]
    norm_num
  · intro z
    unfold Polynomial.IsRoot
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
    fin_cases z
    · change ¬ ((0 : ZMod 7) ^ 3 + 6 * 0 - 2 = 0)
      decide
    · change ¬ ((1 : ZMod 7) ^ 3 + 6 * 1 - 2 = 0)
      decide
    · change ¬ ((2 : ZMod 7) ^ 3 + 6 * 2 - 2 = 0)
      decide
    · change ¬ ((3 : ZMod 7) ^ 3 + 6 * 3 - 2 = 0)
      decide
    · change ¬ ((4 : ZMod 7) ^ 3 + 6 * 4 - 2 = 0)
      decide
    · change ¬ ((5 : ZMod 7) ^ 3 + 6 * 5 - 2 = 0)
      decide
    · change ¬ ((6 : ZMod 7) ^ 3 + 6 * 6 - 2 = 0)
      decide

private theorem depressedPolynomialInt_irreducible :
    Irreducible depressedPolynomialInt := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply depressedPolynomialInt_monic.irreducible_of_irreducible_map
    (Int.castRingHom (ZMod 7))
  simpa only [depressedPolynomialInt_mod_seven] using
    depressedPolynomial_mod_seven_irreducible

private def depressedPolynomial : Polynomial ℚ :=
  X ^ 3 + 6 * X - 2

private theorem depressedPolynomial_eq_map_int :
    depressedPolynomialInt.map (algebraMap ℤ ℚ) =
      depressedPolynomial := by
  norm_num [depressedPolynomialInt, depressedPolynomial]

private theorem depressedPolynomial_monic : depressedPolynomial.Monic := by
  simp only [depressedPolynomial]
  monicity <;> norm_num



private theorem depressedPolynomial_irreducible :
    Irreducible depressedPolynomial := by
  rw [← depressedPolynomial_eq_map_int]
  exact
    (depressedPolynomialInt_monic.irreducible_iff_irreducible_map_fraction_map
      (K := ℚ)).mp depressedPolynomialInt_irreducible

private def depressedCubic : Cubic ℚ :=
  ⟨1, 0, 6, -2⟩

private theorem depressedCubic_toPoly :
    depressedCubic.toPoly = depressedPolynomial := by
  simp [depressedCubic, depressedPolynomial, Cubic.toPoly,
    ← Polynomial.C_ofNat, sub_eq_add_neg]

private theorem depressedCubic_discriminant :
    depressedCubic.discr = -972 := by
  norm_num [depressedCubic, Cubic.discr]

private theorem depressedPolynomial_no_root (z : K) :
    Polynomial.eval z (depressedPolynomial.map (algebraMap ℚ K)) ≠ 0 := by
  intro hz
  have hmin : depressedPolynomial = minpoly ℚ z := by
    apply minpoly.eq_of_irreducible_of_monic depressedPolynomial_irreducible
    · change Polynomial.eval₂ (algebraMap ℚ K) z depressedPolynomial = 0
      rw [← eval_map]
      exact hz
    · exact depressedPolynomial_monic
  have hsplits :
      (depressedPolynomial.map (algebraMap ℚ K)).Splits := by
    rw [hmin]
    exact Normal.splits coefficientField_normal z
  have hsplitsCubic :
      (depressedCubic.toPoly.map (algebraMap ℚ K)).Splits := by
    rwa [depressedCubic_toPoly]
  have ha : depressedCubic.a ≠ 0 := by
    norm_num [depressedCubic]
  obtain ⟨a, b, c, hroots⟩ :=
    (Cubic.splits_iff_roots_eq_three
      (P := depressedCubic) (φ := algebraMap ℚ K) ha).mp
        hsplitsCubic
  have hdisc := Cubic.discr_eq_prod_three_roots
    (P := depressedCubic) (φ := algebraMap ℚ K)
    (x := a) (y := b) (z := c) ha hroots
  rw [depressedCubic_discriminant] at hdisc
  let w : K :=
    algebraMap ℚ K depressedCubic.a *
      algebraMap ℚ K depressedCubic.a *
        (a - b) * (a - c) * (b - c)
  have hw : w ^ 2 = (-972 : K) := by
    dsimp only [w]
    simpa using hdisc.symm
  apply no_square_root_neg_three (w / 18)
  calc
    (w / 18) ^ 2 = w ^ 2 / 324 := by ring
    _ = (-972 : K) / 324 := by rw [hw]
    _ = -3 := by norm_num

/-! ## The third division polynomial -/

private theorem tangent_forces_three_division
    {a₁ a₂ a₃ a₄ a₆ x y slope : K}
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

private theorem eval_psi_three_eq_zero_of_three_nsmul
    {x y : K} (hP : quotientCurve.toAffine.Nonsingular x y)
    (hthree : (3 : ℕ) •
      WeierstrassCurve.Affine.Point.some x y hP = 0) :
    Polynomial.eval x quotientCurve.toAffine.Ψ₃ = 0 := by
  let P := WeierstrassCurve.Affine.Point.some x y hP
  have hthree' : (2 : ℕ) • P + P = 0 := by
    simpa [P, three_nsmul, two_nsmul, add_assoc] using hthree
  have hdouble : (2 : ℕ) • P = -P := by
    calc
      (2 : ℕ) • P = (3 : ℕ) • P - P := by abel
      _ = -P := by rw [show (3 : ℕ) • P = 0 from hthree]; exact zero_sub P
  have hy : y ≠ quotientCurve.toAffine.negY x y := by
    intro hy
    have htwo : (2 : ℕ) • P = 0 := by
      change (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
    have hzero : P = 0 := by
      rw [htwo] at hthree'
      exact (zero_add P).symm.trans hthree'
    exact WeierstrassCurve.Affine.Point.some_ne_zero hP hzero
  let slope := quotientCurve.toAffine.slope x x y y
  have hadd :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hP) hy
  have hxcoord : quotientCurve.toAffine.addX x x slope = x := by
    have hsum : P + P = -P := by
      simpa [two_nsmul] using hdouble
    have hsome := hadd.symm.trans hsum
    exact (WeierstrassCurve.Affine.Point.some.inj hsome).1
  have hslope :
      slope * (2 * y + quotientCurve.toAffine.a₁ * x +
        quotientCurve.toAffine.a₃) =
      3 * x ^ 2 + 2 * quotientCurve.toAffine.a₂ * x +
        quotientCurve.toAffine.a₄ - quotientCurve.toAffine.a₁ * y := by
    have hden : y - quotientCurve.toAffine.negY x y =
        2 * y + quotientCurve.toAffine.a₁ * x +
          quotientCurve.toAffine.a₃ := by
      simp only [WeierstrassCurve.Affine.negY]
      ring
    dsimp [slope]
    rw [← hden, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,
      div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
  have hx : slope ^ 2 + quotientCurve.toAffine.a₁ * slope -
      quotientCurve.toAffine.a₂ - 3 * x = 0 := by
    simp only [WeierstrassCurve.Affine.addX] at hxcoord
    linear_combination hxcoord
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  have hpsi := tangent_forces_three_division hcurve hslope hx
  simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring_nf at hpsi ⊢
  exact hpsi

private theorem quotientCurve_psi_three_factorization (x : K) :
    Polynomial.eval x quotientCurve.toAffine.Ψ₃ =
      (3 * x + tau ^ 2 + tau - 2) *
        ((x + (tau ^ 2 + tau - 3) / 3) ^ 3 +
          (2 / 3) * (x + (tau ^ 2 + tau - 3) / 3) - 2 / 27) := by
  simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    quotientCurve, WeierstrassCurve.toAffine]
  ring_nf
  simp only [tau_pow_eight, tau_pow_seven, tau_pow_six, tau_pow_five,
    tau_pow_four, tau_cubic]
  ring

private theorem linear_factor_impossible
    {x y : K} (hP : quotientCurve.toAffine.Nonsingular x y)
    (hlinear : 3 * x + tau ^ 2 + tau - 2 = 0) : False := by
  have hx : x = (2 - tau ^ 2 - tau) / 3 := by
    linear_combination (1 / 3 : K) * hlinear
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  have hdisc :
      (x + (tau ^ 2 + tau - 1)) ^ 2 +
        4 * (x ^ 3 + (tau ^ 2 + tau - 3) * x ^ 2 +
          (-tau ^ 2 + 4) * x - tau - 2) = (-1 / 3 : K) := by
    rw [hx]
    ring_nf
    simp only [tau_pow_six, tau_pow_five, tau_pow_four, tau_cubic]
    ring
  have hsquare :
      (2 * y + x + (tau ^ 2 + tau - 1)) ^ 2 = (-1 / 3 : K) := by
    calc
      (2 * y + x + (tau ^ 2 + tau - 1)) ^ 2 =
          4 * (y ^ 2 + x * y + (tau ^ 2 + tau - 1) * y) +
            (x + (tau ^ 2 + tau - 1)) ^ 2 := by ring
      _ = 4 * (x ^ 3 + (tau ^ 2 + tau - 3) * x ^ 2 +
            (-tau ^ 2 + 4) * x - tau - 2) +
            (x + (tau ^ 2 + tau - 1)) ^ 2 := by
          rw [show y ^ 2 + x * y + (tau ^ 2 + tau - 1) * y =
            x ^ 3 + (tau ^ 2 + tau - 3) * x ^ 2 +
              (-tau ^ 2 + 4) * x - tau - 2 by
            simpa [quotientCurve, sub_eq_add_neg, add_assoc] using hcurve]
      _ = -1 / 3 := by linear_combination hdisc
  apply no_square_root_neg_three
    (3 * (2 * y + x + (tau ^ 2 + tau - 1)))
  calc
    (3 * (2 * y + x + (tau ^ 2 + tau - 1))) ^ 2 =
        9 * (-1 / 3 : K) := by rw [mul_pow, hsquare]; ring
    _ = -3 := by norm_num

private theorem cubic_factor_impossible (x : K)
    (hcubic :
      (x + (tau ^ 2 + tau - 3) / 3) ^ 3 +
        (2 / 3) * (x + (tau ^ 2 + tau - 3) / 3) - 2 / 27 = 0) : False := by
  let z : K := 3 * (x + (tau ^ 2 + tau - 3) / 3)
  apply depressedPolynomial_no_root z
  rw [show depressedPolynomial.map (algebraMap ℚ K) =
    X ^ 3 + 6 * X - 2 by norm_num [depressedPolynomial]]
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_ofNat]
  dsimp only [z]
  linear_combination 27 * hcubic

/-- The real-cubic quotient has no nonidentity point killed by three. -/
theorem eq_zero_of_three_nsmul_eq_zero
    (P : quotientCurve.toAffine.Point) (hP : (3 : ℕ) • P = 0) :
    P = 0 := by
  cases P with
  | zero => rfl
  | some x y hxy =>
      exfalso
      have hpsi := eval_psi_three_eq_zero_of_three_nsmul hxy hP
      rw [quotientCurve_psi_three_factorization] at hpsi
      rcases mul_eq_zero.mp hpsi with hlinear | hcubic
      · exact linear_factor_impossible hxy hlinear
      · exact cubic_factor_impossible x hcubic

end

end MazurTorsion.XOneEighteenQuotientThreeTorsion

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenFinalQuotientFibers. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The finite fibers of the `X₁(18)` real-cubic quotient

The seven points in the cyclic subgroup generated by `(1,0)` on the
real-cubic quotient have only three affine abscissas:

`1`, `3 - τ²`, and `1 - τ`.

This file proves directly that the quotient of a rational sextic abscissa
cannot have the first value, and can have the other two only at the cusp
abscissas `0` and `1`.  The proof clears the genuine quotient denominator
and uses the degree-three minimal polynomial of `τ`; no point enumeration
or Mordell--Weil assertion is made here.
-/

open Polynomial

namespace MazurTorsion.XOneEighteenFinalQuotientFibers

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient

private theorem cubicPolynomial_monic : cubicPolynomial.Monic := by
  simp only [cubicPolynomial]
  monicity <;> norm_num

private theorem of_rat_eq_cast (q : ℚ) :
    AdjoinRoot.of cubicPolynomial q = (q : K) := by
  rw [← AdjoinRoot.algebraMap_eq]
  exact map_ratCast (algebraMap ℚ K) q

/-- A nonzero rational polynomial of degree at most two cannot vanish at
the cubic generator `τ`. -/
private theorem quadratic_tau_ne_zero
    (a b c : ℚ)
    (hp : C a * X ^ 2 + C b * X + C c ≠ (0 : Polynomial ℚ)) :
    (a : K) * tau ^ 2 + (b : K) * tau + (c : K) ≠ 0 := by
  intro h
  have hdeg :
      (C a * X ^ 2 + C b * X + C c : Polynomial ℚ).natDegree <
        cubicPolynomial.natDegree := by
    have hp_le :
        (C a * X ^ 2 + C b * X + C c : Polynomial ℚ).natDegree ≤ 2 := by
      compute_degree
    have hcubic : cubicPolynomial.natDegree = 3 := by
      simp only [cubicPolynomial]
      compute_degree!
    omega
  apply
    AdjoinRoot.mk_ne_zero_of_natDegree_lt cubicPolynomial_monic hp hdeg
  change
    AdjoinRoot.mk cubicPolynomial
      (C a * X ^ 2 + C b * X + C c) = 0
  simpa only [map_add, map_mul, map_pow, AdjoinRoot.mk_C,
    AdjoinRoot.mk_X, of_rat_eq_cast, tau] using h

private theorem first_relation_polynomial_ne_zero (x : ℚ) :
    C (x + 1) * X ^ 2 + C (3 * x + 1) * X + C x ≠
      (0 : Polynomial ℚ) := by
  intro h
  have htwo := congrArg (fun p : Polynomial ℚ ↦ p.coeff 2) h
  have hone := congrArg (fun p : Polynomial ℚ ↦ p.coeff 1) h
  simp only [C_mul_X_pow_eq_monomial, C_mul_X_eq_monomial,
    coeff_add, coeff_monomial, coeff_C, coeff_zero] at htwo hone
  norm_num at htwo hone
  linarith

private theorem second_relation_polynomial_ne_zero (x : ℚ) :
    C (x - 1) * X ^ 2 + C (-1) * X + C (-2 * x + 1) ≠
      (0 : Polynomial ℚ) := by
  intro h
  have hone := congrArg (fun p : Polynomial ℚ ↦ p.coeff 1) h
  rw [C_mul_X_pow_eq_monomial, C_mul_X_eq_monomial] at hone
  norm_num [coeff_add, coeff_monomial, coeff_C, coeff_one,
    coeff_zero] at hone

private theorem third_relation_polynomial_ne_zero (x : ℚ) :
    C 1 * X ^ 2 + C (x - 2) * X + C (-1) ≠
      (0 : Polynomial ℚ) := by
  intro h
  have htwo := congrArg (fun p : Polynomial ℚ ↦ p.coeff 2) h
  rw [C_mul_X_pow_eq_monomial, C_mul_X_eq_monomial] at htwo
  norm_num [coeff_add, coeff_monomial, coeff_C, coeff_one,
    coeff_zero] at htwo

private theorem tau_pow_four : tau ^ 4 = 3 * tau ^ 2 + tau := by
  calc
    tau ^ 4 = tau * tau ^ 3 := by ring
    _ = 3 * tau ^ 2 + tau := by rw [tau_cubic]; ring

private theorem tau_pow_five : tau ^ 5 = tau ^ 2 + 9 * tau + 3 := by
  calc
    tau ^ 5 = tau * tau ^ 4 := by ring
    _ = tau * (3 * tau ^ 2 + tau) := by rw [tau_pow_four]
    _ = 3 * tau ^ 3 + tau ^ 2 := by ring
    _ = tau ^ 2 + 9 * tau + 3 := by rw [tau_cubic]; ring

private theorem tau_pow_six : tau ^ 6 = 9 * tau ^ 2 + 6 * tau + 1 := by
  calc
    tau ^ 6 = tau * tau ^ 5 := by ring
    _ = tau * (tau ^ 2 + 9 * tau + 3) := by rw [tau_pow_five]
    _ = tau ^ 3 + 9 * tau ^ 2 + 3 * tau := by ring
    _ = 9 * tau ^ 2 + 6 * tau + 1 := by rw [tau_cubic]; ring

/-! ## Cleared quotient identities -/

private theorem quotientX_sub_one_cleared (x : ℚ) :
    12 * ((x : K) + tau) ^ 2 * (quotientX x - 1) =
      -12 *
        (((x + 1 : ℚ) : K) * tau ^ 2 +
          ((3 * x + 1 : ℚ) : K) * tau + (x : K)) := by
  simp only [quotientX, quotientD]
  field_simp [rational_add_tau_ne_zero]
  ring_nf
  simp only [tau_pow_six, tau_pow_four, tau_cubic]
  push_cast
  ring

private theorem quotientX_sub_three_sub_tau_sq_cleared (x : ℚ) :
    12 * ((x : K) + tau) ^ 2 *
        (quotientX x - (3 - tau ^ 2)) =
      12 * (x : K) *
        ((((x - 1 : ℚ) : K) * tau ^ 2) - tau +
          ((-2 * x + 1 : ℚ) : K)) := by
  simp only [quotientX, quotientD]
  field_simp [rational_add_tau_ne_zero]
  ring_nf
  simp only [tau_pow_six, tau_pow_four, tau_cubic]
  push_cast
  ring

private theorem quotientX_sub_one_sub_tau_cleared (x : ℚ) :
    12 * ((x : K) + tau) ^ 2 *
        (quotientX x - (1 - tau)) =
      12 * (((x - 1 : ℚ) : K)) *
        (tau ^ 2 + ((x - 2 : ℚ) : K) * tau - 1) := by
  simp only [quotientX, quotientD]
  field_simp [rational_add_tau_ne_zero]
  ring_nf
  simp only [tau_pow_six, tau_pow_four, tau_cubic]
  push_cast
  ring

/-! ## The three finite fibers -/

/-- No rational abscissa maps to the torsion abscissa `1`. -/
theorem quotientX_ne_one (x : ℚ) : quotientX x ≠ 1 := by
  intro hx
  have hrel := quotientX_sub_one_cleared x
  rw [hx, sub_self, mul_zero] at hrel
  have hzero :
      (((x + 1 : ℚ) : K) * tau ^ 2 +
        ((3 * x + 1 : ℚ) : K) * tau + (x : K)) = 0 := by
    have hprod :
        (-12 : K) *
          (((x + 1 : ℚ) : K) * tau ^ 2 +
            ((3 * x + 1 : ℚ) : K) * tau + (x : K)) = 0 := hrel.symm
    exact (mul_eq_zero.mp hprod).resolve_left (by norm_num)
  exact
    quadratic_tau_ne_zero (x + 1) (3 * x + 1) x
      (first_relation_polynomial_ne_zero x) hzero

/-- The torsion abscissa `3-τ²` can occur only above the cusp `x=0`. -/
theorem quotientX_eq_three_sub_tau_sq_imp_eq_zero
    (x : ℚ) (hx : quotientX x = 3 - tau ^ 2) : x = 0 := by
  by_contra hx0
  have hrel := quotientX_sub_three_sub_tau_sq_cleared x
  rw [hx, sub_self, mul_zero] at hrel
  have hxK : (x : K) ≠ 0 := by exact_mod_cast hx0
  have hzero :
      (((x - 1 : ℚ) : K) * tau ^ 2 - tau +
        ((-2 * x + 1 : ℚ) : K)) = 0 := by
    have hprod :
        (12 : K) * (x : K) *
          ((((x - 1 : ℚ) : K) * tau ^ 2 - tau +
            ((-2 * x + 1 : ℚ) : K))) = 0 := hrel.symm
    exact
      (mul_eq_zero.mp hprod).resolve_left
        (mul_ne_zero (by norm_num) hxK)
  exact
    quadratic_tau_ne_zero (x - 1) (-1) (-2 * x + 1)
      (second_relation_polynomial_ne_zero x) (by
        simpa only [Rat.cast_neg, Rat.cast_one, neg_one_mul,
          sub_eq_add_neg] using hzero)

/-- The torsion abscissa `1-τ` can occur only above the cusp `x=1`. -/
theorem quotientX_eq_one_sub_tau_imp_eq_one
    (x : ℚ) (hx : quotientX x = 1 - tau) : x = 1 := by
  by_contra hx1
  have hrel := quotientX_sub_one_sub_tau_cleared x
  rw [hx, sub_self, mul_zero] at hrel
  have hxK : (((x - 1 : ℚ) : K)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr hx1
  have hzero : tau ^ 2 + ((x - 2 : ℚ) : K) * tau - 1 = 0 := by
    have hprod :
        (12 : K) * (((x - 1 : ℚ) : K)) *
          (tau ^ 2 + ((x - 2 : ℚ) : K) * tau - 1) = 0 := hrel.symm
    exact
      (mul_eq_zero.mp hprod).resolve_left
        (mul_ne_zero (by norm_num) hxK)
  exact
    quadratic_tau_ne_zero 1 (x - 2) (-1)
      (third_relation_polynomial_ne_zero x) (by
        simpa only [Rat.cast_one, Rat.cast_neg, one_mul, neg_one_mul,
          sub_eq_add_neg] using hzero)

/-- A rational noncuspidal sextic abscissa cannot map to any of the three
affine abscissas occurring in the seven-point torsion subgroup. -/
theorem quotientX_not_mem_torsion_abscissas
    (x : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    quotientX x ≠ 1 ∧
      quotientX x ≠ 3 - tau ^ 2 ∧
      quotientX x ≠ 1 - tau := by
  refine ⟨quotientX_ne_one x, ?_, ?_⟩
  · exact fun h ↦ hx0 (quotientX_eq_three_sub_tau_sq_imp_eq_zero x h)
  · exact fun h ↦ hx1 (quotientX_eq_one_sub_tau_imp_eq_one x h)

end

end MazurTorsion.XOneEighteenFinalQuotientFibers

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenQuotientFiniteClassification. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Finite-group classification of the `X₁(18)` elliptic quotient

Once good reduction bounds the finite quotient point group by a divisor of
`21`, the visible point of order seven and the absence of three-torsion force
the group to have exactly seven elements.  This file isolates that elementary
consumer from the number-field reduction and two-descent calculations.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenQuotientFiniteClassification

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenQuotientSevenTorsion
open MazurTorsion.XOneEighteenQuotientThreeTorsion
open MazurTorsion.XOneEighteenFinalQuotientFibers

/-- If the finite quotient point group has cardinality dividing `21`, then
the visible seven-torsion subgroup is the whole group. -/
theorem point_card_eq_seven [Finite quotientCurve.toAffine.Point]
    (hcard : Nat.card quotientCurve.toAffine.Point ∣ 21) :
    Nat.card quotientCurve.toAffine.Point = 7 := by
  have hseven : 7 ∣ Nat.card quotientCurve.toAffine.Point := by
    rw [← addOrderOf_generator]
    exact addOrderOf_dvd_natCard generator
  have hnotThree : ¬3 ∣ Nat.card quotientCurve.toAffine.Point := by
    intro hthree
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨P, hP⟩ :=
      exists_prime_addOrderOf_dvd_card' (G := quotientCurve.toAffine.Point)
        3 hthree
    have hsmul : (3 : ℕ) • P = 0 := by
      rw [← hP]
      exact addOrderOf_nsmul_eq_zero P
    have hzero := eq_zero_of_three_nsmul_eq_zero P hsmul
    rw [hzero, addOrderOf_zero] at hP
    norm_num at hP
  obtain ⟨k, hk⟩ := hseven
  have hkdiv : k ∣ 3 := by
    rw [hk] at hcard
    apply (mul_dvd_mul_iff_left (by norm_num : (7 : ℕ) ≠ 0)).mp
    simpa using hcard
  rcases (Nat.dvd_prime Nat.prime_three).mp hkdiv with hkone | hkthree
  · simpa [hkone] using hk
  · exfalso
    apply hnotThree
    rw [hk, hkthree]
    norm_num

/-- The seven multiples of the visible generator enumerate every point once
the reduction cardinality divisor is known. -/
theorem generatorMultiples_bijective
    [Finite quotientCurve.toAffine.Point]
    (hcard : Nat.card quotientCurve.toAffine.Point ∣ 21) :
    Function.Bijective
      (fun i : Fin 7 ↦ (i : ℕ) • generator) := by
  have hinj : Function.Injective
      (fun i : Fin 7 ↦ (i : ℕ) • generator) := by
    intro i j hij
    apply Fin.ext
    have hfinite : IsOfFinAddOrder generator := by
      rw [isOfFinAddOrder_iff_nsmul_eq_zero]
      exact ⟨7, by norm_num, seven_nsmul_generator⟩
    rw [hfinite.nsmul_eq_nsmul_iff_modEq, addOrderOf_generator] at hij
    exact Nat.ModEq.eq_of_lt_of_lt hij i.isLt j.isLt
  apply hinj.bijective_of_nat_card_le
  rw [Nat.card_fin, point_card_eq_seven hcard]

/-- Under the same finite reduction hypothesis, every point is one of the
seven explicitly displayed multiples of the visible generator. -/
theorem point_eq_visible_multiple
    [Finite quotientCurve.toAffine.Point]
    (hcard : Nat.card quotientCurve.toAffine.Point ∣ 21)
    (P : quotientCurve.toAffine.Point) :
    P = 0 ∨ P = generator ∨ P = pointTwo ∨ P = pointThree ∨
      P = pointFour ∨ P = -pointTwo ∨ P = -generator := by
  obtain ⟨i, rfl⟩ := (generatorMultiples_bijective hcard).2 P
  have hone : (1 : ℕ) • generator = generator := one_nsmul generator
  fin_cases i <;>
    simp [hone, two_nsmul_generator_eq_pointTwo,
      three_nsmul_generator_eq_pointThree,
      four_nsmul_generator_eq_pointFour,
      five_nsmul_generator_eq_neg_pointTwo,
      six_nsmul_generator_eq_neg_generator]

/-- The finite-cardinality conclusion supplied by good reduction is already
enough to exclude a noncuspidal rational point on the sextic. -/
theorem no_noncuspidal_point_of_point_card_dvd_twentyOne
    [Finite quotientCurve.toAffine.Point]
    (hcard : Nat.card quotientCurve.toAffine.Point ∣ 21)
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve :
      y ^ 2 = MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    False := by
  have havoid := quotientX_not_mem_torsion_abscissas x hx0 hx1
  have hcases := point_eq_visible_multiple hcard (quotientPoint x y hcurve)
  rcases hcases with hzero | hgen | htwo | hthree | hfour | hfive | hsix
  · exact WeierstrassCurve.Affine.Point.some_ne_zero _ hzero
  · apply havoid.1
    have hcoords : quotientX x = (1 : K) ∧ quotientY x y = 0 := by
      simpa only [quotientPoint, generator,
        WeierstrassCurve.Affine.Point.some.injEq] using hgen
    exact hcoords.1
  · apply havoid.2.1
    have hcoords :
        quotientX x = 3 - tau ^ 2 ∧ quotientY x y = 2 - tau ^ 2 := by
      simpa only [quotientPoint, pointTwo,
        WeierstrassCurve.Affine.Point.some.injEq] using htwo
    exact hcoords.1
  · apply havoid.2.2
    have hcoords :
        quotientX x = 1 - tau ∧ quotientY x y = -tau ^ 2 + tau := by
      simpa only [quotientPoint, pointThree,
        WeierstrassCurve.Affine.Point.some.injEq] using hthree
    exact hcoords.1
  · apply havoid.2.2
    have hcoords : quotientX x = 1 - tau ∧ quotientY x y = -tau := by
      simpa only [quotientPoint, pointFour,
        WeierstrassCurve.Affine.Point.some.injEq] using hfour
    exact hcoords.1
  · apply havoid.2.1
    have hcoords : quotientX x = 3 - tau ^ 2 ∧
        quotientY x y = quotientCurve.toAffine.negY
          (3 - tau ^ 2) (2 - tau ^ 2) := by
      simpa only [quotientPoint, pointTwo,
        WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.some.injEq] using hfive
    exact hcoords.1
  · apply havoid.1
    have hcoords : quotientX x = (1 : K) ∧
        quotientY x y = quotientCurve.toAffine.negY 1 0 := by
      simpa only [quotientPoint, generator,
        WeierstrassCurve.Affine.Point.neg_some,
        WeierstrassCurve.Affine.Point.some.injEq] using hsix
    exact hcoords.1

end

end MazurTorsion.XOneEighteenQuotientFiniteClassification

end


/- Source module: EllipticCurves.ReductionAtPrime. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


/-!
# Reduction of points modulo a prime of the base ring

Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
Exact-pin changes are documented in `PORTING.md`.

Let `E` be an elliptic curve over the fraction field `K` of a Dedekind domain `R`, let `v` be a
maximal ideal (height-one prime) of `R`, and let `W₀` be an integral model of `E` over `R`
(`hE : W₀.map (algebraMap R K) = E`) whose reduction modulo `v` is again elliptic — *good
reduction* at `v`, the instance hypothesis `[(redCurve v W₀).IsElliptic]`.  This file defines the
reduced curve `redCurve v W₀` over the residue field `R ⧸ v.asIdeal` and the reduction
homomorphism `redHom v hE : E(K) →+ E_red(R ⧸ v.asIdeal)` — a point with `v`-integral coordinates
maps to their residues (via `residueHom v`), a point with a pole at `v` maps to `0` — with **no
completions in the definitions or statements**.

The completion `K_v` enters only through proofs: `adicRed_pointMap` identifies `red v hE` with
the reduction map `adicRed` of the base-changed curve over `K_v` (where the formal-group
machinery of `EllipticCurves.WeierstrassFormalGroup` lives), and additivity, injectivity on
torsion, and preservation of the order of torsion points are transported back along it.

## Main definitions and statements

* `WeierstrassCurve.Affine.redCurve`: the reduction `E_red` of `W₀` modulo `v`, a Weierstrass curve
  over `R ⧸ v.asIdeal`.
* `WeierstrassCurve.Affine.red`, `WeierstrassCurve.Affine.redHom`: the reduction map
  `E(K) →+ E_red(R ⧸ v.asIdeal)`.
* `WeierstrassCurve.Affine.nsmul_eq_zero_of_red_nsmul_eq_zero`: if the reduction of a torsion
  point is `m`-torsion, so is the point itself — under the standard ramification condition on
  the residue characteristic `p`, namely `(p : R) ∈ v.asIdeal` and `(p : R) ∉ v.asIdeal ^ (p - 1)`
  (that is, `e ≤ p - 2` for the ramification index `e`, e.g. `p` odd and `v` unramified).
* `WeierstrassCurve.Affine.addOrderOf_red`: under the same condition, reduction preserves the
  order of a torsion point.
* `WeierstrassCurve.Affine.addOrderOf_dvd_natCard_red`: consequently, the order of a torsion
  point divides the number of points of the reduction.
-/

section

open Function IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R) {E : Affine K} {W₀ : WeierstrassCurve R}
  (hE : W₀.map (algebraMap R K) = E)

/-- The reduction `E_red` of the integral model `W₀` modulo the prime `v`, a Weierstrass curve over
the residue field `R ⧸ v.asIdeal`: the base change of `W₀` along
`algebraMap R (R ⧸ v.asIdeal) = Ideal.Quotient.mk v.asIdeal`.  *Good reduction* of `W₀` at `v`
is the instance hypothesis `[(redCurve v W₀).IsElliptic]`. -/
noncomputable abbrev redCurve (W₀ : WeierstrassCurve R) : Affine (R ⧸ v.asIdeal) :=
  ((W₀.toAffine ⁄ (R ⧸ v.asIdeal)) : WeierstrassCurve _).toAffine

/-! ### The reduction map, defined over `K`

The definition of `red` needs three facts about a point of `E(K)` with `v`-integral
`x`-coordinate: its `y`-coordinate is `v`-integral, the residues of its coordinates satisfy the
reduced Weierstrass equation, and (under good reduction) they are a nonsingular point of `E_red`.
The first is transported from the completion (`integral_of_not_mem`); the others are proved
directly from `residueHom`. -/

















section

variable [(redCurve v W₀).IsElliptic]









end

/-! ### Transport from the completion

The following identifies `red v hE` with the reduction map `adicRed` of the base-changed curve
over the completion `K_v`, along the base change of points `E(K) → E(K_v)` and the residue field
isomorphism `R ⧸ v.asIdeal ≃+* 𝒪_v ⧸ 𝔪_v`.  All group-theoretic properties of `red` follow.
The group structures on the point sets require decidable equality of the base fields
(`[DecidableEq K]`, `[DecidableEq (R ⧸ v.asIdeal)]` in the public statements); the corresponding
instances on the completion and its residue field appear only in private lemmas and are
discharged with `classical` in the proofs of the public ones. -/

section Transport

/- `𝒪_v ⧸ 𝔪_v` as an algebra over `R` (via `𝒪_v`) and over `R ⧸ v.asIdeal` (via the residue
field isomorphism), used only in this section. -/


















section

variable [DecidableEq (R ⧸ v.asIdeal)]





end

variable [(redCurve v W₀).IsElliptic]





variable [DecidableEq (R ⧸ v.asIdeal)] [DecidableEq K]



/-! ### The reduction homomorphism and its behaviour on torsion -/

variable [E.IsElliptic] [CharZero K]















end Transport

end WeierstrassCurve.Affine

end

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenQuotientMod17. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The mod-seventeen point count for the `X₁(18)` elliptic quotient

The rational-coefficient model of the real-cubic quotient is

`y² + xy + y = x³ - x² + 25x + 1`.

This file records its integral model and verifies, by kernel reduction over
`ZMod 17`, that its good special fibre has exactly 21 points.  The result is
deliberately only a finite-field and integral-model certificate: using it to
specialize torsion over the real cubic coefficient field still requires a
prime of its ring of integers above seventeen and the corresponding formal
kernel theorem.
-/

open WeierstrassCurve

namespace MazurTorsion.XOneEighteenQuotientMod17

open WeierstrassCurve.Affine
  IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum
open MazurTorsion.XOneEighteenRealCubicQuotient

private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The integral rational-coefficient model `[1,-1,1,25,1]`. -/
def integralRationalModel : WeierstrassCurve ℤ :=
  ⟨1, -1, 1, 25, 1⟩

/-- Base change of the integral model is the rational-coefficient model over
the real cubic field. -/
theorem integralRationalModel_map_K :
    integralRationalModel.map (algebraMap ℤ K) = rationalModel := by
  ext <;> simp [integralRationalModel, rationalModel]

/-- The discriminant of the integral model is `-2 * 3^12`. -/
theorem integralRationalModel_discriminant :
    integralRationalModel.Δ = -1062882 := by
  norm_num [integralRationalModel, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]









/-- The concrete special fibre over `F₁₇`. -/
def rationalModelModSeventeen : WeierstrassCurve (ZMod 17) :=
  ⟨1, -1, 1, 25, 1⟩













/-- Concrete form of the same point-count certificate. -/
theorem card_rationalModelModSeventeen :
    Fintype.card rationalModelModSeventeen.toAffine.Point = 21 := by
  decide





end MazurTorsion.XOneEighteenQuotientMod17

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenQuotientReductionAtSeventeen. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Reduction of the `X₁(18)` elliptic quotient at a degree-one prime above seventeen

The coefficient cubic `X³ - 3X - 1` has the root `3` modulo `17`.  Kummer--Dedekind,
with the conductor certificate proved in
`XOneEighteenTwoDivisionSmallPrimes`, therefore constructs a genuine prime
of the full ring of integers of the coefficient field whose residue field
is `ZMod 17`.  At that prime the rational-coefficient quotient model has
good reduction and its special fibre has the already checked cardinality
`21`.

Reduction is injective when the source point group is finite: every source
point is then torsion, while the selected prime is unramified.  This gives
the unconditional cardinality divisor needed by
`XOneEighteenQuotientFiniteClassification` once finiteness has been supplied
by the two-descent.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenQuotientReductionAtSeventeen

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid
open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenQuotientFiniteClassification
open MazurTorsion.XOneEighteenQuotientMod17
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

private instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-! ## The degree-one prime above seventeen -/

/-- The integral lift of the factor corresponding to `τ ↦ 3`. -/
def coefficientLinearFactorInt : Polynomial ℤ := X - C 3

/-- The degree-one factor of the coefficient cubic modulo seventeen. -/
def coefficientLinearFactor : Polynomial (ZMod 17) := X - C 3

theorem coefficientLinearFactorInt_map :
    coefficientLinearFactorInt.map (Int.castRingHom (ZMod 17)) =
      coefficientLinearFactor := by
  simp only [coefficientLinearFactorInt, coefficientLinearFactor,
    Polynomial.map_sub, Polynomial.map_X]
  rw [Polynomial.map_C]
  norm_num

private theorem coefficient_not_dvd_exponent_seventeen :
    ¬ 17 ∣ RingOfIntegers.exponent coefficientInteger := by
  rw [RingOfIntegers.not_dvd_exponent_iff]
  have hspan : Ideal.span {(81 : ℤ)} ≤
      Ideal.comap (algebraMap ℤ (𝓞 K))
        (conductor ℤ coefficientInteger) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    exact coefficient_discriminant_mem_conductor
  exact ((Ideal.isCoprime_span_singleton_iff (81 : ℤ) 17).mpr
    (by norm_num)).codisjoint.mono_left hspan

theorem coefficientLinearFactor_mem_monicFactors :
    coefficientLinearFactor ∈
      RingOfIntegers.monicFactorsMod coefficientInteger 17 := by
  change coefficientLinearFactor ∈
    (normalizedFactors
      ((minpoly ℤ coefficientInteger).map
        (Int.castRingHom (ZMod 17)))).toFinset
  rw [Multiset.mem_toFinset, coefficientInteger_minpoly,
    coefficientPolynomialInt_map_zmod]
  apply (Polynomial.mem_normalizedFactors_iff (by
    have hmonic : (coefficientPolynomialMod 17).Monic := by
      simp only [coefficientPolynomialMod]
      monicity <;> norm_num
    exact hmonic.ne_zero)).2
  refine ⟨irreducible_X_sub_C 3, monic_X_sub_C 3, ?_⟩
  rw [coefficientLinearFactor, Polynomial.dvd_iff_isRoot]
  unfold Polynomial.IsRoot
  simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
    eval_mul, eval_ofNat, eval_one]
  decide

theorem coefficientLinearFactorInt_mem_monicFactors :
    coefficientLinearFactorInt.map (Int.castRingHom (ZMod 17)) ∈
      RingOfIntegers.monicFactorsMod coefficientInteger 17 := by
  rw [coefficientLinearFactorInt_map]
  exact coefficientLinearFactor_mem_monicFactors

/-- The Kummer--Dedekind prime selected by the root `τ ↦ 3`. -/
def coefficientPrimeSeventeenIdeal : Ideal (𝓞 K) :=
  (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      coefficient_not_dvd_exponent_seventeen).symm
    ⟨coefficientLinearFactorInt.map (Int.castRingHom (ZMod 17)),
      coefficientLinearFactorInt_mem_monicFactors⟩

theorem coefficientPrimeSeventeen_mem_primesOver :
    coefficientPrimeSeventeenIdeal ∈
      Ideal.primesOver (Ideal.span {(17 : ℤ)}) (𝓞 K) :=
  ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
      coefficient_not_dvd_exponent_seventeen).symm
    ⟨coefficientLinearFactorInt.map (Int.castRingHom (ZMod 17)),
      coefficientLinearFactorInt_mem_monicFactors⟩).property



private instance coefficientPrimeSeventeenIdeal_liesOver :
    coefficientPrimeSeventeenIdeal.LiesOver
      (Ideal.span {(17 : ℤ)}) :=
  coefficientPrimeSeventeen_mem_primesOver.2

/-- The resulting height-one prime of the coefficient-field integers. -/
def coefficientPrimeSeventeen : HeightOneSpectrum (𝓞 K) :=
  .ofPrime (Ideal.prime_of_mem_primesOver
    (by norm_num) coefficientPrimeSeventeen_mem_primesOver)

@[simp] theorem coefficientPrimeSeventeen_asIdeal :
    coefficientPrimeSeventeen.asIdeal = coefficientPrimeSeventeenIdeal :=
  rfl

theorem coefficientPrimeSeventeenIdeal_eq_span :
    coefficientPrimeSeventeenIdeal =
      Ideal.span {(17 : 𝓞 K),
        Polynomial.aeval coefficientInteger coefficientLinearFactorInt} := by
  exact NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span
    coefficient_not_dvd_exponent_seventeen
    coefficientLinearFactorInt_mem_monicFactors

/-! ## The residue field -/

/-- The residue field of the selected coefficient-field prime is `F₁₇`. -/
noncomputable def residueSeventeenRingEquiv :
    (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal) ≃+* ZMod 17 :=
  (Ideal.quotEquivOfEq coefficientPrimeSeventeen_asIdeal).trans <|
    (Ideal.quotEquivOfEq coefficientPrimeSeventeenIdeal_eq_span).trans <|
      (RingOfIntegers.ZModXQuotSpanEquivQuotSpanPair
          coefficient_not_dvd_exponent_seventeen
          coefficientLinearFactorInt_mem_monicFactors).symm.trans <|
        (Ideal.quotEquivOfEq (congrArg (fun f ↦ Ideal.span {f})
          coefficientLinearFactorInt_map)).trans <|
          (Polynomial.quotientSpanXSubCAlgEquiv
            (3 : ZMod 17)).toRingEquiv

/-- The residue equivalence, with its canonical integer-algebra structure. -/
noncomputable def residueSeventeenAlgEquiv :
    (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal) ≃ₐ[ℤ] ZMod 17 :=
  AlgEquiv.ofRingEquiv (f := residueSeventeenRingEquiv) fun z ↦ by
    exact map_intCast residueSeventeenRingEquiv z



noncomputable instance coefficientResidueSeventeen_decidableEq :
    DecidableEq (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal) :=
  residueSeventeenAlgEquiv.toEquiv.decidableEq

/-! ## Unramifiedness at the selected prime -/

private theorem coefficientPolynomialMod_seventeen_ne_zero :
    coefficientPolynomialMod 17 ≠ 0 := by
  have hmonic : (coefficientPolynomialMod 17).Monic := by
    simp only [coefficientPolynomialMod]
    monicity <;> norm_num
  exact hmonic.ne_zero

theorem coefficientLinearFactor_multiplicity :
    multiplicity coefficientLinearFactor (coefficientPolynomialMod 17) = 1 := by
  have hroot : Polynomial.IsRoot (coefficientPolynomialMod 17) (3 : ZMod 17) := by
    unfold Polynomial.IsRoot
    simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
      eval_mul, eval_ofNat, eval_one]
    decide
  have hderivative :
      ¬ Polynomial.IsRoot (derivative (coefficientPolynomialMod 17))
        (3 : ZMod 17) := by
    norm_num [Polynomial.IsRoot, coefficientPolynomialMod,
      derivative_sub, derivative_pow, derivative_X, derivative_mul,
      derivative_ofNat, derivative_one]
    decide
  have hpos :
      0 < (coefficientPolynomialMod 17).rootMultiplicity (3 : ZMod 17) :=
    (Polynomial.rootMultiplicity_pos coefficientPolynomialMod_seventeen_ne_zero).2 hroot
  have hle :
      (coefficientPolynomialMod 17).rootMultiplicity (3 : ZMod 17) ≤ 1 := by
    by_contra h
    have hgt : 1 <
        (coefficientPolynomialMod 17).rootMultiplicity (3 : ZMod 17) := by
      omega
    exact hderivative
      ((Polynomial.one_lt_rootMultiplicity_iff_isRoot
        coefficientPolynomialMod_seventeen_ne_zero).mp hgt).2
  have hrootMultiplicity :
      (coefficientPolynomialMod 17).rootMultiplicity (3 : ZMod 17) = 1 := by
    omega
  have hm := Polynomial.rootMultiplicity_eq_multiplicity
    (coefficientPolynomialMod 17) (3 : ZMod 17)
  rw [if_neg coefficientPolynomialMod_seventeen_ne_zero] at hm
  rw [coefficientLinearFactor]
  exact hm.symm.trans hrootMultiplicity

/-- The selected degree-one prime is unramified over seventeen. -/
theorem coefficientPrimeSeventeen_ramificationIdx :
    coefficientPrimeSeventeenIdeal.ramificationIdx ℤ = 1 := by
  rw [coefficientPrimeSeventeenIdeal]
  rw [NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'
    coefficient_not_dvd_exponent_seventeen
    coefficientLinearFactorInt_mem_monicFactors]
  rw [coefficientInteger_minpoly, coefficientPolynomialInt_map_zmod,
    coefficientLinearFactorInt_map]
  exact coefficientLinearFactor_multiplicity



/-! ## Integral model and good reduction -/

/-- The rational-coefficient integral model, base changed to the full ring
of integers of the coefficient cubic. -/
def integralRationalModelK : WeierstrassCurve (𝓞 K) :=
  integralRationalModel.map (algebraMap ℤ (𝓞 K))

/-- Its generic fibre is the rational-coefficient quotient model. -/
theorem integralRationalModelK_map_K :
    integralRationalModelK.map (algebraMap (𝓞 K) K) =
      rationalModel := by
  rw [integralRationalModelK, WeierstrassCurve.map_map,
    ← IsScalarTower.algebraMap_eq ℤ (𝓞 K) K]
  exact integralRationalModel_map_K

theorem integralRationalModelK_discriminant :
    integralRationalModelK.Δ = (-1062882 : 𝓞 K) := by
  rw [integralRationalModelK, WeierstrassCurve.map_Δ,
    integralRationalModel_discriminant]
  norm_num

/-- The chosen integral model has good reduction at the degree-one prime. -/
instance integralRationalModelK_red_isElliptic :
    (WeierstrassCurve.Affine.redCurve coefficientPrimeSeventeen
      integralRationalModelK).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  change
    (integralRationalModelK.map
      (algebraMap (𝓞 K)
        (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal))).Δ ≠ 0
  rw [WeierstrassCurve.map_Δ, integralRationalModelK_discriminant]
  rw [Ne, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem, coefficientPrimeSeventeen_asIdeal]
  intro hmem
  have hbase : (-1062882 : ℤ) ∈ Ideal.span {(17 : ℤ)} := by
    rw [coefficientPrimeSeventeenIdeal.over_def
      (Ideal.span {(17 : ℤ)})]
    change algebraMap ℤ (𝓞 K) (-1062882 : ℤ) ∈
      coefficientPrimeSeventeenIdeal
    simpa using hmem
  rw [Ideal.mem_span_singleton] at hbase
  norm_num at hbase



/-! ## Identification and cardinality of the special fibre -/

private theorem redCurve_eq_integerBaseChange :
    WeierstrassCurve.Affine.redCurve coefficientPrimeSeventeen
        integralRationalModelK =
      ((integralRationalModel.toAffine ⁄
          (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal)) :
        WeierstrassCurve _).toAffine := by
  change
    (integralRationalModel.map (algebraMap ℤ (𝓞 K))).map
        (algebraMap (𝓞 K)
          (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal)) =
      integralRationalModel.map
        (algebraMap ℤ
          (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal))
  rw [WeierstrassCurve.map_map,
    IsScalarTower.algebraMap_eq ℤ (𝓞 K)
      (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal)]

private theorem integerBaseChange_modSeventeen :
    ((integralRationalModel.toAffine ⁄ (ZMod 17)) :
      WeierstrassCurve _).toAffine =
        rationalModelModSeventeen.toAffine := by
  ext <;> decide +kernel

/-- The special fibre over the selected coefficient-field prime is the
concrete 21-point curve over `F₁₇`. -/
noncomputable def reducedPointEquiv :
    (WeierstrassCurve.Affine.redCurve coefficientPrimeSeventeen
        integralRationalModelK).Point ≃+
      rationalModelModSeventeen.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.congr redCurve_eq_integerBaseChange).trans <|
    (WeierstrassCurve.Affine.Point.mapEquiv
      (W' := integralRationalModel.toAffine)
      residueSeventeenAlgEquiv).trans <|
        WeierstrassCurve.Affine.Point.congr integerBaseChange_modSeventeen



/-- The special fibre at the selected degree-one prime has 21 points. -/
theorem card_reducedCurve_seventeen :
    Nat.card (WeierstrassCurve.Affine.redCurve coefficientPrimeSeventeen
      integralRationalModelK).Point = 21 := by
  calc
    Nat.card (WeierstrassCurve.Affine.redCurve coefficientPrimeSeventeen
        integralRationalModelK).Point =
        Fintype.card rationalModelModSeventeen.toAffine.Point :=
      (Nat.card_congr reducedPointEquiv.toEquiv).trans
        Nat.card_eq_fintype_card
    _ = 21 := card_rationalModelModSeventeen

/-! ## Injective reduction of a finite quotient point group -/











/-- The full torsion good-reduction bound gives the original finite quotient
cardinality divisor at the chosen unramified prime. -/
theorem quotient_point_card_dvd_twentyOne
    [Finite quotientCurve.toAffine.Point] :
    Nat.card quotientCurve.toAffine.Point ∣ 21 := by
  classical
  letI : Finite (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal) :=
    Finite.of_equiv (ZMod 17) residueSeventeenRingEquiv.symm.toEquiv
  letI : coefficientPrimeSeventeen.asIdeal.LiesOver (Ideal.span {(17 : ℤ)}) :=
    coefficientPrimeSeventeen_asIdeal.symm ▸ inferInstance
  have hv : coefficientPrimeSeventeen.valuation K (17 : K) = WithZero.exp (-1 : ℤ) := by
    have hh := MazurReduction.adic_valuation_of_ramification_one
      (K := K) coefficientPrimeSeventeen 17 (by norm_num)
      (by simpa only [coefficientPrimeSeventeen_asIdeal] using
        coefficientPrimeSeventeen_ramificationIdx)
    norm_num at hh
    exact hh
  letI : Finite rationalModel.toAffine.Point :=
    Finite.of_equiv quotientCurve.toAffine.Point
      MazurTorsion.XOneEighteenQuotientTwoDescentModel.quotientToRationalEquiv.toEquiv
  letI : (integralRationalModelK.map (algebraMap (𝓞 K) K)).IsElliptic :=
    integralRationalModelK_map_K.symm ▸ inferInstance
  letI : Finite (integralRationalModelK.map (algebraMap (𝓞 K) K)).toAffine.Point :=
    integralRationalModelK_map_K.symm ▸ inferInstance
  letI : (integralRationalModelK.map (algebraMap (𝓞 K)
      (𝓞 K ⧸ coefficientPrimeSeventeen.asIdeal))).IsElliptic := by
    change (WeierstrassCurve.Affine.redCurve coefficientPrimeSeventeen
      integralRationalModelK).IsElliptic
    infer_instance
  have hb := MazurTransfer.finite_dedekind_point_card_dvd
    (K := K) coefficientPrimeSeventeen 17 (by norm_num) hv integralRationalModelK
  change Nat.card (integralRationalModelK.map (algebraMap (𝓞 K) K)).toAffine.Point ∣
    Nat.card (WeierstrassCurve.Affine.redCurve coefficientPrimeSeventeen integralRationalModelK).Point at hb
  rw [integralRationalModelK_map_K, card_reducedCurve_seventeen] at hb
  rw [Nat.card_congr MazurTorsion.XOneEighteenQuotientTwoDescentModel.quotientToRationalEquiv.toEquiv]
  exact hb


/-- The genuine finite-reduction consumer: once the two-descent supplies
finiteness, the checked 21-point reduction and finite-group classification
exclude every noncuspidal rational point. -/
theorem no_noncuspidal_point_of_finite_quotient
    [Finite quotientCurve.toAffine.Point]
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve :
      y ^ 2 = MazurTorsion.Kubert.orderEighteenHyperellipticPolynomial x) :
    False :=
  no_noncuspidal_point_of_point_card_dvd_twentyOne
    quotient_point_card_dvd_twentyOne x y hx0 hx1 hcurve

end

end MazurTorsion.XOneEighteenQuotientReductionAtSeventeen

end

theorem solution [Finite MazurTorsion.XOneEighteenRealCubicQuotient.quotientCurve.toAffine.Point]
    (x y : ℚ) (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hcurve : y ^ 2 = x ^ 6 - 4 * x ^ 5 + 10 * x ^ 4 - 10 * x ^ 3 + 5 * x ^ 2 - 2 * x + 1) : False := by
  exact MazurTorsion.XOneEighteenQuotientReductionAtSeventeen.no_noncuspidal_point_of_finite_quotient
    x y hx0 hx1 hcurve
#print axioms solution
