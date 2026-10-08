-- Prove2me | solution 1 for MazurHuang.x0_seventeen_two_isogeny_model_points
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-07T17:39:10.234152+00:00
-- url     : https://prove2.me/submissions/0c9c3f39-a6ff-4fa8-992c-722757988261

import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff

set_option maxHeartbeats 1000000

universe u v

-- ===== FLT.PortCompat =====
section
/-! Compatibility shims for porting to the platform Mathlib pin. -/

/-- The former hypothesis-taking form of `padicValRat.pow`. -/
theorem padicValRat.pow_of_ne_zero {p : ℕ} [Fact p.Prime] {q : ℚ} (_hq : q ≠ 0) {k : ℕ} :
    padicValRat p (q ^ k) = k * padicValRat p q :=
  padicValRat.pow q

end

-- ===== FLT.Assumptions.MazurProof.N18RouteC_VariableChangePoints =====
section
/-!
# Point transport under a Weierstrass variable change

This is the field-generic point-level counterpart of Mathlib's curve-level
variable-change action.
-/

namespace MazurProof.N18RouteC.VariableChangePoints

noncomputable section

variable {F : Type*} [Field F] [DecidableEq F]

/-- The transformed `X`-coordinate under a Weierstrass variable change.  This is
the inverse coordinate map from old coordinates on `W` to new coordinates on
`C • W`.
-/
def variableChangePointX (C : WeierstrassCurve.VariableChange F) (x : F) : F :=
  (C.u⁻¹ : F) ^ 2 * (x - C.r)

/-- The transformed `Y`-coordinate under a Weierstrass variable change. -/
def variableChangePointY (C : WeierstrassCurve.VariableChange F) (x y : F) : F :=
  (C.u⁻¹ : F) ^ 3 * (y - C.s * (x - C.r) - C.t)

/-- The old `x`-coordinate recovered from new coordinates. -/
def variableChangePointInvX (C : WeierstrassCurve.VariableChange F) (X : F) : F :=
  (C.u : F) ^ 2 * X + C.r

/-- The old `y`-coordinate recovered from new coordinates. -/
def variableChangePointInvY (C : WeierstrassCurve.VariableChange F) (X Y : F) : F :=
  (C.u : F) ^ 3 * Y + (C.u : F) ^ 2 * C.s * X + C.t

lemma variableChangePoint_equation
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F) {x y : F}
    (h : WeierstrassCurve.Affine.Equation W x y) :
    WeierstrassCurve.Affine.Equation (C • W)
      (variableChangePointX C x) (variableChangePointY C x y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  unfold variableChangePointX variableChangePointY
  rw [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆]
  simp only [Units.val_inv_eq_inv_val]
  field_simp [C.u.ne_zero]
  linear_combination h

lemma variableChangePointInv_equation
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F) {X Y : F}
    (h : WeierstrassCurve.Affine.Equation (C • W) X Y) :
    WeierstrassCurve.Affine.Equation W
      (variableChangePointInvX C X) (variableChangePointInvY C X Y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  unfold variableChangePointInvX variableChangePointInvY
  rw [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆] at h
  simp only [Units.val_inv_eq_inv_val] at h
  field_simp [C.u.ne_zero] at h
  linear_combination h

lemma variableChangePointInvX_pointX
    (C : WeierstrassCurve.VariableChange F) (x : F) :
    variableChangePointInvX C (variableChangePointX C x) = x := by
  simp [variableChangePointInvX, variableChangePointX]

lemma variableChangePointInvY_pointY
    (C : WeierstrassCurve.VariableChange F) (x y : F) :
    variableChangePointInvY C (variableChangePointX C x) (variableChangePointY C x y) = y := by
  simp [variableChangePointInvY, variableChangePointX, variableChangePointY]
  field_simp [C.u.ne_zero]
  ring

lemma variableChangePointX_invX
    (C : WeierstrassCurve.VariableChange F) (X : F) :
    variableChangePointX C (variableChangePointInvX C X) = X := by
  simp [variableChangePointInvX, variableChangePointX]

lemma variableChangePointY_invY
    (C : WeierstrassCurve.VariableChange F) (X Y : F) :
    variableChangePointY C (variableChangePointInvX C X)
      (variableChangePointInvY C X Y) = Y := by
  simp [variableChangePointInvX, variableChangePointInvY, variableChangePointY]
  field_simp [C.u.ne_zero]
  ring

lemma variableChangePointX_eq_iff
    (C : WeierstrassCurve.VariableChange F) {x₁ x₂ : F} :
    variableChangePointX C x₁ = variableChangePointX C x₂ ↔ x₁ = x₂ := by
  unfold variableChangePointX
  constructor
  · intro h
    field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero] at h
    linear_combination h
  · intro h
    simp [h]

lemma variableChangePointY_eq_iff
    (C : WeierstrassCurve.VariableChange F) (x : F) {y₁ y₂ : F} :
    variableChangePointY C x y₁ = variableChangePointY C x y₂ ↔ y₁ = y₂ := by
  unfold variableChangePointY
  constructor
  · intro h
    field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero] at h
    linear_combination h
  · intro h
    simp [h]

lemma variableChangePointY_negY
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F) (x y : F) :
    variableChangePointY C x (WeierstrassCurve.Affine.negY W x y) =
      WeierstrassCurve.Affine.negY (C • W)
        (variableChangePointX C x) (variableChangePointY C x y) := by
  simp [variableChangePointX, variableChangePointY, WeierstrassCurve.Affine.negY,
    WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₃]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  ring

lemma variableChange_slope_of_X_ne
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    {x₁ x₂ y₁ y₂ : F} (hx : x₁ ≠ x₂) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂) =
      (C.u⁻¹ : F) *
        (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂ - C.s) := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  rw [WeierstrassCurve.Affine.slope_of_X_ne]
  · unfold variableChangePointX variableChangePointY
    field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero, sub_ne_zero.mpr hx]
    ring
  · exact fun h => hx ((variableChangePointX_eq_iff C).mp h)

lemma variableChange_slope_of_Y_ne
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    {x₁ x₂ y₁ y₂ : F}
    (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂)
    (hx : x₁ = x₂) (hy : y₁ ≠ WeierstrassCurve.Affine.negY W x₂ y₂) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂) =
      (C.u⁻¹ : F) *
        (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂ - C.s) := by
  have hy_eq : y₁ = y₂ := WeierstrassCurve.Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
  have hy_self : y₁ ≠ WeierstrassCurve.Affine.negY W x₁ y₁ := by
    intro h
    apply hy
    rw [← hx, ← hy_eq]
    exact h
  have hden : x₁ * W.a₁ + W.a₃ + y₁ * 2 ≠ 0 := by
    intro hden
    apply hy_self
    rw [WeierstrassCurve.Affine.negY]
    linear_combination hden
  have hmul :
      (x₁ * W.a₁ + W.a₃ + y₁ * 2) *
          (x₁ * W.a₁ + W.a₃ + y₁ * 2)⁻¹ = 1 :=
    mul_inv_cancel₀ hden
  have htarget_hx :
      variableChangePointX C x₁ = variableChangePointX C x₂ := by
    simp [hx]
  have htarget_hy :
      variableChangePointY C x₁ y₁ ≠
        WeierstrassCurve.Affine.negY (C • W)
          (variableChangePointX C x₂) (variableChangePointY C x₂ y₂) := by
    intro h
    apply hy
    rw [← hx]
    apply (variableChangePointY_eq_iff C x₁).mp
    rw [h]
    rw [hx, variableChangePointY_negY]
  rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hy]
  rw [WeierstrassCurve.Affine.slope_of_Y_ne htarget_hx htarget_hy]
  unfold variableChangePointX variableChangePointY
  simp [WeierstrassCurve.Affine.negY, WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃,
    WeierstrassCurve.variableChange_a₄]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  rw [← sub_eq_zero]
  ring_nf
  convert
    (show C.s *
        (1 - (x₁ * W.a₁ + W.a₃ + y₁ * 2) *
          (x₁ * W.a₁ + W.a₃ + y₁ * 2)⁻¹) = 0 by
      rw [hmul]
      ring) using 1
  ring

lemma variableChange_slope
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    {x₁ x₂ y₁ y₂ : F}
    (h₁ : WeierstrassCurve.Affine.Equation W x₁ y₁)
    (h₂ : WeierstrassCurve.Affine.Equation W x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂)) :
    WeierstrassCurve.Affine.slope (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂) =
      (C.u⁻¹ : F) *
        (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂ - C.s) := by
  by_cases hx : x₁ = x₂
  · exact variableChange_slope_of_Y_ne W C h₁ h₂ hx (fun hy => hxy ⟨hx, hy⟩)
  · exact variableChange_slope_of_X_ne W C hx

lemma variableChange_nonvertical
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    {x₁ x₂ y₁ y₂ : F}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂)) :
    ¬(variableChangePointX C x₁ = variableChangePointX C x₂ ∧
      variableChangePointY C x₁ y₁ =
        WeierstrassCurve.Affine.negY (C • W)
          (variableChangePointX C x₂) (variableChangePointY C x₂ y₂)) := by
  rintro ⟨hx', hy'⟩
  apply hxy
  have hx : x₁ = x₂ := (variableChangePointX_eq_iff C).mp hx'
  refine ⟨hx, ?_⟩
  rw [← hx]
  apply (variableChangePointY_eq_iff C x₁).mp
  rw [hy', hx, ← variableChangePointY_negY]

lemma variableChange_vertical
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    {x₁ x₂ y₁ y₂ : F}
    (hxy : x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂) :
    variableChangePointX C x₁ = variableChangePointX C x₂ ∧
      variableChangePointY C x₁ y₁ =
        WeierstrassCurve.Affine.negY (C • W)
          (variableChangePointX C x₂) (variableChangePointY C x₂ y₂) := by
  rcases hxy with ⟨hx, hy⟩
  constructor
  · simp [hx]
  · rw [hy, ← variableChangePointY_negY, hx]

lemma variableChange_addX
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    (x₁ x₂ ℓ : F) :
    variableChangePointX C (WeierstrassCurve.Affine.addX W x₁ x₂ ℓ) =
      WeierstrassCurve.Affine.addX (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        ((C.u⁻¹ : F) * (ℓ - C.s)) := by
  simp [variableChangePointX, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  ring

lemma variableChange_addY
    (W : WeierstrassCurve F) (C : WeierstrassCurve.VariableChange F)
    (x₁ x₂ y₁ ℓ : F) :
    variableChangePointY C (WeierstrassCurve.Affine.addX W x₁ x₂ ℓ)
        (WeierstrassCurve.Affine.addY W x₁ x₂ y₁ ℓ) =
      WeierstrassCurve.Affine.addY (C • W)
        (variableChangePointX C x₁) (variableChangePointX C x₂)
        (variableChangePointY C x₁ y₁) ((C.u⁻¹ : F) * (ℓ - C.s)) := by
  simp [variableChangePointX, variableChangePointY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.variableChange_a₁,
    WeierstrassCurve.variableChange_a₂, WeierstrassCurve.variableChange_a₃]
  field_simp [Units.val_inv_eq_inv_val, C.u.ne_zero]
  ring

noncomputable def variableChangePointMap
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    WeierstrassCurve.Affine.Point W → WeierstrassCurve.Affine.Point (C • W)
  | WeierstrassCurve.Affine.Point.zero => 0
  | WeierstrassCurve.Affine.Point.some x y h =>
      WeierstrassCurve.Affine.Point.some
        (variableChangePointX C x) (variableChangePointY C x y)
        (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          (variableChangePoint_equation W C h.left))

noncomputable def variableChangePointMapInv
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    WeierstrassCurve.Affine.Point (C • W) → WeierstrassCurve.Affine.Point W
  | WeierstrassCurve.Affine.Point.zero => 0
  | WeierstrassCurve.Affine.Point.some X Y h =>
      WeierstrassCurve.Affine.Point.some
        (variableChangePointInvX C X) (variableChangePointInvY C X Y)
        (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          (variableChangePointInv_equation W C h.left))

@[simp] lemma variableChangePointMap_zero
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    variableChangePointMap W C 0 = 0 :=
  rfl

lemma variableChangePointMap_leftInverse
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    Function.LeftInverse (variableChangePointMapInv W C) (variableChangePointMap W C) := by
  intro P
  cases P with
  | zero => rfl
  | some x y h =>
      simp [variableChangePointMap, variableChangePointMapInv,
        variableChangePointInvX_pointX, variableChangePointInvY_pointY]

lemma variableChangePointMap_rightInverse
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    Function.RightInverse (variableChangePointMapInv W C) (variableChangePointMap W C) := by
  intro P
  cases P with
  | zero => rfl
  | some X Y h =>
      simp [variableChangePointMap, variableChangePointMapInv,
        variableChangePointX_invX, variableChangePointY_invY]

noncomputable def variableChangePointEquiv
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    WeierstrassCurve.Affine.Point W ≃ WeierstrassCurve.Affine.Point (C • W) where
  toFun := variableChangePointMap W C
  invFun := variableChangePointMapInv W C
  left_inv := variableChangePointMap_leftInverse W C
  right_inv := variableChangePointMap_rightInverse W C

lemma variableChangePointMap_add
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F)
    (P Q : WeierstrassCurve.Affine.Point W) :
    variableChangePointMap W C (P + Q) =
      variableChangePointMap W C P + variableChangePointMap W C Q := by
  cases P with
  | zero => rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => rfl
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = WeierstrassCurve.Affine.negY W x₂ y₂
      · have htarget := variableChange_vertical W C hxy
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.left hxy.right]
        simp only [variableChangePointMap]
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq htarget.left htarget.right]
      · have htarget := variableChange_nonvertical W C hxy
        have hslope := variableChange_slope W C h₁.left h₂.left hxy
        rw [WeierstrassCurve.Affine.Point.add_some hxy]
        simp only [variableChangePointMap]
        rw [WeierstrassCurve.Affine.Point.add_some htarget]
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        constructor
        · change
            variableChangePointX C
                (WeierstrassCurve.Affine.addX W x₁ x₂
                  (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)) =
              WeierstrassCurve.Affine.addX (C • W)
                (variableChangePointX C x₁) (variableChangePointX C x₂)
                (WeierstrassCurve.Affine.slope (C • W)
                  (variableChangePointX C x₁) (variableChangePointX C x₂)
                  (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂))
          rw [hslope]
          exact variableChange_addX W C x₁ x₂
            (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)
        · change
            variableChangePointY C
                (WeierstrassCurve.Affine.addX W x₁ x₂
                  (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂))
                (WeierstrassCurve.Affine.addY W x₁ x₂ y₁
                  (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)) =
              WeierstrassCurve.Affine.addY (C • W)
                (variableChangePointX C x₁) (variableChangePointX C x₂)
                (variableChangePointY C x₁ y₁)
                (WeierstrassCurve.Affine.slope (C • W)
                  (variableChangePointX C x₁) (variableChangePointX C x₂)
                  (variableChangePointY C x₁ y₁) (variableChangePointY C x₂ y₂))
          rw [hslope]
          exact variableChange_addY W C x₁ x₂ y₁
            (WeierstrassCurve.Affine.slope W x₁ x₂ y₁ y₂)

noncomputable def variableChangePointAddEquiv
    (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) :
    WeierstrassCurve.Affine.Point W ≃+ WeierstrassCurve.Affine.Point (C • W) :=
  AddEquiv.mk (variableChangePointEquiv W C) (variableChangePointMap_add W C)

end

end MazurProof.N18RouteC.VariableChangePoints

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

@[reducible] def veluQuotCurve (A B r : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0; a₂ := 0; a₃ := 0
  a₄ := A - 5 * veluT A r
  a₆ := B - 7 * r * veluT A r

/-! ## Equation lemmas -/

lemma shortWS_equation {A B x y : ℚ} :
    Equation (shortWS A B) x y ↔ y ^ 2 = x ^ 3 + A * x + B := by
  simp only [equation_iff, shortWS]; constructor <;> intro h <;> linarith

lemma veluQuotCurve_equation {A B r x y : ℚ} :
    Equation (veluQuotCurve A B r) x y ↔
    y ^ 2 = x ^ 3 + (A - 5 * veluT A r) * x + (B - 7 * r * veluT A r) := by
  simp only [equation_iff, veluQuotCurve]; constructor <;> intro h <;> linarith

/-! ## Well-definedness -/

lemma velu_equation {A B r x y : ℚ}
    (hcurve : Equation (shortWS A B) x y)
    (htors : r ^ 3 + A * r + B = 0)
    (hx : x ≠ r) :
    Equation (veluQuotCurve A B r)
      (x + veluT A r / (x - r))
      (y * ((x - r) ^ 2 - veluT A r) / (x - r) ^ 2) := by
  rw [veluQuotCurve_equation]
  have hcurve' := shortWS_equation.mp hcurve
  have hd : x - r ≠ 0 := sub_ne_zero.mpr hx
  unfold veluT
  field_simp
  linear_combination
    (A ^ 2 + 4 * A * r ^ 2 + 4 * A * r * x - 2 * A * x ^ 2 +
     4 * r ^ 4 + 8 * r ^ 3 * x - 4 * r * x ^ 3 + x ^ 4) * hcurve' +
    (A ^ 2 + 4 * A * r ^ 2 + 4 * A * r * x - 2 * A * x ^ 2 +
     3 * r ^ 4 + 12 * r ^ 3 * x - 6 * r ^ 2 * x ^ 2) * htors

/-! ## IsElliptic instances -/

lemma shortWS_Δ (A B : ℚ) :
    (shortWS A B).Δ = -16 * (4 * A ^ 3 + 27 * B ^ 2) := by
  simp [shortWS, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma shortWS_Δ_factor {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    (shortWS A B).Δ = -16 * (A + 3 * r ^ 2) ^ 2 * (4 * A + 3 * r ^ 2) := by
  rw [shortWS_Δ]
  have hB : B = -r ^ 3 - A * r := by linarith
  rw [hB]; ring

lemma veluQuotCurve_Δ_factor {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    (veluQuotCurve A B r).Δ = 256 * (A + 3 * r ^ 2) * (4 * A + 3 * r ^ 2) ^ 2 := by
  simp only [veluQuotCurve, veluT, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  have hB : B = -r ^ 3 - A * r := by linarith
  rw [hB]; ring

lemma veluQuotCurve_isElliptic {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    (hE : (shortWS A B).IsElliptic) :
    (veluQuotCurve A B r).IsElliptic := by
  have hΔ := hE.isUnit
  rw [shortWS_Δ_factor htors] at hΔ
  have hne := isUnit_iff_ne_zero.mp hΔ
  have h1 : A + 3 * r ^ 2 ≠ 0 := by intro h; apply hne; simp [h]
  have h2 : 4 * A + 3 * r ^ 2 ≠ 0 := by intro h; apply hne; simp [h]
  constructor
  rw [veluQuotCurve_Δ_factor htors]
  exact (mul_ne_zero (mul_ne_zero (by norm_num : (256 : ℚ) ≠ 0) h1)
    (pow_ne_zero 2 h2)).isUnit

/-! ## The Vélu point map -/

def veluMapPoint {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Point (shortWS A B) → Point (veluQuotCurve A B r)
  | .zero => .zero
  | .some x y h =>
    if hx : x = r then .zero
    else
      .some (x + veluT A r / (x - r))
        (y * ((x - r) ^ 2 - veluT A r) / (x - r) ^ 2)
        (equation_iff_nonsingular.mp (velu_equation h.left htors hx))

@[simp] lemma veluMapPoint_zero {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    veluMapPoint htors (0 : Point (shortWS A B)) = 0 := rfl

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

def fx (x y : ℚ) : ℚ := y ^ 2 / x ^ 2
def fy (b x y : ℚ) : ℚ := y * (b - x ^ 2) / x ^ 2
def dx (x y : ℚ) : ℚ := y ^ 2 / x ^ 2 / 4
def dy (a b x y : ℚ) : ℚ := y * ((a ^ 2 - 4 * b) - x ^ 2) / x ^ 2 / 8

lemma forward_equation {a b x y : ℚ}
    (h : Equation (curve a b) x y) (hx : x ≠ 0) :
    Equation (curve (-2 * a) (a ^ 2 - 4 * b))
      (fx x y) (fy b x y) := by
  rw [curve_equation]
  have heq := curve_equation.mp h
  unfold fx fy
  field_simp [hx]
  rw [heq]
  ring

lemma dual_equation {a b x y : ℚ}
    (h : Equation (curve (-2 * a) (a ^ 2 - 4 * b)) x y) (hx : x ≠ 0) :
    Equation (curve a b) (dx x y) (dy a b x y) := by
  rw [curve_equation]
  have heq := curve_equation.mp h
  unfold dx dy
  field_simp [hx]
  rw [heq]
  ring

def tangent (a b x y : ℚ) : ℚ := (3 * x ^ 2 + 2 * a * x + b) / (2 * y)
def tx (a x m : ℚ) : ℚ := m ^ 2 - a - 2 * x
def ty (a x y m : ℚ) : ℚ := -(m * (tx a x m - x) + y)

lemma dual_forward_x {a b x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y ^ 2 = x * (x ^ 2 + a * x + b)) :
    dx (fx x y) (fy b x y) = tx a x (tangent a b x y) := by
  unfold dx fx fy tx tangent
  field_simp [hx, hy]
  rw [h]
  ring

lemma dual_forward_y {a b x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y ^ 2 = x * (x ^ 2 + a * x + b)) :
    dy a b (fx x y) (fy b x y) = ty a x y (tangent a b x y) := by
  unfold dy fx fy ty tx tangent
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x * (x ^ 2 + a * x + b)) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = _ := by rw [h]
  rw [hy4, h]
  ring

lemma forward_dual_x {a b x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y ^ 2 = x * (x ^ 2 + (-2 * a) * x + (a ^ 2 - 4 * b))) :
    fx (dx x y) (dy a b x y) =
      tx (-2 * a) x (tangent (-2 * a) (a ^ 2 - 4 * b) x y) := by
  unfold fx dx dy tx tangent
  field_simp [hx, hy]
  rw [h]
  ring

lemma forward_dual_y {a b x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : y ^ 2 = x * (x ^ 2 + (-2 * a) * x + (a ^ 2 - 4 * b))) :
    fy b (dx x y) (dy a b x y) =
      ty (-2 * a) x y (tangent (-2 * a) (a ^ 2 - 4 * b) x y) := by
  unfold fy dx dy ty tx tangent
  field_simp [hx, hy]
  have hy4 :
      y ^ 4 = (x * (x ^ 2 + (-2 * a) * x + (a ^ 2 - 4 * b))) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = _ := by rw [h]
  rw [hy4, h]
  ring

noncomputable def pointMap {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic] :
    Point (curve a b) → Point (curve (-2 * a) (a ^ 2 - 4 * b))
  | .zero => .zero
  | .some x y h =>
      if hx : x = 0 then .zero
      else .some (fx x y) (fy b x y)
        (equation_iff_nonsingular.mp (forward_equation h.left hx))

noncomputable def dualPoint {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic] :
    Point (curve (-2 * a) (a ^ 2 - 4 * b)) → Point (curve a b)
  | .zero => .zero
  | .some x y h =>
      if hx : x = 0 then .zero
      else .some (dx x y) (dy a b x y)
        (equation_iff_nonsingular.mp (dual_equation h.left hx))

@[simp] lemma pointMap_zero {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic] :
    pointMap (a := a) (b := b) 0 = 0 := rfl

@[simp] lemma dualPoint_zero {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic] :
    dualPoint (a := a) (b := b) 0 = 0 := rfl

lemma pointMap_some {a b x y : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h : Nonsingular (curve a b) x y) (hx : x ≠ 0) :
    pointMap (a := a) (b := b) (.some x y h) =
      .some (fx x y) (fy b x y)
        (equation_iff_nonsingular.mp (forward_equation h.left hx)) := by
  simp [pointMap, hx]

lemma dualPoint_some {a b x y : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h : Nonsingular (curve (-2 * a) (a ^ 2 - 4 * b)) x y) (hx : x ≠ 0) :
    dualPoint (a := a) (b := b) (.some x y h) =
      .some (dx x y) (dy a b x y)
        (equation_iff_nonsingular.mp (dual_equation h.left hx)) := by
  simp [dualPoint, hx]

@[simp] lemma curve_negY (a b x y : ℚ) :
    negY (curve a b) x y = -y := by
  simp [negY, curve]

lemma y_zero_of_x_zero {a b x y : ℚ}
    (h : Nonsingular (curve a b) x y) (hx : x = 0) : y = 0 := by
  have heq := curve_equation.mp h.left
  rw [hx] at heq
  nlinarith

lemma double_eq_zero_of_y_zero {a b x y : ℚ}
    [hE : (curve a b).IsElliptic]
    (h : Nonsingular (curve a b) x y) (hy : y = 0) :
    2 • (Point.some x y h : Point (curve a b)) = 0 := by
  rw [two_nsmul]
  exact Point.add_self_of_Y_eq (by simp [hy, curve_negY])

lemma y_ne_negY {a b x y : ℚ} (hy : y ≠ 0) :
    y ≠ negY (curve a b) x y := by
  rw [curve_negY]
  intro h
  exact hy (by linarith)

lemma slope_self {a b x y : ℚ} (hy : y ≠ 0) :
    slope (curve a b) x x y y = tangent a b x y := by
  rw [slope_of_Y_ne rfl (y_ne_negY hy)]
  simp [curve, tangent, negY]
  ring

lemma addX_self (a b x y : ℚ) :
    addX (curve a b) x x (tangent a b x y) =
      tx a x (tangent a b x y) := by
  simp [curve, addX, tx]
  ring

lemma addY_self (a b x y : ℚ) :
    addY (curve a b) x x y (tangent a b x y) =
      ty a x y (tangent a b x y) := by
  simp only [curve, addY, WeierstrassCurve.Affine.negAddY, negY, addX, ty, tx,
    zero_mul, add_zero, sub_zero]
  ring

/-! ### Dual composition and doubling -/

lemma dual_comp_pointMap {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    dualPoint (a := a) (b := b) (pointMap P) = 2 • P := by
  cases P with
  | zero => rfl
  | some x y h =>
      by_cases hx : x = 0
      · have hy := y_zero_of_x_zero h hx
        have hmap : pointMap (a := a) (b := b) (Point.some x y h) = 0 := by
          show pointMap (a := a) (b := b) (Point.some x y h) = Point.zero
          unfold pointMap
          exact dif_pos hx
        rw [hmap, dualPoint_zero]
        exact (double_eq_zero_of_y_zero h hy).symm
      · rw [pointMap_some h hx]
        by_cases hy : y = 0
        · have hfx : fx x y = 0 := by simp [fx, hy]
          simp only [dualPoint, hfx, dite_true]
          exact (double_eq_zero_of_y_zero h hy).symm
        · have hfx : fx x y ≠ 0 :=
            div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx)
          rw [dualPoint_some _ hfx, two_nsmul,
            Point.add_self_of_Y_ne (y_ne_negY hy)]
          rw [Point.some.injEq]
          have heq := curve_equation.mp h.left
          exact ⟨by
            rw [dual_forward_x hx hy heq, slope_self hy, addX_self],
            by rw [dual_forward_y hx hy heq, slope_self hy, addY_self]⟩

lemma pointMap_comp_dual {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve (-2 * a) (a ^ 2 - 4 * b))) :
    pointMap (a := a) (b := b) (dualPoint P) = 2 • P := by
  cases P with
  | zero => rfl
  | some x y h =>
      by_cases hx : x = 0
      · have hy := y_zero_of_x_zero h hx
        have hmap : dualPoint (a := a) (b := b) (Point.some x y h) = 0 := by
          show dualPoint (a := a) (b := b) (Point.some x y h) = Point.zero
          unfold dualPoint
          exact dif_pos hx
        rw [hmap, pointMap_zero]
        exact (double_eq_zero_of_y_zero h hy).symm
      · rw [dualPoint_some h hx]
        by_cases hy : y = 0
        · have hdx : dx x y = 0 := by simp [dx, hy]
          simp only [pointMap, hdx, dite_true]
          exact (double_eq_zero_of_y_zero h hy).symm
        · have hdx : dx x y ≠ 0 :=
            div_ne_zero
              (div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx))
              (by norm_num)
          rw [pointMap_some _ hdx, two_nsmul,
            Point.add_self_of_Y_ne (y_ne_negY hy)]
          rw [Point.some.injEq]
          have heq := curve_equation.mp h.left
          exact ⟨by
            rw [forward_dual_x hx hy heq, slope_self hy, addX_self],
            by rw [forward_dual_y hx hy heq, slope_self hy, addY_self]⟩

lemma pointMap_add_self {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (P + P) = pointMap P + pointMap P := by
  rw [← two_nsmul]
  calc
    pointMap (2 • P) = pointMap (dualPoint (pointMap P)) := by
      rw [dual_comp_pointMap]
    _ = 2 • pointMap P := pointMap_comp_dual _

/-! ### Kernel translations and fibres -/

def kernelPoint (a b : ℚ) [hE : (curve a b).IsElliptic] :
    Point (curve a b) :=
  .some 0 0 (equation_iff_nonsingular.mp (curve_equation.mpr (by ring)))

lemma b_ne_zero (a b : ℚ) [hE : (curve a b).IsElliptic] : b ≠ 0 := by
  have hns : Nonsingular (curve a b) 0 0 :=
    equation_iff_nonsingular.mp (curve_equation.mpr (by ring))
  have h := (nonsingular_zero (W := curve a b)).mp hns
  simpa [curve] using h.2

@[simp] lemma pointMap_kernel {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic] :
    pointMap (kernelPoint a b) = 0 := by
  show pointMap (a := a) (b := b) (kernelPoint a b) = Point.zero
  unfold pointMap kernelPoint
  exact dif_pos rfl

lemma kernel_add_self {a b : ℚ} [hE : (curve a b).IsElliptic] :
    kernelPoint a b + kernelPoint a b = 0 := by
  exact Point.add_self_of_Y_eq (by simp [kernelPoint, curve_negY])

lemma pointMap_neg {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (-P) = -pointMap P := by
  cases P with
  | zero => rfl
  | some x y h =>
      simp only [Point.neg_some, pointMap]
      by_cases hx : x = 0
      · simp only [hx, dite_true]
        rfl
      · simp only [hx, dite_false]
        rw [Point.neg_some]
        congr 1
        · simp [curve_negY, fx]
        · simp only [curve_negY, fy]
          ring

lemma slope_kernel {a b x y : ℚ} (hx : x ≠ 0) :
    slope (curve a b) x 0 y 0 = y / x := by
  rw [slope_of_X_ne hx]
  ring

lemma add_kernel_x {a b x y : ℚ}
    (h : Nonsingular (curve a b) x y) (hx : x ≠ 0) :
    addX (curve a b) x 0 (slope (curve a b) x 0 y 0) = b / x := by
  rw [slope_kernel hx]
  have heq := curve_equation.mp h.left
  simp only [addX, curve, zero_mul, add_zero, sub_zero]
  field_simp [hx]
  linear_combination heq

lemma add_kernel_y {a b x y : ℚ}
    (h : Nonsingular (curve a b) x y) (hx : x ≠ 0) :
    addY (curve a b) x 0 y (slope (curve a b) x 0 y 0) =
      -(b * y / x ^ 2) := by
  rw [slope_kernel hx]
  have hX : addX (curve a b) x 0 (y / x) = b / x := by
    rw [← slope_kernel hx]
    exact add_kernel_x h hx
  simp only [addY, WeierstrassCurve.Affine.negAddY, curve_negY]
  rw [hX]
  field_simp [hx]
  ring

lemma translation_coordinates {b x y : ℚ}
    (hx : x ≠ 0) (hb : b ≠ 0) :
    fx (b / x) (-(b * y / x ^ 2)) = fx x y ∧
      fy b (b / x) (-(b * y / x ^ 2)) = fy b x y := by
  constructor
  · unfold fx
    field_simp [hx, hb]
  · unfold fy
    field_simp [hx, hb]
    ring

lemma pointMap_add_kernel {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (P + kernelPoint a b) = pointMap P := by
  cases P with
  | zero =>
      change pointMap (kernelPoint a b) = pointMap 0
      rw [pointMap_kernel, pointMap_zero]
  | some x y h =>
      by_cases hx : x = 0
      · have hy := y_zero_of_x_zero h hx
        have hP : (Point.some x y h : Point (curve a b)) = kernelPoint a b := by
          unfold kernelPoint
          rw [Point.some.injEq]
          exact ⟨hx, hy⟩
        rw [hP, kernel_add_self, pointMap_zero, pointMap_kernel]
      · rw [show kernelPoint a b =
            Point.some 0 0 (equation_iff_nonsingular.mp
              (curve_equation.mpr (by ring))) by rfl]
        rw [Point.add_of_X_ne hx]
        have hb := b_ne_zero a b
        have hax : addX (curve a b) x 0 (slope (curve a b) x 0 y 0) ≠ 0 := by
          rw [add_kernel_x h hx]
          exact div_ne_zero hb hx
        rw [pointMap_some _ hax, pointMap_some h hx, Point.some.injEq]
        rw [add_kernel_x h hx, add_kernel_y h hx]
        exact translation_coordinates hx hb

lemma pointMap_kernel_add {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (kernelPoint a b + P) = pointMap P := by
  rw [add_comm, pointMap_add_kernel]

lemma pointMap_eq_zero_iff {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap P = 0 ↔ P = 0 ∨ P = kernelPoint a b := by
  constructor
  · intro hmap
    cases P with
    | zero => exact Or.inl rfl
    | some x y h =>
        by_cases hx : x = 0
        · right
          unfold kernelPoint
          rw [Point.some.injEq]
          exact ⟨hx, y_zero_of_x_zero h hx⟩
        · rw [pointMap_some h hx] at hmap
          exact (Point.some_ne_zero _ hmap).elim
  · rintro (rfl | rfl)
    · exact pointMap_zero
    · exact pointMap_kernel

lemma fx_secant_form {a b x y : ℚ}
    (h : y ^ 2 = x * (x ^ 2 + a * x + b)) (hx : x ≠ 0) :
    fx x y = x + a + b / x := by
  unfold fx
  rw [h]
  field_simp [hx]

lemma x_fibre_factor {a b x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : y₁ ^ 2 = x₁ * (x₁ ^ 2 + a * x₁ + b))
    (h₂ : y₂ ^ 2 = x₂ * (x₂ ^ 2 + a * x₂ + b))
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hfx : fx x₁ y₁ = fx x₂ y₂) :
    x₁ = x₂ ∨ x₁ * x₂ = b := by
  rw [fx_secant_form h₁ hx₁, fx_secant_form h₂ hx₂] at hfx
  have hprod : (x₁ - x₂) * (x₁ * x₂ - b) = 0 := by
    field_simp [hx₁, hx₂] at hfx
    linear_combination hfx
  rcases mul_eq_zero.mp hprod with h | h
  · left
    linarith
  · right
    linarith

lemma affine_fibre {a b x₁ y₁ x₂ y₂ : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h₁ : Nonsingular (curve a b) x₁ y₁)
    (h₂ : Nonsingular (curve a b) x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hmap : pointMap (a := a) (b := b) (Point.some x₁ y₁ h₁) =
      pointMap (a := a) (b := b) (Point.some x₂ y₂ h₂)) :
    (Point.some x₂ y₂ h₂ : Point (curve a b)) = Point.some x₁ y₁ h₁ ∨
      (Point.some x₂ y₂ h₂ : Point (curve a b)) =
        Point.some x₁ y₁ h₁ + kernelPoint a b := by
  rw [pointMap_some h₁ hx₁, pointMap_some h₂ hx₂] at hmap
  have hcoords := Point.some.inj hmap
  have heq₁ := curve_equation.mp h₁.left
  have heq₂ := curve_equation.mp h₂.left
  have hxf := x_fibre_factor heq₁ heq₂ hx₁ hx₂ hcoords.1
  have sameX (hxeq : x₁ = x₂) :
      (Point.some x₂ y₂ h₂ : Point (curve a b)) = Point.some x₁ y₁ h₁ ∨
        (Point.some x₂ y₂ h₂ : Point (curve a b)) =
          Point.some x₁ y₁ h₁ + kernelPoint a b := by
    rcases Y_eq_of_X_eq h₁.left h₂.left hxeq with hyeq | hyneg
    · left
      rw [Point.some.injEq]
      exact ⟨hxeq.symm, hyeq.symm⟩
    · have hy₂ : y₂ = -y₁ := by
        rw [curve_negY] at hyneg
        linarith
      by_cases hy₁ : y₁ = 0
      · left
        rw [Point.some.injEq]
        exact ⟨hxeq.symm, by linarith⟩
      · have hY := hcoords.2
        rw [← hxeq] at hY
        unfold fy at hY
        field_simp [hx₁] at hY
        rw [hy₂] at hY
        have hprod : y₁ * (b - x₁ ^ 2) = 0 := by
          linear_combination (1 / 2 : ℚ) * hY
        have hsquare : x₁ ^ 2 = b := by
          have := (mul_eq_zero.mp hprod).resolve_left hy₁
          linarith
        right
        change Point.some x₂ y₂ h₂ =
          (Point.some x₁ y₁ h₁ : Point (curve a b)) +
            Point.some 0 0 _
        rw [Point.add_of_X_ne hx₁, Point.some.injEq]
        constructor
        · rw [add_kernel_x h₁ hx₁, ← hxeq]
          field_simp [hx₁]
          nlinarith
        · rw [add_kernel_y h₁ hx₁, hy₂]
          field_simp [hx₁]
          nlinarith
  rcases hxf with hxeq | hprod
  · exact sameX hxeq
  · by_cases hxeq : x₁ = x₂
    · exact sameX hxeq
    · have hx₂val : x₂ = b / x₁ := by
        field_simp [hx₁]
        nlinarith
      have hsquare : x₁ ^ 2 ≠ b := by
        intro hs
        apply hxeq
        rw [hx₂val]
        field_simp [hx₁]
        nlinarith
      have hY := hcoords.2
      rw [hx₂val] at hY
      have hb := b_ne_zero a b
      unfold fy at hY
      field_simp [hx₁, hb] at hY
      have hfac : (x₁ ^ 2 - b) * (x₁ ^ 2 * y₂ + b * y₁) = 0 := by
        calc
          (x₁ ^ 2 - b) * (x₁ ^ 2 * y₂ + b * y₁) =
              -(y₁ * b * (b - x₁ ^ 2) -
                x₁ ^ 2 * y₂ * (x₁ ^ 2 - b)) := by ring
          _ = 0 := by rw [hY]; ring
      have hyrel : x₁ ^ 2 * y₂ + b * y₁ = 0 :=
        (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hsquare)
      right
      change Point.some x₂ y₂ h₂ =
        (Point.some x₁ y₁ h₁ : Point (curve a b)) +
          Point.some 0 0 _
      rw [Point.add_of_X_ne hx₁, Point.some.injEq]
      constructor
      · rw [add_kernel_x h₁ hx₁, hx₂val]
      · rw [add_kernel_y h₁ hx₁]
        field_simp [hx₁]
        nlinarith

lemma pointMap_eq_iff {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P Q : Point (curve a b)) :
    pointMap P = pointMap Q ↔ Q = P ∨ Q = P + kernelPoint a b := by
  constructor
  · intro hPQ
    by_cases hPzero : pointMap P = 0
    · have hQzero : pointMap Q = 0 := by rw [← hPQ]; exact hPzero
      rcases (pointMap_eq_zero_iff P).mp hPzero with hP | hP <;>
        rcases (pointMap_eq_zero_iff Q).mp hQzero with hQ | hQ
      · left
        rw [hP, hQ]
      · right
        rw [hP, hQ, zero_add]
      · right
        rw [hP, hQ, kernel_add_self]
      · left
        rw [hP, hQ]
    · have hQzero : pointMap Q ≠ 0 := by
        intro hQ
        apply hPzero
        rw [hPQ, hQ]
      cases P with
      | zero => exact (hPzero pointMap_zero).elim
      | some x₁ y₁ h₁ =>
          cases Q with
          | zero => exact (hQzero pointMap_zero).elim
          | some x₂ y₂ h₂ =>
              have hx₁ : x₁ ≠ 0 := by
                intro hx
                apply hPzero
                show pointMap (a := a) (b := b) (Point.some x₁ y₁ h₁) = Point.zero
                unfold pointMap
                exact dif_pos hx
              have hx₂ : x₂ ≠ 0 := by
                intro hx
                apply hQzero
                show pointMap (a := a) (b := b) (Point.some x₂ y₂ h₂) = Point.zero
                unfold pointMap
                exact dif_pos hx
              exact affine_fibre h₁ h₂ hx₁ hx₂ hPQ
  · rintro (rfl | rfl)
    · rfl
    · exact (pointMap_add_kernel P).symm

/-! ### The generic secant calculation

The two `secant_*_identity` lemmas package the only coordinate calculation.
They are low-degree consequences of the two curve equations and the equation of
the secant line; all exceptional configurations have already been classified as
kernel cosets.
-/

lemma secant_relations
    {a b x₁ y₁ x₂ y₂ ℓ r : ℚ}
    (h₁ : y₁ ^ 2 = x₁ * (x₁ ^ 2 + a * x₁ + b))
    (h₂ : y₂ ^ 2 = x₂ * (x₂ ^ 2 + a * x₂ + b))
    (hx₁x₂ : x₁ ≠ x₂)
    (hℓ : ℓ = (y₁ - y₂) / (x₁ - x₂))
    (hrdef : r = ℓ ^ 2 - a - x₁ - x₂) :
    x₁ * x₂ + x₁ * r + x₂ * r -
          (b - 2 * ℓ * y₁ + 2 * ℓ ^ 2 * x₁) = 0 ∧
      x₁ * x₂ * r - (y₁ - ℓ * x₁) ^ 2 = 0 := by
  have hline : y₂ = y₁ - ℓ * (x₁ - x₂) := by
    rw [hℓ]
    field_simp [sub_ne_zero.mpr hx₁x₂]
    ring
  have h₂' := h₂
  rw [hline] at h₂'
  have hBmul :
      (x₁ - x₂) *
        (x₁ * x₂ + x₁ * r + x₂ * r -
          (b - 2 * ℓ * y₁ + 2 * ℓ ^ 2 * x₁)) = 0 := by
    rw [hrdef]
    linear_combination h₁ - h₂'
  have hB :
      x₁ * x₂ + x₁ * r + x₂ * r -
          (b - 2 * ℓ * y₁ + 2 * ℓ ^ 2 * x₁) = 0 :=
    (mul_eq_zero.mp hBmul).resolve_left (sub_ne_zero.mpr hx₁x₂)
  refine ⟨hB, ?_⟩
  linear_combination x₁ * hB - h₁ - x₁ ^ 2 * hrdef

lemma secant_x_identity
    {a b x₁ y₁ x₂ y₂ ℓ r : ℚ}
    (h₁ : y₁ ^ 2 = x₁ * (x₁ ^ 2 + a * x₁ + b))
    (h₂ : y₂ ^ 2 = x₂ * (x₂ ^ 2 + a * x₂ + b))
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₁x₂ : x₁ ≠ x₂)
    (hℓ : ℓ = (y₁ - y₂) / (x₁ - x₂))
    (hrdef : r = ℓ ^ 2 - a - x₁ - x₂)
    (hr : r ≠ 0) (hb : x₁ * x₂ - b ≠ 0) :
    r + a + b / r =
      ((y₁ * (b - x₁ ^ 2) / x₁ ^ 2 -
          y₂ * (b - x₂ ^ 2) / x₂ ^ 2) /
        ((x₁ + a + b / x₁) - (x₂ + a + b / x₂))) ^ 2 +
        2 * a - (x₁ + a + b / x₁) - (x₂ + a + b / x₂) := by
  have hline : y₂ = y₁ - ℓ * (x₁ - x₂) := by
    rw [hℓ]
    field_simp [sub_ne_zero.mpr hx₁x₂]
    ring
  obtain ⟨hB, hC⟩ := secant_relations h₁ h₂ hx₁x₂ hℓ hrdef
  have hCeq : r * x₁ * x₂ = (ℓ * x₁ - y₁) ^ 2 := by
    linear_combination hC
  have hu : ℓ * x₁ - y₁ ≠ 0 := by
    intro hu0
    have hprod : r * x₁ * x₂ ≠ 0 := mul_ne_zero (mul_ne_zero hr hx₁) hx₂
    apply hprod
    rw [hCeq, hu0]
    norm_num
  have hu' : -y₁ + x₁ * ℓ ≠ 0 := by
    intro hu0
    apply hu
    linear_combination hu0
  have hu'' : x₁ * ℓ - y₁ ≠ 0 := by
    intro hu0
    apply hu
    linear_combination hu0
  have hT :
      x₁ * x₂ + r * (x₁ + x₂) = b + 2 * ℓ * (ℓ * x₁ - y₁) := by
    linear_combination hB
  have hA : r + x₁ + x₂ + a = ℓ ^ 2 := by
    linear_combination hrdef
  have hFD_eq :
      (x₁ + a + b / x₁) - (x₂ + a + b / x₂) =
        (x₁ - x₂) * (x₁ * x₂ - b) / (x₁ * x₂) := by
    field_simp [hx₁, hx₂]
    ring
  have hm₀ :
      (y₁ * (b - x₁ ^ 2) / x₁ ^ 2 -
          y₂ * (b - x₂ ^ 2) / x₂ ^ 2) /
        ((x₁ + a + b / x₁) - (x₂ + a + b / x₂)) =
      (-b * y₁ * (x₁ + x₂) + ℓ * x₁ ^ 2 * (b - x₂ ^ 2)) /
        (x₁ * x₂ * (x₁ * x₂ - b)) := by
    rw [hline, hFD_eq]
    field_simp [hx₁, hx₂, sub_ne_zero.mpr hx₁x₂, hb]
    ring
  have hcross :
      (-b * y₁ * (x₁ + x₂) + ℓ * x₁ ^ 2 * (b - x₂ ^ 2)) *
          (ℓ * x₁ - y₁) +
        (ℓ * (ℓ * x₁ - y₁) + b) * (x₁ * x₂ * (x₁ * x₂ - b)) = 0 := by
    linear_combination (b * x₁ * x₂) * hB - (b * (x₁ + x₂)) * hC
  have hden : x₁ * x₂ * (x₁ * x₂ - b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hx₁ hx₂) hb
  have hm₁ :
      (-b * y₁ * (x₁ + x₂) + ℓ * x₁ ^ 2 * (b - x₂ ^ 2)) /
          (x₁ * x₂ * (x₁ * x₂ - b)) =
        -(ℓ * (ℓ * x₁ - y₁) + b) / (ℓ * x₁ - y₁) := by
    apply (div_eq_iff hden).2
    field_simp [hu, hu', hu'']
    linear_combination hcross
  have hsum :
      (r + a + b / r) + (x₁ + a + b / x₁) +
          (x₂ + a + b / x₂) - 2 * a =
        ((ℓ * (ℓ * x₁ - y₁) + b) / (ℓ * x₁ - y₁)) ^ 2 := by
    calc
      (r + a + b / r) + (x₁ + a + b / x₁) +
            (x₂ + a + b / x₂) - 2 * a =
          r + x₁ + x₂ + a +
            b * (x₁ * x₂ + r * (x₁ + x₂)) / (r * x₁ * x₂) := by
        field_simp [hr, hx₁, hx₂]
        ring
      _ = ℓ ^ 2 +
            b * (x₁ * x₂ + r * (x₁ + x₂)) / (r * x₁ * x₂) := by rw [hA]
      _ = ℓ ^ 2 +
            b * (b + 2 * ℓ * (ℓ * x₁ - y₁)) /
              ((ℓ * x₁ - y₁) ^ 2) := by rw [hT, hCeq]
      _ = ((ℓ * (ℓ * x₁ - y₁) + b) / (ℓ * x₁ - y₁)) ^ 2 := by
        field_simp [hu]
        ring
  rw [hm₀, hm₁]
  linear_combination hsum

lemma secant_y_identity
    {a b x₁ y₁ x₂ y₂ ℓ r : ℚ}
    (h₁ : y₁ ^ 2 = x₁ * (x₁ ^ 2 + a * x₁ + b))
    (h₂ : y₂ ^ 2 = x₂ * (x₂ ^ 2 + a * x₂ + b))
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₁x₂ : x₁ ≠ x₂)
    (hℓ : ℓ = (y₁ - y₂) / (x₁ - x₂))
    (hrdef : r = ℓ ^ 2 - a - x₁ - x₂)
    (hr : r ≠ 0) (hb : x₁ * x₂ - b ≠ 0) :
    (ℓ * (x₁ - r) - y₁) * (b - r ^ 2) / r ^ 2 =
      ((y₁ * (b - x₁ ^ 2) / x₁ ^ 2 -
          y₂ * (b - x₂ ^ 2) / x₂ ^ 2) /
        ((x₁ + a + b / x₁) - (x₂ + a + b / x₂))) *
          ((x₁ + a + b / x₁) - (r + a + b / r)) -
        y₁ * (b - x₁ ^ 2) / x₁ ^ 2 := by
  have hline : y₂ = y₁ - ℓ * (x₁ - x₂) := by
    rw [hℓ]
    field_simp [sub_ne_zero.mpr hx₁x₂]
    ring
  obtain ⟨hB, hC⟩ := secant_relations h₁ h₂ hx₁x₂ hℓ hrdef
  have hH :
      ℓ * r * x₁ ^ 2 - ℓ * r * x₁ * x₂ + ℓ * x₁ ^ 2 * x₂ -
          b * ℓ * x₁ - r * x₁ * y₁ - r * x₂ * y₁ - x₁ * x₂ * y₁ +
          b * y₁ = 0 := by
    linear_combination (ℓ * x₁ - y₁) * hB - 2 * ℓ * hC
  have hFD_eq :
      (x₁ + a + b / x₁) - (x₂ + a + b / x₂) =
        (x₁ - x₂) * (x₁ * x₂ - b) / (x₁ * x₂) := by
    field_simp [hx₁, hx₂]
    ring
  have hm :
      (y₁ * (b - x₁ ^ 2) / x₁ ^ 2 -
          y₂ * (b - x₂ ^ 2) / x₂ ^ 2) /
        ((x₁ + a + b / x₁) - (x₂ + a + b / x₂)) =
      (-b * y₁ * (x₁ + x₂) + ℓ * x₁ ^ 2 * (b - x₂ ^ 2)) /
        (x₁ * x₂ * (x₁ * x₂ - b)) := by
    rw [hline, hFD_eq]
    field_simp [hx₁, hx₂, sub_ne_zero.mpr hx₁x₂, hb]
    ring
  rw [hm]
  apply sub_eq_zero.mp
  calc
    (ℓ * (x₁ - r) - y₁) * (b - r ^ 2) / r ^ 2 -
          ((-b * y₁ * (x₁ + x₂) + ℓ * x₁ ^ 2 * (b - x₂ ^ 2)) /
              (x₁ * x₂ * (x₁ * x₂ - b)) *
            ((x₁ + a + b / x₁) - (r + a + b / r)) -
          y₁ * (b - x₁ ^ 2) / x₁ ^ 2) =
        b * (x₁ - r) * (x₂ - r) *
            (ℓ * r * x₁ ^ 2 - ℓ * r * x₁ * x₂ + ℓ * x₁ ^ 2 * x₂ -
              b * ℓ * x₁ - r * x₁ * y₁ - r * x₂ * y₁ - x₁ * x₂ * y₁ +
              b * y₁) /
          (r ^ 2 * x₁ * x₂ * (x₁ * x₂ - b)) := by
      field_simp [hx₁, hx₂, hr, hb]
      ring
    _ = 0 := by rw [hH]; ring

/-! ### Additivity on the standard model -/

lemma pointMap_add_x_generic {a b x₁ y₁ x₂ y₂ : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h₁ : Nonsingular (curve a b) x₁ y₁)
    (h₂ : Nonsingular (curve a b) x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₁x₂ : x₁ ≠ x₂)
    (hr : addX (curve a b) x₁ x₂ (slope (curve a b) x₁ x₂ y₁ y₂) ≠ 0)
    (hF : fx x₁ y₁ ≠ fx x₂ y₂) :
    fx
        (addX (curve a b) x₁ x₂ (slope (curve a b) x₁ x₂ y₁ y₂))
        (addY (curve a b) x₁ x₂ y₁ (slope (curve a b) x₁ x₂ y₁ y₂)) =
      addX (curve (-2 * a) (a ^ 2 - 4 * b))
        (fx x₁ y₁) (fx x₂ y₂)
        (slope (curve (-2 * a) (a ^ 2 - 4 * b))
          (fx x₁ y₁) (fx x₂ y₂) (fy b x₁ y₁) (fy b x₂ y₂)) := by
  have heq₁ := curve_equation.mp h₁.left
  have heq₂ := curve_equation.mp h₂.left
  have hsum := nonsingular_add h₁ h₂ (fun hxy => hx₁x₂ hxy.1)
  have hsumEq := curve_equation.mp hsum.left
  have hr' :
      ((y₁ - y₂) / (x₁ - x₂)) ^ 2 - a - x₁ - x₂ ≠ 0 := by
    simpa [slope_of_X_ne hx₁x₂, addX, curve] using hr
  have hF' : x₁ + a + b / x₁ ≠ x₂ + a + b / x₂ := by
    simpa [fx_secant_form heq₁ hx₁, fx_secant_form heq₂ hx₂] using hF
  have hb : x₁ * x₂ - b ≠ 0 := by
    intro hzero
    apply hF'
    apply sub_eq_zero.mp
    calc
      (x₁ + a + b / x₁) - (x₂ + a + b / x₂) =
          (x₁ - x₂) * (x₁ * x₂ - b) / (x₁ * x₂) := by
        field_simp [hx₁, hx₂]
        ring
      _ = 0 := by rw [hzero]; simp
  have hid := secant_x_identity heq₁ heq₂ hx₁ hx₂ hx₁x₂
    (ℓ := (y₁ - y₂) / (x₁ - x₂))
    (r := ((y₁ - y₂) / (x₁ - x₂)) ^ 2 - a - x₁ - x₂)
    rfl rfl hr' hb
  rw [fx_secant_form hsumEq hr]
  rw [slope_of_X_ne hx₁x₂, slope_of_X_ne hF]
  rw [fx_secant_form heq₁ hx₁, fx_secant_form heq₂ hx₂]
  simp only [addX, curve, zero_mul, add_zero, fy]
  convert hid using 1 <;> ring

lemma pointMap_add_y_generic {a b x₁ y₁ x₂ y₂ : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h₁ : Nonsingular (curve a b) x₁ y₁)
    (h₂ : Nonsingular (curve a b) x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₁x₂ : x₁ ≠ x₂)
    (hr : addX (curve a b) x₁ x₂ (slope (curve a b) x₁ x₂ y₁ y₂) ≠ 0)
    (hF : fx x₁ y₁ ≠ fx x₂ y₂) :
    fy b
        (addX (curve a b) x₁ x₂ (slope (curve a b) x₁ x₂ y₁ y₂))
        (addY (curve a b) x₁ x₂ y₁ (slope (curve a b) x₁ x₂ y₁ y₂)) =
      addY (curve (-2 * a) (a ^ 2 - 4 * b))
        (fx x₁ y₁) (fx x₂ y₂) (fy b x₁ y₁)
        (slope (curve (-2 * a) (a ^ 2 - 4 * b))
          (fx x₁ y₁) (fx x₂ y₂) (fy b x₁ y₁) (fy b x₂ y₂)) := by
  have heq₁ := curve_equation.mp h₁.left
  have heq₂ := curve_equation.mp h₂.left
  have hsum := nonsingular_add h₁ h₂ (fun hxy => hx₁x₂ hxy.1)
  have hsumEq := curve_equation.mp hsum.left
  have hr' :
      ((y₁ - y₂) / (x₁ - x₂)) ^ 2 - a - x₁ - x₂ ≠ 0 := by
    simpa [slope_of_X_ne hx₁x₂, addX, curve] using hr
  have hF' : x₁ + a + b / x₁ ≠ x₂ + a + b / x₂ := by
    simpa [fx_secant_form heq₁ hx₁, fx_secant_form heq₂ hx₂] using hF
  have hb : x₁ * x₂ - b ≠ 0 := by
    intro hzero
    apply hF'
    apply sub_eq_zero.mp
    calc
      (x₁ + a + b / x₁) - (x₂ + a + b / x₂) =
          (x₁ - x₂) * (x₁ * x₂ - b) / (x₁ * x₂) := by
        field_simp [hx₁, hx₂]
        ring
      _ = 0 := by rw [hzero]; simp
  have hid := secant_y_identity heq₁ heq₂ hx₁ hx₂ hx₁x₂
    (ℓ := (y₁ - y₂) / (x₁ - x₂))
    (r := ((y₁ - y₂) / (x₁ - x₂)) ^ 2 - a - x₁ - x₂)
    rfl rfl hr' hb
  have hX := pointMap_add_x_generic h₁ h₂ hx₁ hx₂ hx₁x₂ hr hF
  unfold addY WeierstrassCurve.Affine.negAddY
  rw [curve_negY, curve_negY]
  rw [← hX]
  rw [fx_secant_form hsumEq hr]
  rw [slope_of_X_ne hx₁x₂, slope_of_X_ne hF]
  rw [fx_secant_form heq₁ hx₁, fx_secant_form heq₂ hx₂]
  simp only [fy, addX, curve, zero_mul, add_zero]
  convert hid using 1 <;> ring

lemma pointMap_add_generic {a b x₁ y₁ x₂ y₂ : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h₁ : Nonsingular (curve a b) x₁ y₁)
    (h₂ : Nonsingular (curve a b) x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₁x₂ : x₁ ≠ x₂)
    (hr : addX (curve a b) x₁ x₂ (slope (curve a b) x₁ x₂ y₁ y₂) ≠ 0)
    (hF : fx x₁ y₁ ≠ fx x₂ y₂) :
    pointMap
        ((Point.some x₁ y₁ h₁ : Point (curve a b)) + Point.some x₂ y₂ h₂) =
      pointMap (Point.some x₁ y₁ h₁) + pointMap (Point.some x₂ y₂ h₂) := by
  rw [Point.add_of_X_ne hx₁x₂]
  have hsum := nonsingular_add h₁ h₂ (fun hxy => hx₁x₂ hxy.1)
  rw [pointMap_some hsum hr, pointMap_some h₁ hx₁, pointMap_some h₂ hx₂]
  rw [Point.add_of_X_ne hF, Point.some.injEq]
  exact ⟨pointMap_add_x_generic h₁ h₂ hx₁ hx₂ hx₁x₂ hr hF,
    pointMap_add_y_generic h₁ h₂ hx₁ hx₂ hx₁x₂ hr hF⟩

lemma pointMap_add_zero {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (P + 0) = pointMap P + pointMap 0 := by
  rw [add_zero, pointMap_zero, add_zero]

lemma pointMap_zero_add {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (0 + P) = pointMap 0 + pointMap P := by
  rw [zero_add, pointMap_zero, zero_add]

lemma pointMap_add_neg {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (P + -P) = pointMap P + pointMap (-P) := by
  rw [add_neg_cancel, pointMap_zero, pointMap_neg, add_neg_cancel]

lemma pointMap_add_kernelTranslate {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (P + (P + kernelPoint a b)) =
      pointMap P + pointMap (P + kernelPoint a b) := by
  rw [← add_assoc, pointMap_add_kernel, pointMap_add_kernel, pointMap_add_self]

lemma pointMap_add_neg_kernelTranslate {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P : Point (curve a b)) :
    pointMap (P + (-P + kernelPoint a b)) =
      pointMap P + pointMap (-P + kernelPoint a b) := by
  rw [← add_assoc, add_neg_cancel, zero_add, pointMap_kernel,
    pointMap_add_kernel, pointMap_neg, add_neg_cancel]

lemma pointMap_add_of_basic_or_kernel_relation {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P Q : Point (curve a b))
    (hQ : Q = 0 ∨ Q = kernelPoint a b ∨ Q = P ∨ Q = -P ∨
      Q = P + kernelPoint a b ∨ Q = -P + kernelPoint a b) :
    pointMap (P + Q) = pointMap P + pointMap Q := by
  rcases hQ with hQ | hQ | hQ | hQ | hQ | hQ
  · rw [hQ]
    exact pointMap_add_zero P
  · rw [hQ, pointMap_add_kernel, pointMap_kernel, add_zero]
  · rw [hQ]
    exact pointMap_add_self P
  · rw [hQ]
    exact pointMap_add_neg P
  · rw [hQ]
    exact pointMap_add_kernelTranslate P
  · rw [hQ]
    exact pointMap_add_neg_kernelTranslate P

lemma kernel_neg {a b : ℚ} [hE : (curve a b).IsElliptic] :
    -(kernelPoint a b) = kernelPoint a b := by
  rw [neg_eq_iff_add_eq_zero]
  exact kernel_add_self

lemma pointMap_add_of_fx_eq {a b x₁ y₁ x₂ y₂ : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h₁ : Nonsingular (curve a b) x₁ y₁)
    (h₂ : Nonsingular (curve a b) x₂ y₂)
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hF : fx x₁ y₁ = fx x₂ y₂) :
    pointMap
        ((Point.some x₁ y₁ h₁ : Point (curve a b)) + Point.some x₂ y₂ h₂) =
      pointMap (Point.some x₁ y₁ h₁) + pointMap (Point.some x₂ y₂ h₂) := by
  have hf₁ : Nonsingular (curve (-2 * a) (a ^ 2 - 4 * b))
      (fx x₁ y₁) (fy b x₁ y₁) :=
    equation_iff_nonsingular.mp (forward_equation h₁.left hx₁)
  have hf₂ : Nonsingular (curve (-2 * a) (a ^ 2 - 4 * b))
      (fx x₂ y₂) (fy b x₂ y₂) :=
    equation_iff_nonsingular.mp (forward_equation h₂.left hx₂)
  rcases (Point.X_eq_iff (h₁ := hf₁) (h₂ := hf₂)).mp hF with hsame | hneg
  · have hmap :
        pointMap (a := a) (b := b) (Point.some x₁ y₁ h₁) =
          pointMap (a := a) (b := b) (Point.some x₂ y₂ h₂) := by
      rw [pointMap_some h₁ hx₁, pointMap_some h₂ hx₂]
      exact hsame
    rcases (pointMap_eq_iff
      (Point.some x₁ y₁ h₁) (Point.some x₂ y₂ h₂)).mp hmap with hQ | hQ
    · exact pointMap_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inl hQ)))
    · exact pointMap_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hQ)))))
  · have hmapneg :
        pointMap (a := a) (b := b) (Point.some x₁ y₁ h₁) =
          -pointMap (a := a) (b := b) (Point.some x₂ y₂ h₂) := by
      rw [pointMap_some h₁ hx₁, pointMap_some h₂ hx₂]
      exact hneg
    have hmap :
        pointMap (a := a) (b := b) (Point.some x₁ y₁ h₁) =
          pointMap (a := a) (b := b) (-(Point.some x₂ y₂ h₂)) := by
      rw [pointMap_neg]
      exact hmapneg
    rcases (pointMap_eq_iff
      (Point.some x₁ y₁ h₁) (-(Point.some x₂ y₂ h₂))).mp hmap with hQ | hQ
    · have hQ' :
          (Point.some x₂ y₂ h₂ : Point (curve a b)) =
            -(Point.some x₁ y₁ h₁) := by
        calc
          (Point.some x₂ y₂ h₂ : Point (curve a b)) =
              -(-(Point.some x₂ y₂ h₂)) := (neg_neg _).symm
          _ = -(Point.some x₁ y₁ h₁) := congrArg Neg.neg hQ
      exact pointMap_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inr (Or.inl hQ'))))
    · have hQ' :
          (Point.some x₂ y₂ h₂ : Point (curve a b)) =
            -(Point.some x₁ y₁ h₁) + kernelPoint a b := by
        calc
          (Point.some x₂ y₂ h₂ : Point (curve a b)) =
              -(-(Point.some x₂ y₂ h₂)) := (neg_neg _).symm
          _ = -((Point.some x₁ y₁ h₁ : Point (curve a b)) +
                kernelPoint a b) := by rw [hQ]
          _ = -(Point.some x₁ y₁ h₁) + kernelPoint a b := by
            rw [neg_add_rev, kernel_neg, add_comm]
      exact pointMap_add_of_basic_or_kernel_relation _ _
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ')))))

theorem pointMap_add {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (P Q : Point (curve a b)) :
    pointMap (P + Q) = pointMap P + pointMap Q := by
  cases P with
  | zero => exact pointMap_zero_add Q
  | some x₁ y₁ h₁ =>
      cases Q with
      | zero => exact pointMap_add_zero _
      | some x₂ y₂ h₂ =>
          by_cases hx₁ : x₁ = 0
          · have hy₁ := y_zero_of_x_zero h₁ hx₁
            have hP :
                (Point.some x₁ y₁ h₁ : Point (curve a b)) = kernelPoint a b := by
              unfold kernelPoint
              rw [Point.some.injEq]
              exact ⟨hx₁, hy₁⟩
            rw [hP, pointMap_kernel_add, pointMap_kernel, zero_add]
          · by_cases hx₂ : x₂ = 0
            · have hy₂ := y_zero_of_x_zero h₂ hx₂
              have hQ :
                  (Point.some x₂ y₂ h₂ : Point (curve a b)) = kernelPoint a b := by
                unfold kernelPoint
                rw [Point.some.injEq]
                exact ⟨hx₂, hy₂⟩
              rw [hQ, pointMap_add_kernel, pointMap_kernel, add_zero]
            · by_cases hx₁x₂ : x₁ = x₂
              · rcases (Point.X_eq_iff (h₁ := h₁) (h₂ := h₂)).mp hx₁x₂ with hsame | hneg
                · rw [← hsame]
                  exact pointMap_add_self _
                · have hQ :
                      (Point.some x₂ y₂ h₂ : Point (curve a b)) =
                        -(Point.some x₁ y₁ h₁) := by
                    calc
                      (Point.some x₂ y₂ h₂ : Point (curve a b)) =
                          -(-(Point.some x₂ y₂ h₂)) := (neg_neg _).symm
                      _ = -(Point.some x₁ y₁ h₁) := (congrArg Neg.neg hneg).symm
                  rw [hQ]
                  exact pointMap_add_neg _
              · by_cases hr :
                    addX (curve a b) x₁ x₂ (slope (curve a b) x₁ x₂ y₁ y₂) = 0
                · have hsum := nonsingular_add h₁ h₂ (fun hxy => hx₁x₂ hxy.1)
                  have hsumY := y_zero_of_x_zero hsum hr
                  have hsumK :
                      (Point.some x₁ y₁ h₁ : Point (curve a b)) +
                          Point.some x₂ y₂ h₂ = kernelPoint a b := by
                    change
                      (Point.some x₁ y₁ h₁ : Point (curve a b)) +
                          Point.some x₂ y₂ h₂ = Point.some 0 0 _
                    rw [Point.add_of_X_ne hx₁x₂, Point.some.injEq]
                    exact ⟨hr, hsumY⟩
                  have hQ :
                      (Point.some x₂ y₂ h₂ : Point (curve a b)) =
                        -(Point.some x₁ y₁ h₁) + kernelPoint a b := by
                    calc
                      (Point.some x₂ y₂ h₂ : Point (curve a b)) =
                          -(Point.some x₁ y₁ h₁) +
                            ((Point.some x₁ y₁ h₁ : Point (curve a b)) +
                              Point.some x₂ y₂ h₂) := by
                        symm
                        rw [← add_assoc, neg_add_cancel, zero_add]
                      _ = -(Point.some x₁ y₁ h₁) + kernelPoint a b := by
                        rw [hsumK]
                  exact pointMap_add_of_basic_or_kernel_relation _ _
                    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hQ)))))
                · by_cases hF : fx x₁ y₁ = fx x₂ y₂
                  · exact pointMap_add_of_fx_eq h₁ h₂ hx₁ hx₂ hF
                  · exact pointMap_add_generic h₁ h₂ hx₁ hx₂ hx₁x₂ hr hF

/-! ### Conjugating the Vélu formula to the standard model -/

open MazurProof.N18RouteC.VariableChangePoints

def sourceChange (r : ℚ) : WeierstrassCurve.VariableChange ℚ where
  u := 1
  r := r
  s := 0
  t := 0

def targetChange (r : ℚ) : WeierstrassCurve.VariableChange ℚ where
  u := -1
  r := -2 * r
  s := 0
  t := 0

lemma sourceChange_eq {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    sourceChange r • shortWS A B = curve (3 * r) (veluT A r) := by
  rw [WeierstrassCurve.variableChange_def]
  ext <;> simp [sourceChange, shortWS, curve, veluT] <;> nlinarith

lemma targetChange_eq {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    targetChange r • veluQuotCurve A B r =
      curve (-2 * (3 * r)) ((3 * r) ^ 2 - 4 * veluT A r) := by
  rw [WeierstrassCurve.variableChange_def]
  ext <;> simp [targetChange, veluQuotCurve, curve, veluT] <;> nlinarith

noncomputable def curveCastAddEquiv {W₁ W₂ : WeierstrassCurve ℚ}
    [W₁.IsElliptic] [W₂.IsElliptic] (h : W₁ = W₂) :
    Point W₁ ≃+ Point W₂ :=
  AddEquiv.mk
    { toFun := fun P => h ▸ P
      invFun := fun P => h.symm ▸ P
      left_inv := by subst h; intro P; rfl
      right_inv := by subst h; intro P; rfl }
    (by subst h; intro P Q; rfl)

@[reducible] def sourceStdIsElliptic {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic] :
    (curve (3 * r) (veluT A r)).IsElliptic :=
  sourceChange_eq htors ▸
    (inferInstance : (sourceChange r • shortWS A B).IsElliptic)

@[reducible] def targetStdIsElliptic {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    (curve (-2 * (3 * r)) ((3 * r) ^ 2 - 4 * veluT A r)).IsElliptic :=
  targetChange_eq htors ▸
    (inferInstance : (targetChange r • veluQuotCurve A B r).IsElliptic)

noncomputable def sourceEquiv {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic] :
    Point (shortWS A B) ≃+ Point (curve (3 * r) (veluT A r)) :=
  haveI hstd : (curve (3 * r) (veluT A r)).IsElliptic :=
    sourceStdIsElliptic htors
  (variableChangePointAddEquiv (shortWS A B) (sourceChange r)).trans
    (curveCastAddEquiv (sourceChange_eq htors))

noncomputable def targetEquiv {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Point (veluQuotCurve A B r) ≃+
      Point (curve (-2 * (3 * r)) ((3 * r) ^ 2 - 4 * veluT A r)) :=
  haveI hstd :
      (curve (-2 * (3 * r)) ((3 * r) ^ 2 - 4 * veluT A r)).IsElliptic :=
    targetStdIsElliptic htors
  (variableChangePointAddEquiv (veluQuotCurve A B r) (targetChange r)).trans
    (curveCastAddEquiv (targetChange_eq htors))

lemma standard_x_eq {A B r x y : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    (hcurve : y ^ 2 = x ^ 3 + A * x + B)
    (hxr : x ≠ r) :
    fx (x - r) y = x + veluT A r / (x - r) + 2 * r := by
  have hB : B = -(r ^ 3 + A * r) := by
    linarith [htors]
  have hfactor :
      y ^ 2 = (x - r) * (x ^ 2 + x * r + r ^ 2 + A) := by
    rw [hcurve, hB]
    ring
  unfold fx veluT
  field_simp [sub_ne_zero.mpr hxr]
  rw [hfactor]
  ring

@[simp] lemma sourceChange_x (r x : ℚ) :
    variableChangePointX (sourceChange r) x = x - r := by
  simp [variableChangePointX, sourceChange]

@[simp] lemma sourceChange_y (r x y : ℚ) :
    variableChangePointY (sourceChange r) x y = y := by
  simp [variableChangePointY, sourceChange]

@[simp] lemma targetChange_x (r x : ℚ) :
    variableChangePointX (targetChange r) x = x + 2 * r := by
  simp [variableChangePointX, targetChange]

@[simp] lemma targetChange_y (r x y : ℚ) :
    variableChangePointY (targetChange r) x y = -y := by
  simp [variableChangePointY, targetChange]
  ring

lemma variableChangeEquiv_some
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange ℚ)
    {x y : ℚ} (hns : Nonsingular W x y) :
    (variableChangePointAddEquiv W C) (Point.some x y hns) =
      Point.some (variableChangePointX C x) (variableChangePointY C x y)
        (equation_iff_nonsingular.mp
          (variableChangePoint_equation W C hns.left)) := by
  show variableChangePointMap W C (Point.some x y hns) = _
  unfold variableChangePointMap
  rfl

lemma curveCastAddEquiv_some {W₁ W₂ : WeierstrassCurve ℚ}
    [W₁.IsElliptic] [W₂.IsElliptic] (h : W₁ = W₂)
    {x y : ℚ} (hns : Nonsingular W₁ x y) :
    curveCastAddEquiv h (Point.some x y hns) =
      Point.some x y (h ▸ hns) := by
  subst h
  rfl

@[simp] lemma sourceEquiv_zero {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic] :
    sourceEquiv htors 0 = 0 :=
  map_zero _

@[simp] lemma targetEquiv_zero {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    targetEquiv htors 0 = 0 :=
  map_zero _

lemma sourceEquiv_some {A B r x y : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hstd : (curve (3 * r) (veluT A r)).IsElliptic]
    (hns : Nonsingular (shortWS A B) x y) :
    sourceEquiv htors (Point.some x y hns) =
      Point.some (variableChangePointX (sourceChange r) x)
        (variableChangePointY (sourceChange r) x y)
        ((sourceChange_eq htors) ▸
          equation_iff_nonsingular.mp
            (variableChangePoint_equation (shortWS A B) (sourceChange r) hns.left)) := by
  unfold sourceEquiv
  rw [AddEquiv.trans_apply, variableChangeEquiv_some, curveCastAddEquiv_some]

lemma targetEquiv_some {A B r x y : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic]
    [hstd :
      (curve (-2 * (3 * r)) ((3 * r) ^ 2 - 4 * veluT A r)).IsElliptic]
    (hns : Nonsingular (veluQuotCurve A B r) x y) :
    targetEquiv htors (Point.some x y hns) =
      Point.some (variableChangePointX (targetChange r) x)
        (variableChangePointY (targetChange r) x y)
        ((targetChange_eq htors) ▸
          equation_iff_nonsingular.mp
            (variableChangePoint_equation (veluQuotCurve A B r) (targetChange r) hns.left)) := by
  unfold targetEquiv
  rw [AddEquiv.trans_apply, variableChangeEquiv_some, curveCastAddEquiv_some]

lemma map_conjugacy {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic]
    [hsourceStd : (curve (3 * r) (veluT A r)).IsElliptic]
    [htargetStd :
      (curve (-2 * (3 * r)) ((3 * r) ^ 2 - 4 * veluT A r)).IsElliptic]
    (P : Point (shortWS A B)) :
    targetEquiv htors (veluMapPoint htors P) =
      pointMap (sourceEquiv htors P) := by
  cases P with
  | zero =>
      change targetEquiv htors 0 = pointMap (sourceEquiv htors 0)
      rw [targetEquiv_zero, sourceEquiv_zero, pointMap_zero]
  | some x y h =>
      by_cases hxr : x = r
      · have hmap : veluMapPoint htors (Point.some x y h) = 0 := by
          show veluMapPoint htors (Point.some x y h) = Point.zero
          unfold veluMapPoint
          exact dif_pos hxr
        rw [hmap, targetEquiv_zero, sourceEquiv_some]
        have hx0 : variableChangePointX (sourceChange r) x = 0 := by
          simp [hxr]
        simp only [pointMap, hx0, dite_true]
        rfl
      · have hvns := equation_iff_nonsingular.mp (velu_equation h.left htors hxr)
        have hmap :
            veluMapPoint htors (Point.some x y h) =
              Point.some (x + veluT A r / (x - r))
                (y * ((x - r) ^ 2 - veluT A r) / (x - r) ^ 2) hvns := by
          unfold veluMapPoint
          exact dif_neg hxr
        rw [hmap, targetEquiv_some, sourceEquiv_some]
        rw [pointMap_some]
        · rw [Point.some.injEq]
          constructor
          · simp only [targetChange_x, sourceChange_x, sourceChange_y]
            exact (standard_x_eq htors (shortWS_equation.mp h.left) hxr).symm
          · simp only [targetChange_x, targetChange_y, sourceChange_x,
              sourceChange_y, fy]
            ring
        · simpa only [sourceChange_x] using sub_ne_zero.mpr hxr

theorem conjugated_veluMapPoint_add {A B r : ℚ}
    (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic]
    (P Q : Point (shortWS A B)) :
    veluMapPoint htors (P + Q) = veluMapPoint htors P + veluMapPoint htors Q := by
  letI hsourceStd : (curve (3 * r) (veluT A r)).IsElliptic :=
    sourceStdIsElliptic htors
  letI htargetStd :
      (curve (-2 * (3 * r)) ((3 * r) ^ 2 - 4 * veluT A r)).IsElliptic :=
    targetStdIsElliptic htors
  apply (targetEquiv htors).injective
  calc
    targetEquiv htors (veluMapPoint htors (P + Q)) =
        pointMap (sourceEquiv htors (P + Q)) :=
      map_conjugacy htors (P + Q)
    _ = pointMap (sourceEquiv htors P + sourceEquiv htors Q) := by
      rw [map_add]
    _ = pointMap (sourceEquiv htors P) + pointMap (sourceEquiv htors Q) :=
      pointMap_add _ _
    _ = targetEquiv htors (veluMapPoint htors P) +
        targetEquiv htors (veluMapPoint htors Q) := by
      rw [map_conjugacy, map_conjugacy]
    _ = targetEquiv htors (veluMapPoint htors P + veluMapPoint htors Q) := by
      rw [map_add]


end StandardTwoIsogeny

lemma veluMapPoint_add {A B r : ℚ} {htors : r ^ 3 + A * r + B = 0}
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic]
    (P Q : Point (shortWS A B)) :
    veluMapPoint htors (P + Q) =
      veluMapPoint htors P + veluMapPoint htors Q :=
  StandardTwoIsogeny.conjugated_veluMapPoint_add htors P Q

def veluMapHom {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE : (shortWS A B).IsElliptic]
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Point (shortWS A B) →+ Point (veluQuotCurve A B r) where
  toFun := veluMapPoint htors
  map_zero' := veluMapPoint_zero
  map_add' := veluMapPoint_add

/-! ## η = (-2r, 0) on E' -/

lemma eta_on_curve {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0) :
    Equation (veluQuotCurve A B r) (-2 * r) 0 := by
  rw [veluQuotCurve_equation]
  unfold veluT
  nlinarith

lemma eta_nonsingular {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Nonsingular (veluQuotCurve A B r) (-2 * r) 0 :=
  equation_iff_nonsingular.mp (eta_on_curve htors)

def etaPoint {A B r : ℚ} (htors : r ^ 3 + A * r + B = 0)
    [hE' : (veluQuotCurve A B r).IsElliptic] :
    Point (veluQuotCurve A B r) :=
  .some (-2 * r) 0 (eta_nonsingular htors)

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

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.VeluTwoIsogeny
open MazurProof.N18RouteC.VariableChangePoints

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

/-- The horizontal coordinate of the variable change is `4x-1`. -/
@[simp] theorem toShortChange_x (x : ℚ) :
    variableChangePointX toShortChange x = 4 * x - 1 := by
  norm_num [variableChangePointX, toShortChange]
  ring

/-- The vertical coordinate of the variable change is `8y+4x+4`. -/
@[simp] theorem toShortChange_y (x y : ℚ) :
    variableChangePointY toShortChange x y = 8 * y + 4 * x + 4 := by
  norm_num [variableChangePointY, toShortChange]
  ring

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

/-- Vélu quotient of the short model by its visible rational two-torsion. -/
@[reducible] def shortDual : WeierstrassCurve ℚ :=
  veluQuotCurve (-11) (-890) 10

/-- The Vélu quotient remains elliptic. -/
instance shortDual_isElliptic : shortDual.IsElliptic :=
  veluQuotCurve_isElliptic ten_is_root
    (inferInstance : short.IsElliptic)

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

/-- The standard dual is
`Y² = X(X² - 60X - 256) = X(X-64)(X+4)`. -/
@[reducible] def standardDual : WeierstrassCurve ℚ :=
  StandardTwoIsogeny.curve (-2 * a17) (a17 ^ 2 - 4 * b17)

/-- The standard source change identifies `short` with `standard`. -/
theorem sourceChange_curve :
    StandardTwoIsogeny.sourceChange 10 • short = standard := by
  simpa only [short, standard, a17, b17] using
    StandardTwoIsogeny.sourceChange_eq ten_is_root

/-- The standard target change identifies the Vélu quotient with
`standardDual`. -/
theorem targetChange_curve :
    StandardTwoIsogeny.targetChange 10 • shortDual = standardDual := by
  simpa only [shortDual, standardDual, a17, b17] using
    StandardTwoIsogeny.targetChange_eq ten_is_root

/-- The standard source model is elliptic. -/
instance standard_isElliptic : standard.IsElliptic := by
  rw [← sourceChange_curve]
  infer_instance

/-- The standard dual model is elliptic. -/
instance standardDual_isElliptic : standardDual.IsElliptic := by
  rw [← targetChange_curve]
  infer_instance

/-- Additive equivalence from the integral model to the short model. -/
noncomputable def X017ToShort : Point X017 ≃+ Point short :=
  (variableChangePointAddEquiv X017 toShortChange).trans
    (StandardTwoIsogeny.curveCastAddEquiv toShortChange_curve)

/-- Additive equivalence from the short model to the standard source model. -/
noncomputable def ShortToStandard : Point short ≃+ Point standard := by
  simpa only [short, standard, a17, b17] using
    StandardTwoIsogeny.sourceEquiv ten_is_root

/-- Additive equivalence from the integral model to the standard
two-isogeny source model. -/
noncomputable def X017ToStandard : Point X017 ≃+ Point standard :=
  X017ToShort.trans ShortToStandard

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

/-- The coordinates `(64,0)` define a nonsingular point on the standard
dual curve. -/
private theorem U_nonsingular :
    Nonsingular standardDual 64 0 := by
  apply equation_iff_nonsingular.mp
  rw [StandardTwoIsogeny.curve_equation]
  norm_num [a17, b17, veluT]

/-- The forward two-isogeny image of `T` on the standard dual curve. -/
noncomputable def U : Point standardDual :=
  Point.some 64 0 U_nonsingular

/-- The standard forward two-isogeny sends `T` to `(64,0)`. -/
theorem pointMap_T :
    StandardTwoIsogeny.pointMap T = U := by
  change
    StandardTwoIsogeny.pointMap (a := a17) (b := b17)
        (Point.some 17 136 T_nonsingular) =
      Point.some 64 0 U_nonsingular
  rw [StandardTwoIsogeny.pointMap_some T_nonsingular (by norm_num)]
  rw [Point.some.injEq]
  constructor
  · norm_num [a17, b17, veluT, StandardTwoIsogeny.fx]
  · norm_num [a17, b17, veluT, StandardTwoIsogeny.fy]

/-- The standard dual isogeny sends `(64,0)` to the source kernel point. -/
theorem dualPoint_U :
    StandardTwoIsogeny.dualPoint U = K := by
  change
    StandardTwoIsogeny.dualPoint (a := a17) (b := b17)
        (Point.some 64 0 U_nonsingular) =
      StandardTwoIsogeny.kernelPoint a17 b17
  rw [StandardTwoIsogeny.dualPoint_some U_nonsingular (by norm_num)]
  unfold StandardTwoIsogeny.kernelPoint
  rw [Point.some.injEq]
  constructor
  · norm_num [StandardTwoIsogeny.dx]
  · norm_num [StandardTwoIsogeny.dy]

/-- The dual-composition theorem computes `2T` as the visible kernel point. -/
theorem two_nsmul_T_eq_K : 2 • T = K := by
  have h := StandardTwoIsogeny.dual_comp_pointMap T
  rw [pointMap_T, dualPoint_U] at h
  exact h.symm

/-- The visible point `T` is not the point at infinity. -/
theorem T_ne_zero : T ≠ 0 :=
  Point.some_ne_zero _

/-- The visible kernel point is not the point at infinity. -/
theorem K_ne_zero : K ≠ 0 := by
  unfold K StandardTwoIsogeny.kernelPoint
  exact Point.some_ne_zero _

/-- The visible point `T` has exact additive order four. -/
theorem T_order_four : addOrderOf T = 4 := by
  have h2K : 2 • K = 0 := by
    change 2 • StandardTwoIsogeny.kernelPoint a17 b17 = 0
    simpa [two_nsmul] using
      (StandardTwoIsogeny.kernel_add_self (a := a17) (b := b17))
  have h4 : 4 • T = 0 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_nsmul,
      two_nsmul_T_eq_K, h2K]
  apply (addOrderOf_eq_iff (x := T) (by norm_num)).2
  refine ⟨h4, ?_⟩
  intro m hm hmpos
  have hm_cases : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm_cases with rfl | rfl | rfl
  · simpa using T_ne_zero
  · simpa [two_nsmul_T_eq_K] using K_ne_zero
  · intro h3
    have h43 : 4 • T = 3 • T + T := by
      rw [show (4 : ℕ) = 3 + 1 by norm_num, add_nsmul, one_nsmul]
    rw [h4, h3, zero_add] at h43
    exact T_ne_zero h43.symm

end

end MazurProof.X017Model

end

-- ===== FLT.Assumptions.MazurProof.X017FormalTwoCore =====
section
/-!
# The two-adic formal kernel of the integral X₀(17) model

This file proves the local part of the good-reduction argument on

`y² + xy + y = x³ - x² - x - 14`.

For a nonzero formal point, the affine valuations have the shape
`v₂(x) = -2k`, `v₂(y) = -3k` with `k > 0`.  Explicit duplication formulas
show that doubling either gives zero or raises `k` by at least one.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017FormalTwoCore

open WeierstrassCurve.Affine
open MazurProof.X017Model

noncomputable section

/-! ## Elementary valuation lemmas -/

private theorem val_int_nonneg (z : ℤ) :
    0 ≤ padicValRat 2 (z : ℚ) := by
  rw [padicValRat.of_int]
  exact Int.natCast_nonneg _

private theorem val_add_eq_left_of_lt {a b : ℚ} (ha : a ≠ 0)
    (hval : padicValRat 2 a < padicValRat 2 b) :
    padicValRat 2 (a + b) = padicValRat 2 a := by
  by_cases hb : b = 0
  · simp [hb]
  have hab : a + b ≠ 0 := by
    intro hzero
    have hba : b = -a := by linarith
    have : padicValRat 2 b = padicValRat 2 a := by
      rw [hba, padicValRat.neg]
    omega
  exact padicValRat.add_eq_of_lt hab ha hb hval

private theorem val_sum_gt_or_zero {q : ℚ} (l : List ℚ)
    (hgt : ∀ a ∈ l, padicValRat 2 q < padicValRat 2 a) :
    l.sum = 0 ∨ padicValRat 2 q < padicValRat 2 l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : padicValRat 2 q < padicValRat 2 a := hgt a (by simp)
      have htail : ∀ b ∈ l, padicValRat 2 q < padicValRat 2 b := by
        intro b hb
        exact hgt b (by simp [hb])
      rcases ih htail with hzero | htailgt
      · right
        simpa [hzero] using ha
      · by_cases hs : a + l.sum = 0
        · exact Or.inl (by simpa using hs)
        · exact Or.inr (padicValRat.lt_add_of_lt hs ha htailgt)

private theorem val_add_list_eq {q : ℚ} (l : List ℚ) (hq : q ≠ 0)
    (hgt : ∀ a ∈ l, padicValRat 2 q < padicValRat 2 a) :
    padicValRat 2 (q + l.sum) = padicValRat 2 q := by
  rcases val_sum_gt_or_zero l hgt with hzero | hsum
  · simp [hzero]
  · exact val_add_eq_left_of_lt hq hsum

private theorem val_monomial_ge
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (c : ℤ) (hc : c ≠ 0) (a b : ℕ) :
    (a : ℤ) * padicValRat 2 x + (b : ℤ) * padicValRat 2 y ≤
      padicValRat 2 ((c : ℚ) * x ^ a * y ^ b) := by
  rw [padicValRat.mul
      (mul_ne_zero (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx))
      (pow_ne_zero b hy),
    padicValRat.mul (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx),
    padicValRat.pow_of_ne_zero hx, padicValRat.pow_of_ne_zero hy]
  have hcval := val_int_nonneg c
  omega

/-! ## Explicit duplication formulas -/

/-- Denominator of the tangent slope on the integral model. -/
def doubleDen (x y : ℚ) : ℚ :=
  2 * y + x + 1

/-- Numerator of the horizontal coordinate after doubling. -/
def doubleXNum (x : ℚ) : ℚ :=
  x ^ 4 + x ^ 2 + 110 * x - 41

/-- Numerator of the vertical coordinate after doubling. -/
def doubleYNum (x y : ℚ) : ℚ :=
  x ^ 6 - 2 * x ^ 5 - 5 * x ^ 4 - 276 * x ^ 3 + 152 * x ^ 2 -
    95 * x + y * (-x ^ 4 - 4 * x ^ 3 + 2 * x ^ 2 - 108 * x + 96) - 1485

/-- The tangent formula for the horizontal coordinate has denominator
`doubleDen²`. -/
theorem doubleX_formula {x y : ℚ}
    (hd : doubleDen x y ≠ 0)
    (hE : y ^ 2 + x * y + y = x ^ 3 - x ^ 2 - x - 14) :
    addX X017 x x (slope X017 x x y y) =
      doubleXNum x / doubleDen x y ^ 2 := by
  have hneg : y ≠ negY X017 x y := by
    intro h
    apply hd
    simp [doubleDen, negY] at h ⊢
    linarith
  have hslope :
      slope X017 x x y y =
        (3 * x ^ 2 - 2 * x - 1 - y) / doubleDen x y := by
    rw [slope_of_Y_ne rfl hneg]
    simp [doubleDen, negY]
    ring
  rw [hslope]
  unfold addX doubleXNum
  field_simp [hd]
  field_simp [hd]
  unfold doubleDen
  linear_combination (-8 * x + 3) * hE

/-- The tangent formula for the vertical coordinate has denominator
`doubleDen³`. -/
theorem doubleY_formula {x y : ℚ}
    (hd : doubleDen x y ≠ 0)
    (hE : y ^ 2 + x * y + y = x ^ 3 - x ^ 2 - x - 14) :
    addY X017 x x y (slope X017 x x y y) =
      doubleYNum x y / doubleDen x y ^ 3 := by
  have hneg : y ≠ negY X017 x y := by
    intro h
    apply hd
    simp [doubleDen, negY] at h ⊢
    linarith
  have hslope :
      slope X017 x x y y =
        (3 * x ^ 2 - 2 * x - 1 - y) / doubleDen x y := by
    rw [slope_of_Y_ne rfl hneg]
    simp [doubleDen, negY]
    ring
  rw [hslope]
  unfold addY negAddY negY addX doubleYNum
  simp
  field_simp [hd]
  unfold doubleDen
  linear_combination
    (28 * x ^ 3 - 19 * x ^ 2 - x - 8 * y ^ 2 - 15 * y + 106) * hE

private theorem doubleXNum_val
    {x y : ℚ} {k : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 2 x = -2 * k) :
    padicValRat 2 (doubleXNum x) = -8 * k := by
  have hshape :
      doubleXNum x = x ^ 4 + [x ^ 2, 110 * x, (-41 : ℚ)].sum := by
    simp [doubleXNum]
    ring
  rw [hshape, val_add_list_eq (q := x ^ 4)]
  · rw [padicValRat.pow_of_ne_zero hx, hvx]
    ring
  · exact pow_ne_zero 4 hx
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · have hval2 : padicValRat 2 (x ^ 2) = -4 * k := by
        rw [padicValRat.pow_of_ne_zero hx, hvx]
        ring
      have hval4 : padicValRat 2 (x ^ 4) = -8 * k := by
        rw [padicValRat.pow_of_ne_zero hx, hvx]
        ring
      rw [hval4, hval2]
      omega
    · have hge := val_monomial_ge hx hy 110 (by norm_num) 1 0
      rw [padicValRat.pow_of_ne_zero hx, hvx]
      norm_num at hge ⊢
      omega
    · have hge := val_int_nonneg (-41)
      rw [padicValRat.pow_of_ne_zero hx, hvx]
      norm_num at hge ⊢
      omega

private theorem doubleYNum_val
    {x y : ℚ} {k : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 2 x = -2 * k)
    (hvy : padicValRat 2 y = -3 * k) :
    padicValRat 2 (doubleYNum x y) = -12 * k := by
  let l : List ℚ :=
    [-2 * x ^ 5, -5 * x ^ 4, -276 * x ^ 3, 152 * x ^ 2, -95 * x,
      (-1 : ℚ) * x ^ 4 * y, -4 * x ^ 3 * y, 2 * x ^ 2 * y,
      -108 * x * y, 96 * y, (-1485 : ℚ)]
  have hshape : doubleYNum x y = x ^ 6 + l.sum := by
    simp [doubleYNum, l]
    ring
  rw [hshape, val_add_list_eq (q := x ^ 6)]
  · rw [padicValRat.pow_of_ne_zero hx, hvx]
    ring
  · exact pow_ne_zero 6 hx
  · intro a ha
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals rw [padicValRat.pow_of_ne_zero hx, hvx]
    · have hge := val_monomial_ge hx hy (-2) (by norm_num) 5 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-5) (by norm_num) 4 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-276) (by norm_num) 3 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy 152 (by norm_num) 2 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-95) (by norm_num) 1 0
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-1) (by norm_num) 4 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-4) (by norm_num) 3 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy 2 (by norm_num) 2 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy (-108) (by norm_num) 1 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_monomial_ge hx hy 96 (by norm_num) 0 1
      rw [hvx, hvy] at hge
      norm_num at hge ⊢
      omega
    · have hge := val_int_nonneg (-1485)
      norm_num at hge ⊢
      omega

/-! ## Formal levels and doubling -/

/-- A point lies in the two-adic formal kernel when its affine valuations are
`(-2k,-3k)` for some positive level `k`. -/
def FormalAtTwo : Point X017 → Prop
  | .zero => True
  | .some x y _ =>
      ∃ k : ℤ, 0 < k ∧
        padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k

/-- The exact positive level of a nonzero formal point. -/
def FormalLevel : Point X017 → ℤ → Prop
  | .zero, _ => False
  | .some x y _, k =>
      0 < k ∧ padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k

/-- A formal point is either infinity or a nonzero point with an exact
positive level. -/
theorem formalAtTwo_iff (P : Point X017) :
    FormalAtTwo P ↔ P = 0 ∨ ∃ k : ℤ, FormalLevel P k := by
  cases P with
  | zero =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        trivial
  | some x y h =>
      simp only [FormalAtTwo, FormalLevel, Point.some_ne_zero, false_or]

/-- Doubling either reaches infinity or raises the formal level by at least
one.  This is the explicit `v₂([2]z) ≥ v₂(z)+1` estimate. -/
theorem formalLevel_double {P : Point X017} {k : ℤ}
    (hP : FormalLevel P k) :
    2 • P = 0 ∨
      ∃ k' : ℤ, k + 1 ≤ k' ∧ FormalLevel (2 • P) k' := by
  cases P with
  | zero => simp [FormalLevel] at hP
  | some x y h =>
      rcases hP with ⟨hk, hvx, hvy⟩
      have hx : x ≠ 0 := by
        intro hx0
        rw [hx0, padicValRat.zero] at hvx
        omega
      have hy : y ≠ 0 := by
        intro hy0
        rw [hy0, padicValRat.zero] at hvy
        omega
      by_cases hd : doubleDen x y = 0
      · left
        rw [two_nsmul]
        apply Point.add_self_of_Y_eq
        simp [doubleDen, negY] at hd ⊢
        linarith
      · have hv2y : padicValRat 2 (2 * y) = 1 - 3 * k := by
          have hv2 : padicValRat 2 (2 : ℚ) = 1 :=
            padicValRat.self (by norm_num : 1 < 2)
          rw [padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hy, hv2, hvy]
          ring
        have hvfirst :
            1 - 3 * k ≤ padicValRat 2 (2 * y + x) := by
          by_cases hfirst : 2 * y + x = 0
          · rw [hfirst, padicValRat.zero]
            omega
          · have hmin := padicValRat.min_le_padicValRat_add (p := 2)
              (q := 2 * y) (r := x) hfirst
            rw [hv2y, hvx, min_eq_left (by omega)] at hmin
            exact hmin
        have hvdenLower :
            1 - 3 * k ≤ padicValRat 2 (doubleDen x y) := by
          have hmin := padicValRat.min_le_padicValRat_add (p := 2)
            (q := 2 * y + x) (r := 1)
            (by simpa [doubleDen] using hd)
          rw [padicValRat.one] at hmin
          have hlower :
              1 - 3 * k ≤ min (padicValRat 2 (2 * y + x)) 0 :=
            le_min hvfirst (by omega)
          exact hlower.trans (by simpa [doubleDen] using hmin)
        let k' : ℤ := 4 * k + padicValRat 2 (doubleDen x y)
        have hkstep : k + 1 ≤ k' := by
          dsimp [k']
          omega
        have hk' : 0 < k' := by omega
        have hvN := doubleXNum_val hx hy hk hvx
        have hvY := doubleYNum_val hx hy hk hvx hvy
        have hN : doubleXNum x ≠ 0 := by
          intro hzero
          rw [hzero, padicValRat.zero] at hvN
          omega
        have hY : doubleYNum x y ≠ 0 := by
          intro hzero
          rw [hzero, padicValRat.zero] at hvY
          omega
        have hE := (X017_equation_iff x y).mp h.left
        have hxform := doubleX_formula hd hE
        have hyform := doubleY_formula hd hE
        have hvx2 :
            padicValRat 2 (addX X017 x x (slope X017 x x y y)) =
              -2 * k' := by
          rw [hxform, padicValRat.div hN (pow_ne_zero 2 hd), hvN,
            padicValRat.pow_of_ne_zero hd]
          dsimp [k']
          ring
        have hvy2 :
            padicValRat 2 (addY X017 x x y (slope X017 x x y y)) =
              -3 * k' := by
          rw [hyform, padicValRat.div hY (pow_ne_zero 3 hd), hvY,
            padicValRat.pow_of_ne_zero hd]
          dsimp [k']
          ring
        right
        refine ⟨k', hkstep, ?_⟩
        have hneg : y ≠ negY X017 x y := by
          intro heq
          apply hd
          simp [doubleDen, negY] at heq ⊢
          linarith
        rw [two_nsmul, Point.add_self_of_Y_ne hneg]
        exact ⟨hk', hvx2, hvy2⟩

/-- Doubling preserves the two-adic formal kernel. -/
theorem formalAtTwo_double {P : Point X017}
    (hP : FormalAtTwo P) : FormalAtTwo (2 • P) := by
  rw [formalAtTwo_iff] at hP ⊢
  rcases hP with rfl | ⟨k, hk⟩
  · simp
  · rcases formalLevel_double hk with hzero | ⟨k', _, hk'⟩
    · exact Or.inl hzero
    · exact Or.inr ⟨k', hk'⟩

/-! ## Integral-or-formal dichotomy -/

/-- Good reduction at two gives the usual valuation dichotomy: an affine
rational point has two-integral coordinates, or it belongs to the formal
kernel with valuations `(-2k,-3k)`. -/
theorem formal_or_integral (P : Point X017) :
    FormalAtTwo P ∨
      match P with
      | .zero => True
      | .some x y _ => 0 ≤ padicValRat 2 x ∧ 0 ≤ padicValRat 2 y := by
  cases P with
  | zero => exact Or.inl trivial
  | some x y h =>
      have hE := (X017_equation_iff x y).mp h.left
      let vx := padicValRat 2 x
      let vy := padicValRat 2 y
      by_cases hxint : 0 ≤ vx
      · right
        refine ⟨hxint, ?_⟩
        by_contra hyint
        have hvyneg : vy < 0 := lt_of_not_ge hyint
        have hy : y ≠ 0 := by
          intro hy0
          dsimp [vy] at hvyneg
          rw [hy0, padicValRat.zero] at hvyneg
          omega
        let l : List ℚ :=
          [x * y, (1 : ℚ) * y, -(x ^ 3), x ^ 2,
            (1 : ℚ) * x, (14 : ℚ)]
        have hshape : y ^ 2 + l.sum = 0 := by
          simp [l]
          linarith
        have hlead : padicValRat 2 (y ^ 2) = 2 * vy := by
          rw [padicValRat.pow_of_ne_zero hy]
          rfl
        have hgt :
            ∀ a ∈ l, padicValRat 2 (y ^ 2) < padicValRat 2 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
          · by_cases hx0 : x = 0
            · rw [hx0, zero_mul, padicValRat.zero, hlead]
              omega
            · rw [padicValRat.mul hx0 hy, hlead]
              dsimp [vx, vy] at hxint hvyneg ⊢
              omega
          · rw [one_mul, hlead]
            dsimp [vy] at hvyneg ⊢
            omega
          · by_cases hx0 : x = 0
            · rw [hx0, zero_pow (by norm_num : 3 ≠ 0), neg_zero,
                padicValRat.zero, hlead]
              omega
            · rw [padicValRat.neg, padicValRat.pow_of_ne_zero hx0, hlead]
              dsimp [vx] at hxint ⊢
              omega
          · by_cases hx0 : x = 0
            · rw [hx0, zero_pow (by norm_num : 2 ≠ 0),
                padicValRat.zero, hlead]
              omega
            · rw [padicValRat.pow_of_ne_zero hx0, hlead]
              dsimp [vx] at hxint ⊢
              omega
          · rw [one_mul]
            by_cases hx0 : x = 0
            · rw [hx0, padicValRat.zero, hlead]
              omega
            · rw [hlead]
              dsimp [vx] at hxint ⊢
              omega
          · have hge := val_int_nonneg 14
            rw [hlead]
            norm_num at hge ⊢
            omega
        have hval := val_add_list_eq l (pow_ne_zero 2 hy) hgt
        rw [hshape, padicValRat.zero, hlead] at hval
        omega
      · have hvxneg : vx < 0 := lt_of_not_ge hxint
        have hx : x ≠ 0 := by
          intro hx0
          dsimp [vx] at hvxneg
          rw [hx0, padicValRat.zero] at hvxneg
          omega
        have hvylt : vy < vx := by
          by_contra hnot
          have hvxley : vx ≤ vy := le_of_not_gt hnot
          let l : List ℚ :=
            [y ^ 2, x * y, (1 : ℚ) * y, x ^ 2,
              (1 : ℚ) * x, (14 : ℚ)]
          have hshape : -(x ^ 3) + l.sum = 0 := by
            simp [l]
            linarith
          have hlead : padicValRat 2 (-(x ^ 3)) = 3 * vx := by
            rw [padicValRat.neg, padicValRat.pow_of_ne_zero hx]
            rfl
          have hgt :
              ∀ a ∈ l, padicValRat 2 (-(x ^ 3)) < padicValRat 2 a := by
            intro a ha
            simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
            · by_cases hy0 : y = 0
              · rw [hy0, zero_pow (by norm_num : 2 ≠ 0),
                  padicValRat.zero, hlead]
                omega
              · rw [padicValRat.pow_of_ne_zero hy0, hlead]
                dsimp [vx, vy] at hvxneg hvxley ⊢
                omega
            · by_cases hy0 : y = 0
              · rw [hy0, mul_zero, padicValRat.zero, hlead]
                omega
              · rw [padicValRat.mul hx hy0, hlead]
                dsimp [vx, vy] at hvxneg hvxley ⊢
                omega
            · rw [one_mul, hlead]
              dsimp [vx, vy] at hvxneg hvxley ⊢
              omega
            · rw [hlead, padicValRat.pow_of_ne_zero hx]
              dsimp [vx] at hvxneg ⊢
              omega
            · rw [one_mul, hlead]
              dsimp [vx] at hvxneg ⊢
              omega
            · have hge := val_int_nonneg 14
              rw [hlead]
              norm_num at hge ⊢
              omega
          have hval :=
            val_add_list_eq l (neg_ne_zero.mpr (pow_ne_zero 3 hx)) hgt
          rw [hshape, padicValRat.zero, hlead] at hval
          omega
        have hy : y ≠ 0 := by
          intro hy0
          dsimp [vx, vy] at hvylt
          rw [hy0, padicValRat.zero] at hvylt
          omega
        let lleft : List ℚ := [x * y, y]
        have hleftshape :
            y ^ 2 + lleft.sum = y ^ 2 + x * y + y := by
          simp [lleft]
          ring
        have hleftgt :
            ∀ a ∈ lleft, padicValRat 2 (y ^ 2) < padicValRat 2 a := by
          intro a ha
          simp only [lleft, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl
          · rw [padicValRat.pow_of_ne_zero hy, padicValRat.mul hx hy]
            dsimp [vx, vy] at hvylt ⊢
            omega
          · rw [padicValRat.pow_of_ne_zero hy]
            dsimp [vy] at hvylt ⊢
            omega
        have hvleft0 :=
          val_add_list_eq lleft (pow_ne_zero 2 hy) hleftgt
        have hvleft :
            padicValRat 2 (y ^ 2 + x * y + y) = 2 * vy := by
          rw [← hleftshape, hvleft0, padicValRat.pow_of_ne_zero hy]
          rfl
        let lright : List ℚ := [-(x ^ 2), -x, (-14 : ℚ)]
        have hrightshape :
            x ^ 3 + lright.sum = x ^ 3 - x ^ 2 - x - 14 := by
          simp [lright]
          ring
        have hrightgt :
            ∀ a ∈ lright, padicValRat 2 (x ^ 3) < padicValRat 2 a := by
          intro a ha
          simp only [lright, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl
          · rw [padicValRat.neg, padicValRat.pow_of_ne_zero hx,
              padicValRat.pow_of_ne_zero hx]
            dsimp [vx] at hvxneg ⊢
            omega
          · rw [padicValRat.neg, padicValRat.pow_of_ne_zero hx]
            dsimp [vx] at hvxneg ⊢
            omega
          · have hge := val_int_nonneg (-14)
            rw [padicValRat.pow_of_ne_zero hx]
            dsimp [vx] at hvxneg hge ⊢
            omega
        have hvright0 :=
          val_add_list_eq lright (pow_ne_zero 3 hx) hrightgt
        have hvright :
            padicValRat 2 (x ^ 3 - x ^ 2 - x - 14) = 3 * vx := by
          rw [← hrightshape, hvright0, padicValRat.pow_of_ne_zero hx]
          rfl
        have hvrel : 2 * vy = 3 * vx := by
          calc
            2 * vy = padicValRat 2 (y ^ 2 + x * y + y) := hvleft.symm
            _ = padicValRat 2 (x ^ 3 - x ^ 2 - x - 14) := by rw [hE]
            _ = 3 * vx := hvright
        left
        change ∃ k : ℤ, 0 < k ∧
          padicValRat 2 x = -2 * k ∧ padicValRat 2 y = -3 * k
        refine ⟨vx - vy, by omega, ?_, ?_⟩
        · dsimp [vx]
          omega
        · dsimp [vy]
          omega

end

end MazurProof.X017FormalTwoCore

end

-- ===== FLT.Assumptions.MazurProof.X017FormalTwoReduction =====
section
/-!
# Mod-two entry into the X₀(17) formal kernel

The integral model has four points on its good fibre at two.  Instead of
constructing a general reduction homomorphism, this file follows the explicit
duplication formulas.  For integral coordinates, the residue of `x` is zero
or one:

* residue one makes the first double a formal point;
* residue zero makes the first double integral with `x`-residue one, so the
  second double is formal.

Thus four times every rational point belongs to the two-adic formal kernel.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017FormalTwoReduction

open WeierstrassCurve.Affine
open MazurProof.X017FormalTwoCore
open MazurProof.X017Model

noncomputable section

/-! ## Integral rational numbers and their residues -/

/-- Regard a rational number of nonnegative two-adic valuation as a two-adic
integer. -/
private noncomputable def ratPadicInt (q : ℚ)
    (hq : 0 ≤ padicValRat 2 q) : ℤ_[2] :=
  ⟨(q : ℚ_[2]), by
    rw [Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast]
    exact_mod_cast hq⟩

private theorem zmod2_nonzero_eq_one (z : ZMod 2) (hz : z ≠ 0) : z = 1 := by
  fin_cases z
  · exact (hz rfl).elim
  · rfl

private theorem ratPadicInt_red_eq_one_of_val_zero
    {q : ℚ} (hq : q ≠ 0) (hv : padicValRat 2 q = 0) :
    PadicInt.toZMod (ratPadicInt q (by omega)) = 1 := by
  apply zmod2_nonzero_eq_one
  intro hz0
  have hm : ratPadicInt q (by omega) ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
    rw [← PadicInt.ker_toZMod]
    exact hz0
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd] at hm
  change ‖((ratPadicInt q (by omega) : ℤ_[2]) : ℚ_[2])‖ < 1 at hm
  change ‖(q : ℚ_[2])‖ < 1 at hm
  have hqcast : (q : ℚ_[2]) ≠ 0 := by exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, hv] at hm
  norm_num at hm

private theorem ratPadicInt_red_eq_zero_of_val_pos
    {q : ℚ} (hq : q ≠ 0) (hv : 0 < padicValRat 2 q) :
    PadicInt.toZMod (ratPadicInt q (le_of_lt hv)) = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd]
  change ‖(q : ℚ_[2])‖ < 1
  have hqcast : (q : ℚ_[2]) ≠ 0 := by exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, ← zpow_zero (2 : ℝ)]
  exact (zpow_lt_zpow_iff_right₀ (a := (2 : ℝ))
    (by norm_num : (1 : ℝ) < 2)).2 (by omega)

private theorem val_pos_of_red_zero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 2 q)
    (hred : PadicInt.toZMod (ratPadicInt q hqi) = 0) :
    0 < padicValRat 2 q := by
  by_contra hnot
  have hv0 : padicValRat 2 q = 0 := by omega
  have hone := ratPadicInt_red_eq_one_of_val_zero hq hv0
  have heq : ratPadicInt q hqi = ratPadicInt q (by omega) := by
    apply Subtype.ext
    rfl
  rw [heq, hone] at hred
  norm_num at hred

private theorem val_zero_of_red_nonzero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 2 q)
    (hred : PadicInt.toZMod (ratPadicInt q hqi) ≠ 0) :
    padicValRat 2 q = 0 := by
  by_contra hne
  have hvpos : 0 < padicValRat 2 q := lt_of_le_of_ne hqi (Ne.symm hne)
  have hzero := ratPadicInt_red_eq_zero_of_val_pos hq hvpos
  have heq : ratPadicInt q hqi = ratPadicInt q (le_of_lt hvpos) := by
    apply Subtype.ext
    rfl
  exact hred (by rw [heq, hzero])

/-! ## Duplication polynomials over the two-adic integers -/

private noncomputable def doubleDenPadic (x y : ℤ_[2]) : ℤ_[2] :=
  2 * y + x + 1

private noncomputable def doubleXNumPadic (x : ℤ_[2]) : ℤ_[2] :=
  x ^ 4 + x ^ 2 + 110 * x - 41

private noncomputable def doubleYNumPadic (x y : ℤ_[2]) : ℤ_[2] :=
  x ^ 6 - 2 * x ^ 5 - 5 * x ^ 4 - 276 * x ^ 3 + 152 * x ^ 2 -
    95 * x + y * (-x ^ 4 - 4 * x ^ 3 + 2 * x ^ 2 - 108 * x + 96) - 1485

private theorem doubleDenPadic_coe (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    ((doubleDenPadic (ratPadicInt x hx) (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2]) =
      ((doubleDen x y : ℚ) : ℚ_[2]) := by
  change 2 * (y : ℚ_[2]) + (x : ℚ_[2]) + 1 =
    (((2 * y + x + 1 : ℚ)) : ℚ_[2])
  push_cast
  ring

private theorem doubleXNumPadic_coe (x : ℚ)
    (hx : 0 ≤ padicValRat 2 x) :
    ((doubleXNumPadic (ratPadicInt x hx) : ℤ_[2]) : ℚ_[2]) =
      ((doubleXNum x : ℚ) : ℚ_[2]) := by
  change (x : ℚ_[2]) ^ 4 + (x : ℚ_[2]) ^ 2 + 110 * (x : ℚ_[2]) - 41 =
    (((x ^ 4 + x ^ 2 + 110 * x - 41 : ℚ)) : ℚ_[2])
  push_cast
  ring

private theorem doubleYNumPadic_coe (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    ((doubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2]) =
      ((doubleYNum x y : ℚ) : ℚ_[2]) := by
  change
    (x : ℚ_[2]) ^ 6 - 2 * (x : ℚ_[2]) ^ 5 - 5 * (x : ℚ_[2]) ^ 4 -
        276 * (x : ℚ_[2]) ^ 3 + 152 * (x : ℚ_[2]) ^ 2 - 95 * (x : ℚ_[2]) +
        (y : ℚ_[2]) * (-(x : ℚ_[2]) ^ 4 - 4 * (x : ℚ_[2]) ^ 3 +
          2 * (x : ℚ_[2]) ^ 2 - 108 * (x : ℚ_[2]) + 96) - 1485 =
      (((doubleYNum x y : ℚ)) : ℚ_[2])
  rfl

private theorem doubleDen_integral (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    0 ≤ padicValRat 2 (doubleDen x y) := by
  have hnorm := (doubleDenPadic (ratPadicInt x hx) (ratPadicInt y hy)).2
  change ‖((doubleDenPadic (ratPadicInt x hx)
    (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 at hnorm
  rw [doubleDenPadic_coe x y hx hy, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_ratCast] at hnorm
  exact_mod_cast hnorm

private theorem doubleXNum_integral (x : ℚ)
    (hx : 0 ≤ padicValRat 2 x) :
    0 ≤ padicValRat 2 (doubleXNum x) := by
  have hnorm := (doubleXNumPadic (ratPadicInt x hx)).2
  change ‖((doubleXNumPadic (ratPadicInt x hx) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 at hnorm
  rw [doubleXNumPadic_coe x hx, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_ratCast] at hnorm
  exact_mod_cast hnorm

private theorem doubleYNum_integral (x y : ℚ)
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    0 ≤ padicValRat 2 (doubleYNum x y) := by
  have hnorm := (doubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy)).2
  change ‖((doubleYNumPadic (ratPadicInt x hx)
    (ratPadicInt y hy) : ℤ_[2]) : ℚ_[2])‖ ≤ 1 at hnorm
  rw [doubleYNumPadic_coe x y hx hy, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_ratCast] at hnorm
  exact_mod_cast hnorm

private theorem padicInt_equation {x y : ℚ}
    (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y)
    (hE : y ^ 2 + x * y + y = x ^ 3 - x ^ 2 - x - 14) :
    (ratPadicInt y hy) ^ 2 + ratPadicInt x hx * ratPadicInt y hy +
        ratPadicInt y hy =
      (ratPadicInt x hx) ^ 3 - (ratPadicInt x hx) ^ 2 -
        ratPadicInt x hx - 14 := by
  apply Subtype.ext
  change (y : ℚ_[2]) ^ 2 + (x : ℚ_[2]) * (y : ℚ_[2]) + (y : ℚ_[2]) =
    (x : ℚ_[2]) ^ 3 - (x : ℚ_[2]) ^ 2 - (x : ℚ_[2]) - 14
  exact_mod_cast hE

/-! ## Kernel-checked residue identities -/

private theorem doubleDenPadic_red_zero
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 0) :
    PadicInt.toZMod (doubleDenPadic z w) = 1 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [doubleDenPadic, map_add, map_mul, map_ofNat, hz, htwo]

private theorem doubleDenPadic_red_one
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 1) :
    PadicInt.toZMod (doubleDenPadic z w) = 0 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [doubleDenPadic, map_add, map_mul, map_ofNat, hz, htwo]
  decide

private theorem doubleXNumPadic_red_zero
    {z : ℤ_[2]} (hz : PadicInt.toZMod z = 0) :
    PadicInt.toZMod (doubleXNumPadic z) = 1 := by
  simp [doubleXNumPadic, map_add, map_sub, map_mul, map_pow,
    map_ofNat, hz]
  decide

private theorem doubleXNumPadic_red_one
    {z : ℤ_[2]} (hz : PadicInt.toZMod z = 1) :
    PadicInt.toZMod (doubleXNumPadic z) = 1 := by
  simp [doubleXNumPadic, map_add, map_sub, map_mul, map_pow,
    map_ofNat, hz]
  decide

private theorem doubleYNumPadic_red_zero
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 0) :
    PadicInt.toZMod (doubleYNumPadic z w) = 1 := by
  simp [doubleYNumPadic, map_add, map_sub, map_mul, map_pow,
    map_ofNat, hz]
  have h96 : (96 : ZMod 2) = 0 := by decide
  have hm1485 : (-1485 : ZMod 2) = 1 := by decide
  rw [h96, mul_zero, zero_sub]
  exact hm1485

private theorem doubleYNumPadic_red_one_one
    {z w : ℤ_[2]} (hz : PadicInt.toZMod z = 1)
    (hw : PadicInt.toZMod w = 1) :
    PadicInt.toZMod (doubleYNumPadic z w) = 1 := by
  simp [doubleYNumPadic, map_add, map_sub, map_mul, map_pow,
    map_ofNat, hz, hw]
  decide

private theorem ratPadicInt_doubleDen
    (x y : ℚ) (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    ratPadicInt (doubleDen x y) (doubleDen_integral x y hx hy) =
      doubleDenPadic (ratPadicInt x hx) (ratPadicInt y hy) := by
  apply Subtype.ext
  exact (doubleDenPadic_coe x y hx hy).symm

private theorem ratPadicInt_doubleXNum
    (x : ℚ) (hx : 0 ≤ padicValRat 2 x) :
    ratPadicInt (doubleXNum x) (doubleXNum_integral x hx) =
      doubleXNumPadic (ratPadicInt x hx) := by
  apply Subtype.ext
  exact (doubleXNumPadic_coe x hx).symm

private theorem ratPadicInt_doubleYNum
    (x y : ℚ) (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y) :
    ratPadicInt (doubleYNum x y) (doubleYNum_integral x y hx hy) =
      doubleYNumPadic (ratPadicInt x hx) (ratPadicInt y hy) := by
  apply Subtype.ext
  exact (doubleYNumPadic_coe x y hx hy).symm

private theorem y_red_one_of_x_red_one
    {x y : ℚ} (hx : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y)
    (hE : y ^ 2 + x * y + y = x ^ 3 - x ^ 2 - x - 14)
    (hxred : PadicInt.toZMod (ratPadicInt x hx) = 1) :
    PadicInt.toZMod (ratPadicInt y hy) = 1 := by
  have heq := congrArg PadicInt.toZMod (padicInt_equation hx hy hE)
  simp [map_add, map_sub, map_mul, map_pow, map_ofNat, hxred] at heq
  by_cases hyred : PadicInt.toZMod (ratPadicInt y hy) = 0
  · rw [hyred] at heq
    have hbad : (0 : ZMod 2) ≠ 1 - 14 := by decide
    exact (hbad (by simpa using heq)).elim
  · exact zmod2_nonzero_eq_one _ hyred

private theorem rat_ne_zero_of_red_one
    {q : ℚ} (hq : 0 ≤ padicValRat 2 q)
    (hred : PadicInt.toZMod (ratPadicInt q hq) = 1) :
    q ≠ 0 := by
  intro hzero
  have hz : ratPadicInt q hq = 0 := by
    apply Subtype.ext
    change (q : ℚ_[2]) = 0
    simp [hzero]
  rw [hz, map_zero] at hred
  norm_num at hred

/-! ## Integral points enter the formal kernel after at most two doublings -/

private theorem double_formal_of_integral_x_unit
    {x y : ℚ} {h : Nonsingular X017 x y}
    (hxn : x ≠ 0) (hx : padicValRat 2 x = 0)
    (hy : 0 ≤ padicValRat 2 y) :
    FormalAtTwo (2 • Point.some x y h) := by
  have hx0 : 0 ≤ padicValRat 2 x := by omega
  have hE := (X017_equation_iff x y).mp h.left
  have hxred := ratPadicInt_red_eq_one_of_val_zero hxn hx
  have hyred := y_red_one_of_x_red_one hx0 hy hE hxred
  have hDi := doubleDen_integral x y hx0 hy
  have hDred :
      PadicInt.toZMod (ratPadicInt (doubleDen x y) hDi) = 0 := by
    rw [ratPadicInt_doubleDen x y hx0 hy]
    exact doubleDenPadic_red_one hxred
  by_cases hd : doubleDen x y = 0
  · rw [two_nsmul]
    have hYeq : y = negY X017 x y := by
      simp [doubleDen, negY] at hd ⊢
      linarith
    rw [Point.add_self_of_Y_eq hYeq]
    trivial
  · have hvd : 0 < padicValRat 2 (doubleDen x y) :=
      val_pos_of_red_zero hd hDi hDred
    have hNi := doubleXNum_integral x hx0
    have hYi := doubleYNum_integral x y hx0 hy
    have hNred :
        PadicInt.toZMod (ratPadicInt (doubleXNum x) hNi) = 1 := by
      rw [ratPadicInt_doubleXNum x hx0]
      exact doubleXNumPadic_red_one hxred
    have hYred :
        PadicInt.toZMod (ratPadicInt (doubleYNum x y) hYi) = 1 := by
      rw [ratPadicInt_doubleYNum x y hx0 hy]
      exact doubleYNumPadic_red_one_one hxred hyred
    have hN : doubleXNum x ≠ 0 :=
      rat_ne_zero_of_red_one hNi hNred
    have hY : doubleYNum x y ≠ 0 :=
      rat_ne_zero_of_red_one hYi hYred
    have hvN : padicValRat 2 (doubleXNum x) = 0 :=
      val_zero_of_red_nonzero hN hNi (by rw [hNred]; norm_num)
    have hvY : padicValRat 2 (doubleYNum x y) = 0 :=
      val_zero_of_red_nonzero hY hYi (by rw [hYred]; norm_num)
    have hneg : y ≠ negY X017 x y := by
      intro heq
      apply hd
      simp [doubleDen, negY] at heq ⊢
      linarith
    rw [two_nsmul, Point.add_self_of_Y_ne hneg]
    refine ⟨padicValRat 2 (doubleDen x y), hvd, ?_, ?_⟩
    · rw [doubleX_formula hd hE,
        padicValRat.div hN (pow_ne_zero 2 hd), hvN,
        padicValRat.pow_of_ne_zero hd]
      ring
    · rw [doubleY_formula hd hE,
        padicValRat.div hY (pow_ne_zero 3 hd), hvY,
        padicValRat.pow_of_ne_zero hd]
      ring

private theorem four_formal_of_integral_x_red_zero
    {x y : ℚ} {h : Nonsingular X017 x y}
    (hx0 : 0 ≤ padicValRat 2 x) (hy : 0 ≤ padicValRat 2 y)
    (hxred : PadicInt.toZMod (ratPadicInt x hx0) = 0) :
    FormalAtTwo (4 • Point.some x y h) := by
  have hE := (X017_equation_iff x y).mp h.left
  have hDi := doubleDen_integral x y hx0 hy
  have hDred :
      PadicInt.toZMod (ratPadicInt (doubleDen x y) hDi) = 1 := by
    rw [ratPadicInt_doubleDen x y hx0 hy]
    exact doubleDenPadic_red_zero hxred
  have hd : doubleDen x y ≠ 0 :=
    rat_ne_zero_of_red_one hDi hDred
  have hvd : padicValRat 2 (doubleDen x y) = 0 :=
    val_zero_of_red_nonzero hd hDi (by rw [hDred]; norm_num)
  have hNi := doubleXNum_integral x hx0
  have hYi := doubleYNum_integral x y hx0 hy
  have hNred :
      PadicInt.toZMod (ratPadicInt (doubleXNum x) hNi) = 1 := by
    rw [ratPadicInt_doubleXNum x hx0]
    exact doubleXNumPadic_red_zero hxred
  have hYred :
      PadicInt.toZMod (ratPadicInt (doubleYNum x y) hYi) = 1 := by
    rw [ratPadicInt_doubleYNum x y hx0 hy]
    exact doubleYNumPadic_red_zero hxred
  have hN : doubleXNum x ≠ 0 :=
    rat_ne_zero_of_red_one hNi hNred
  have hY : doubleYNum x y ≠ 0 :=
    rat_ne_zero_of_red_one hYi hYred
  have hvN : padicValRat 2 (doubleXNum x) = 0 :=
    val_zero_of_red_nonzero hN hNi (by rw [hNred]; norm_num)
  have hvY : padicValRat 2 (doubleYNum x y) = 0 :=
    val_zero_of_red_nonzero hY hYi (by rw [hYred]; norm_num)
  have hneg : y ≠ negY X017 x y := by
    intro heq
    apply hd
    simp [doubleDen, negY] at heq ⊢
    linarith
  have hfour :
      4 • Point.some x y h =
        2 • (Point.some x y h + Point.some x y h) := by
    rw [← two_nsmul]
    norm_num [← mul_nsmul]
  rw [hfour, Point.add_self_of_Y_ne hneg]
  have hx2ne : addX X017 x x (slope X017 x x y y) ≠ 0 := by
    rw [doubleX_formula hd hE]
    exact div_ne_zero hN (pow_ne_zero 2 hd)
  apply double_formal_of_integral_x_unit
  · exact hx2ne
  · rw [doubleX_formula hd hE,
      padicValRat.div hN (pow_ne_zero 2 hd),
      padicValRat.pow_of_ne_zero hd, hvN, hvd]
    norm_num
  · rw [doubleY_formula hd hE,
      padicValRat.div hY (pow_ne_zero 3 hd),
      padicValRat.pow_of_ne_zero hd, hvY, hvd]
    norm_num

/-- Four times every rational point on the good integral model belongs to
the two-adic formal kernel. -/
theorem four_nsmul_formal (P : Point X017) :
    FormalAtTwo (4 • P) := by
  rcases formal_or_integral P with hformal | hintegral
  · have h2 := formalAtTwo_double hformal
    have h4 := formalAtTwo_double h2
    rw [show 4 • P = 2 • (2 • P) by norm_num [← mul_nsmul]]
    exact h4
  · cases P with
    | zero => trivial
    | some x y h =>
        rcases hintegral with ⟨hx, hy⟩
        by_cases hxzero : x = 0
        · have hxred : PadicInt.toZMod (ratPadicInt x hx) = 0 := by
            have hxi : ratPadicInt x hx = 0 := by
              apply Subtype.ext
              change (x : ℚ_[2]) = 0
              simp [hxzero]
            rw [hxi, map_zero]
          exact four_formal_of_integral_x_red_zero hx hy hxred
        · by_cases hxunit : padicValRat 2 x = 0
          · have h2 :=
              double_formal_of_integral_x_unit (h := h) hxzero hxunit hy
            have h4 := formalAtTwo_double h2
            rw [show 4 • Point.some x y h =
                2 • (2 • Point.some x y h) by
                  norm_num [← mul_nsmul]]
            exact h4
          · have hxpos : 0 < padicValRat 2 x :=
              lt_of_le_of_ne hx (Ne.symm hxunit)
            have hxred :=
              ratPadicInt_red_eq_zero_of_val_pos hxzero hxpos
            exact four_formal_of_integral_x_red_zero hx hy hxred

/-! ## Separatedness of the formal filtration -/

private theorem formalLevel_unique {P : Point X017} {k l : ℤ}
    (hk : FormalLevel P k) (hl : FormalLevel P l) : k = l := by
  cases P with
  | zero => simp [FormalLevel] at hk
  | some x y h =>
      rcases hk with ⟨_, hxk, _⟩
      rcases hl with ⟨_, hxl, _⟩
      omega

/-- Repeated doubling either reaches infinity or raises the formal level by
at least the number of doublings. -/
theorem formalLevel_two_power {P : Point X017} {k : ℤ}
    (hP : FormalLevel P k) (n : ℕ) :
    (2 ^ n : ℕ) • P = 0 ∨
      ∃ k' : ℤ, k + n ≤ k' ∧
        FormalLevel ((2 ^ n : ℕ) • P) k' := by
  induction n with
  | zero =>
      right
      refine ⟨k, by simp, ?_⟩
      simpa using hP
  | succ n ih =>
      rcases ih with hzero | ⟨l, hkl, hl⟩
      · left
        rw [pow_succ', Nat.mul_comm, mul_nsmul, hzero, nsmul_zero]
      · rcases formalLevel_double hl with hzero | ⟨l', hll', hl'⟩
        · left
          rw [pow_succ', Nat.mul_comm, mul_nsmul]
          exact hzero
        · right
          refine ⟨l', ?_, ?_⟩
          · norm_num at hkl ⊢
            omega
          · rw [pow_succ', Nat.mul_comm, mul_nsmul]
            exact hl'

/-- A formal point divisible by every power of two through formal points is
zero.  Otherwise its fixed level would exceed itself after sufficiently many
doublings. -/
theorem formal_separated (P : Point X017)
    (hP : FormalAtTwo P)
    (hdiv : ∀ n : ℕ, ∃ Q : Point X017,
      FormalAtTwo Q ∧ P = (2 ^ n : ℕ) • Q) :
    P = 0 := by
  by_contra hP0
  have hlevelP : ∃ k : ℤ, FormalLevel P k := by
    rw [formalAtTwo_iff] at hP
    exact hP.resolve_left hP0
  obtain ⟨k, hk⟩ := hlevelP
  have hkpos : 0 < k := by
    cases P with
    | zero => exact (hP0 rfl).elim
    | some x y h => exact hk.1
  let n : ℕ := k.toNat + 1
  obtain ⟨Q, hQformal, hPQ⟩ := hdiv n
  have hQ0 : Q ≠ 0 := by
    intro hzero
    rw [hzero, nsmul_zero] at hPQ
    exact hP0 hPQ
  have hlevelQ : ∃ l : ℤ, FormalLevel Q l := by
    rw [formalAtTwo_iff] at hQformal
    exact hQformal.resolve_left hQ0
  obtain ⟨l, hl⟩ := hlevelQ
  have hlpos : 0 < l := by
    cases Q with
    | zero => simp [FormalLevel] at hl
    | some x y h => exact hl.1
  rcases formalLevel_two_power hl n with hzero | ⟨l', hbound, hl'⟩
  · exact hP0 (hPQ.trans hzero)
  · have hl'P : FormalLevel P l' := by
      rw [hPQ]
      exact hl'
    have heq : l' = k := formalLevel_unique hl'P hk
    have hkNat : (k.toNat : ℤ) = k :=
      Int.toNat_of_nonneg (le_of_lt hkpos)
    dsimp [n] at hbound
    norm_num [hkNat] at hbound
    omega

end

end MazurProof.X017FormalTwoReduction

end

-- ===== FLT.Assumptions.MazurProof.RationalPointsN15Descent =====
section
/-!
# First full-two-torsion descent layer for the order-15 curve

Scaling the curve from `RationalPointsN15C0` by `X = 4s`, `Y = 4v`
gives

`Y² = X(X+1)(X+16) = X³ + 17X² + 16X`.

This file carries out the elementary front end of a full `2`-descent:

* square-denominator normalization and an integral primitive model;
* pairwise gcd bounds for the three linear factors;
* extraction of the finite squareclasses of the `X` coordinate;
* the analogous squareclass computation on the `2`-isogenous curve
  `Y² = X³ - 34X² + 225X`;
* kernel-checked local exclusions of the remaining `2`- and `3`-supported
  squareclasses.

No rank or rational-point exhaustion statement is made here.
-/

namespace MazurProof.RationalPointsN15Descent



/-! ## Scaling and the two integral cubics -/

/-! ## Generic square-denominator normalization -/

private theorem nat_isSquare_of_isSquare_cube {n : ℕ} (hn : n ≠ 0)
    (h : IsSquare (n ^ 3)) : IsSquare n := by
  rcases h with ⟨c, hc⟩
  have hdvd : n ^ 2 ∣ c ^ 2 := ⟨n, by rw [sq c, ← hc]; ring⟩
  have hndvdc : n ∣ c := by
    rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
      Nat.ceilRoot_pow_self two_ne_zero] at hdvd
  obtain ⟨d, rfl⟩ := hndvdc
  exact ⟨d, mul_left_cancel₀ (pow_ne_zero 2 hn)
    (show n ^ 2 * n = n ^ 2 * (d * d) by
      calc
        n ^ 2 * n = n ^ 3 := by ring
        _ = n * d * (n * d) := hc
        _ = n ^ 2 * (d * d) := by ring)⟩

/-- The denominator of a monic cubic with zero constant term is the cube of
the denominator of its argument. -/
private theorem den_monic_cubic (a b : ℤ) (x : ℚ) :
    ((x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x).den : ℤ) =
      (x.den : ℤ) ^ 3 := by
  set A : ℤ := x.num
  set D : ℤ := (x.den : ℤ)
  have hDpos : (0 : ℤ) < D := by positivity
  have hDne : (D : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hDpos)
  have hred : IsCoprime A D := by
    rw [Int.isCoprime_iff_nat_coprime]
    simp only [A, D, Int.natAbs_natCast]
    exact x.reduced
  set N : ℤ := A ^ 3 + a * A ^ 2 * D + b * A * D ^ 2
  have hND : IsCoprime N D := by
    have h1 : IsCoprime (A ^ 3) D := hred.pow_left
    have h2 : IsCoprime
        (A ^ 3 + D * (a * A ^ 2 + b * A * D)) D :=
      h1.add_mul_left_left _
    convert h2 using 1
    ring
  have hND3 : IsCoprime N (D ^ 3) := hND.pow_right
  have hND3nat : Nat.Coprime N.natAbs (D ^ 3).natAbs :=
    Int.isCoprime_iff_nat_coprime.mp hND3
  have hrepr : x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x =
      (N : ℚ) / (D ^ 3 : ℚ) := by
    have hx : x = (A : ℚ) / (D : ℚ) := by
      simp only [A, D]
      push_cast
      exact (Rat.num_div_den x).symm
    rw [hx]
    field_simp [hDne]
    push_cast [N]
    ring
  rw [hrepr]
  exact_mod_cast Rat.den_div_eq_of_coprime (by positivity) hND3nat

theorem rat_denom_square_monic (a b : ℤ) (x y : ℚ)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :
    ∃ A B : ℤ, 0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 := by
  have hsq : IsSquare
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :=
    ⟨y, by rw [← h]; ring⟩
  have hdenSq : IsSquare
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x).den :=
    (Rat.isSquare_iff.mp hsq).2
  have hdenEq :
      (x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x).den = x.den ^ 3 := by
    exact_mod_cast den_monic_cubic a b x
  have hden3Sq : IsSquare (x.den ^ 3) := hdenEq ▸ hdenSq
  have hdenSq' : IsSquare x.den :=
    nat_isSquare_of_isSquare_cube x.den_ne_zero hden3Sq
  obtain ⟨B0, hB0⟩ := hdenSq'
  have hB0pos : 0 < B0 := by
    rcases Nat.eq_zero_or_pos B0 with hzero | hpos
    · simp [hzero] at hB0
    · exact hpos
  refine ⟨x.num, (B0 : ℤ), by exact_mod_cast hB0pos, ?_, ?_⟩
  · have hBdvd : B0 ∣ x.den := ⟨B0, hB0⟩
    have := x.reduced.coprime_dvd_right hBdvd
    simpa [Int.gcd, Int.natAbs_natCast] using this
  · calc
      x = (x.num : ℚ) / (x.den : ℚ) := by
        simpa using (Rat.num_div_den x).symm
      _ = (x.num : ℚ) / ((B0 : ℚ) ^ 2) := by
        rw [hB0]
        push_cast
        ring

/-- Denominator clearing for any monic cubic `y²=x³+ax²+bx`. -/
theorem integral_model_monic (a b : ℤ) (x y : ℚ)
    (h : y ^ 2 = x ^ 3 + (a : ℚ) * x ^ 2 + (b : ℚ) * x) :
    ∃ A B C : ℤ,
      0 < B ∧ Int.gcd A B = 1 ∧
      x = (A : ℚ) / (B : ℚ) ^ 2 ∧
      C ^ 2 = A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4) := by
  obtain ⟨A, B, hBpos, hcop, hx⟩ := rat_denom_square_monic a b x y h
  have hBne : (B : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hBpos)
  set N : ℤ := A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4)
  have hrat : (y * (B : ℚ) ^ 3) ^ 2 = (N : ℚ) := by
    rw [hx] at h
    push_cast [N] at h ⊢
    field_simp [hBne] at h ⊢
    nlinarith
  have hNsq : IsSquare (N : ℚ) :=
    ⟨y * (B : ℚ) ^ 3, by rw [← sq]; exact hrat.symm⟩
  rw [Rat.isSquare_intCast_iff] at hNsq
  obtain ⟨C, hC⟩ := hNsq
  refine ⟨A, B, C, hBpos, hcop, hx, ?_⟩
  rw [sq C]
  exact hC.symm

/-! ## Pairwise gcd bounds for the full-two-torsion factors -/

private theorem coprime_of_dvd_left {a b d : ℤ} (hab : IsCoprime a b)
    (hd : d ∣ a) : IsCoprime d b := by
  rcases hab with ⟨u, v, huv⟩
  rcases hd with ⟨k, rfl⟩
  exact ⟨u * k, v, by rw [← huv]; ring⟩

/-! ## Squarefree cores and finite squareclasses -/

/-- If `a*q` is a square and `d` is the squarefree core in
`a = r²*d`, then `d` divides `q`. -/
private theorem squarefree_core_dvd_other {a q c d r : ℕ}
    (ha0 : a ≠ 0) (hdecomp : r ^ 2 * d = a) (hd : Squarefree d)
    (hsq : c ^ 2 = a * q) : d ∣ q := by
  have hr0 : r ≠ 0 := by
    intro hr
    subst r
    simp at hdecomp
    exact ha0 hdecomp.symm
  have hr2dvd : r ^ 2 ∣ c ^ 2 := by
    refine ⟨d * q, ?_⟩
    rw [hsq, ← hdecomp]
    ring
  have hrdvd : r ∣ c := by
    rwa [Nat.dvd_pow_iff_ceilRoot_dvd two_ne_zero,
      Nat.ceilRoot_pow_self two_ne_zero] at hr2dvd
  obtain ⟨k, rfl⟩ := hrdvd
  have hk : k ^ 2 = d * q := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hr0)
    calc
      r ^ 2 * k ^ 2 = (r * k) ^ 2 := by ring
      _ = a * q := hsq
      _ = (r ^ 2 * d) * q := by rw [hdecomp]
      _ = r ^ 2 * (d * q) := by ring
  have hdk2 : d ∣ k ^ 2 := ⟨q, hk⟩
  have hdk : d ∣ k := (hd.dvd_pow_iff_dvd two_ne_zero).mp hdk2
  obtain ⟨l, rfl⟩ := hdk
  have hcancel : d * (d * l ^ 2) = d * q := by
    calc
      d * (d * l ^ 2) = (d * l) ^ 2 := by ring
      _ = d * q := hk
  have hq : d * l ^ 2 = q := mul_left_cancel₀ hd.ne_zero hcancel
  exact ⟨l ^ 2, hq.symm⟩

/-- In a primitive integral model
`C²=A(A²+aAB²+bB⁴)`, the squarefree core of `|A|` divides `|b|`. -/
theorem squarefree_core_dvd_cubic_coefficient
    {a b A B C : ℤ} {d r : ℕ}
    (hcop : Int.gcd A B = 1) (hA0 : A ≠ 0)
    (hmodel : C ^ 2 = A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4))
    (hdecomp : r ^ 2 * d = A.natAbs) (hd : Squarefree d) :
    d ∣ b.natAbs := by
  let Q : ℤ := A ^ 2 + a * A * B ^ 2 + b * B ^ 4
  have hAabs0 : A.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hA0
  have habs : C.natAbs ^ 2 = A.natAbs * Q.natAbs := by
    simpa [Q, Int.natAbs_pow, Int.natAbs_mul] using
      congrArg Int.natAbs hmodel
  have hdQ : d ∣ Q.natAbs :=
    squarefree_core_dvd_other hAabs0 hdecomp hd habs
  have hdA : d ∣ A.natAbs := by
    exact hdecomp ▸ dvd_mul_left d (r ^ 2)
  have hdAZ : (d : ℤ) ∣ A := Int.natCast_dvd.mpr hdA
  have hdQZ : (d : ℤ) ∣ Q := Int.natCast_dvd.mpr hdQ
  have hdbB4 : (d : ℤ) ∣ b * B ^ 4 := by
    rw [show b * B ^ 4 = Q - A * (A + a * B ^ 2) by
      simp only [Q]
      ring]
    exact dvd_sub hdQZ (dvd_mul_of_dvd_left hdAZ _)
  have hAB : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hdB4 : IsCoprime (d : ℤ) (B ^ 4) :=
    (coprime_of_dvd_left hAB hdAZ).pow_right
  have hdbZ : (d : ℤ) ∣ b := hdB4.dvd_of_dvd_mul_right hdbB4
  exact Int.natCast_dvd.mp hdbZ

/-- Finite squareclass extraction for the first coordinate of a primitive
monic-cubic model. -/
theorem first_coordinate_squareclass
    {a b A B C : ℤ}
    (hcop : Int.gcd A B = 1) (hA0 : A ≠ 0)
    (hmodel : C ^ 2 = A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4)) :
    ∃ d r : ℕ, Squarefree d ∧ d ∣ b.natAbs ∧
      (A = (d : ℤ) * (r : ℤ) ^ 2 ∨
       A = -((d : ℤ) * (r : ℤ) ^ 2)) := by
  obtain ⟨d, r, hdecomp, hd⟩ := Nat.sq_mul_squarefree A.natAbs
  have hdb := squarefree_core_dvd_cubic_coefficient hcop hA0 hmodel hdecomp hd
  have habs : (A.natAbs : ℤ) = (d : ℤ) * (r : ℤ) ^ 2 := by
    have hcast : (A.natAbs : ℤ) = ((r ^ 2 * d : ℕ) : ℤ) := by
      exact_mod_cast hdecomp.symm
    rw [hcast]
    push_cast
    ring
  refine ⟨d, r, hd, hdb, ?_⟩
  rcases Int.natAbs_eq A with hpos | hneg
  · left
    rw [hpos, habs]
  · right
    rw [hneg, habs]

/-! ## Homogeneous quartic covers and local squareclass exclusions -/

/-- Substituting `A=d*r²` in the primitive cubic model produces the standard
homogeneous quartic for the `d`-squareclass. -/
theorem quartic_cover_of_squareclass
    {a b d e A B C r : ℤ} (hd : d ≠ 0) (hr : r ≠ 0)
    (hb : b = d * e) (hA : A = d * r ^ 2)
    (hmodel : C ^ 2 = A * (A ^ 2 + a * A * B ^ 2 + b * B ^ 4)) :
    ∃ z : ℤ,
      z ^ 2 = d * r ^ 4 + a * r ^ 2 * B ^ 2 + e * B ^ 4 := by
  let Q : ℤ := d * r ^ 4 + a * r ^ 2 * B ^ 2 + e * B ^ 4
  have hfactor : C ^ 2 = (d * r) ^ 2 * Q := by
    rw [hmodel, hA, hb]
    simp only [Q]
    ring
  have hfactor' : C ^ 2 = d ^ 2 * r ^ 2 * Q := by
    calc
      C ^ 2 = (d * r) ^ 2 * Q := hfactor
      _ = d ^ 2 * r ^ 2 * Q := by ring
  have hdq : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd
  have hrq : (r : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hr
  have hrat : ((C : ℚ) / ((d : ℚ) * (r : ℚ))) ^ 2 = (Q : ℚ) := by
    field_simp [hdq, hrq]
    exact_mod_cast hfactor'
  have hsq : IsSquare (Q : ℚ) :=
    ⟨(C : ℚ) / ((d : ℚ) * (r : ℚ)), by
      rw [← sq]
      exact hrat.symm⟩
  rw [Rat.isSquare_intCast_iff] at hsq
  obtain ⟨z, hz⟩ := hsq
  refine ⟨z, ?_⟩
  rw [sq]
  exact hz.symm

theorem root_coprime_denominator {d r A B : ℤ}
    (hcop : Int.gcd A B = 1) (hA : A = d * r ^ 2) :
    Int.gcd r B = 1 := by
  have hAB : IsCoprime A B := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  have hrA : r ∣ A := by
    rw [hA]
    exact ⟨d * r, by ring⟩
  exact Int.isCoprime_iff_gcd_eq_one.mp (coprime_of_dvd_left hAB hrA)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the `16³` residue triples for this cover.

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the `16³` residue triples for this cover.

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the `9³` residue triples for this cover.

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the `9³` residue triples for this cover.

/-! ## The two squareclass images after local solubility -/

/-! ## Rational-coordinate consequences -/

end MazurProof.RationalPointsN15Descent

end

-- ===== FLT.Assumptions.MazurProof.RationalPointsN15ExactSequence =====
section
/-!
# The abstract exact sequence behind the order-15 two-isogeny descent

Mathlib currently has no elliptic-curve isogeny object and no Mordell--Weil
theorem.  This file therefore isolates and proves the entire group-theoretic
part of the descent.  For homomorphisms `φ : G → H` and `ψ : H → G` whose
composites are multiplication by two, it constructs the exact sequence

`H/φG → G/2G → G/ψH`

and proves the corresponding cardinal bound.  It also proves, for a finitely
generated abelian group, that a four-element two-torsion kernel together with
`|G/2G| ≤ 4` forces free rank zero.  Combining both statements gives the
standard two-isogeny rank-zero criterion.

The sole elliptic-curve-specific boundary left by this file is to realize the
explicit affine maps from `RationalPointsN15Descent` as group homomorphisms and
identify their two quotient groups with the already computed squareclass
images.  No such API exists in Mathlib at present.
-/

namespace MazurProof.RationalPointsN15ExactSequence


/-! ## Quotients by multiplication by two -/

abbrev TwoTorsion (G : Type u) [AddCommGroup G] : Type u :=
  {g : G // 2 • g = 0}

section IsogenySequence

variable {G : Type u} {H : Type v} [AddCommGroup G] [AddCommGroup H]
variable (φ : G →+ H) (ψ : H →+ G)
variable (hψφ : ∀ g : G, ψ (φ g) = 2 • g)

end IsogenySequence

/-! ## The finite torsion contribution -/

section FiniteGroup

variable (T : Type u) [AddCommGroup T] [Finite T]

end FiniteGroup

/-! ## Separating the torsion and free contributions -/

section TorsionAndFree

variable (G : Type u) [AddCommGroup G]

end TorsionAndFree

/-! ## The rank-zero criterion -/

section RankCriterion

variable (G : Type u) [AddCommGroup G] [AddGroup.FG G]

end RankCriterion

/-! ## The consumable two-isogeny criterion -/

end MazurProof.RationalPointsN15ExactSequence

end

-- ===== FLT.Assumptions.MazurProof.X017ExactSequence =====
section
/-!
# The sharpened two-isogeny exact sequence for `X₀(17)`

The general two-isogeny exact sequence bounds `G / 2G` by the product of two
endpoint quotients.  For the standard `X₀(17)` model, the first arrow is
expected to vanish: the left endpoint has two cosets, represented by zero and
a point killed by the dual isogeny.  Exactness then embeds `G / 2G` into the
right endpoint, improving the bound from four to two.

The second section records the corresponding general rank criterion.  In a
finitely generated abelian group, its torsion subgroup contributes exactly
`|G[2]|` classes modulo doubling.  If the entire quotient has no more classes
than this, the free quotient is trivial.
-/

namespace MazurProof.X017ExactSequence

open MazurProof.RationalPointsN15ExactSequence


/-! ## Vanishing of the left exact-sequence map -/

section SharpenedExactSequence

variable {G : Type u} {H : Type v}
variable [AddCommGroup G] [AddCommGroup H]

/-- The quotient `H / φ(G)` has representatives zero and `η`.  This form
retains witnesses in `G`, which lets the isogeny identities reduce both
representatives modulo doubling without choosing a quotient equivalence. -/
def TwoCosetExhaustion (φ : G →+ H) (η : H) : Prop :=
  ∀ h : H, ∃ g : G, h = φ g ∨ h = η + φ g

end SharpenedExactSequence

/-! ## Rank zero at the exact two-torsion bound -/

section RankCriterion

variable (G : Type u) [AddCommGroup G] [AddGroup.FG G]

end RankCriterion

end MazurProof.X017ExactSequence

end

-- ===== FLT.Assumptions.MazurProof.X017HeightDescent =====
section
/-!
# A two-coset height descent

Mathlib's general descent theorem proves finite generation from a finite set of
representatives modulo an endomorphism and compatible height inequalities.
For the standard `X₀(17)` model, the quotient modulo doubling is expected to
have the two representatives zero and the visible order-four point.  This
specialization shows that only one nontrivial translation estimate is needed.
-/

open scoped Pointwise

namespace MazurProof.X017HeightDescent

open MazurProof.X017ExactSequence

variable {G : Type*} [AddCommGroup G]

/-- A two-coset exhaustion for doubling is exactly the representative-set
cover required by the height descent theorem. -/
theorem twoCosetExhaustion_set_cover
    (T : G)
    (hrep :
      TwoCosetExhaustion (nsmulAddMonoidHom (α := G) 2) T) :
    ({0, T} : Set G) +
        ((nsmulAddMonoidHom (α := G) 2).range : Set G) = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  obtain ⟨g, hx | hx⟩ := hrep x
  · apply Set.mem_add.mpr
    exact ⟨0, by simp, 2 • g, ⟨g, rfl⟩, by simpa using hx.symm⟩
  · apply Set.mem_add.mpr
    exact ⟨T, by simp, 2 • g, ⟨g, rfl⟩, hx.symm⟩

/-! ## Removing the fixed-translation estimate by orbit symmetrization -/

/-- Sum a height over the four translates by a point of order dividing four.
For the visible point on `X₀(17)`, this replaces a coordinate-wise translation
estimate by an exactly translation-invariant height. -/
def fourOrbitHeight (T : G) (h : G → ℝ) (x : G) : ℝ :=
  h x + h (T + x) + h (2 • T + x) + h (3 • T + x)

/-- The four-orbit height is invariant under translation by `T` when
`4 • T = 0`; translation merely cyclically permutes its four summands. -/
theorem fourOrbitHeight_add_left
    (T : G) (h : G → ℝ) (hT : 4 • T = 0) (x : G) :
    fourOrbitHeight T h (T + x) = fourOrbitHeight T h x := by
  simp only [fourOrbitHeight]
  have hTT : T + T = 2 • T := by simp [two_nsmul]
  have hT2T : T + 2 • T = 3 • T := by
    rw [show (3 : ℕ) = 1 + 2 by norm_num, add_nsmul, one_nsmul]
  have hT3T : T + 3 • T = 0 := by
    rw [show (4 : ℕ) = 1 + 3 by norm_num, add_nsmul, one_nsmul] at hT
    exact hT
  have h2TT : 2 • T + (T + x) = 3 • T + x := by
    calc
      2 • T + (T + x) = (T + 2 • T) + x := by abel
      _ = 3 • T + x := by rw [hT2T]
  have h3TT : 3 • T + (T + x) = x := by
    calc
      3 • T + (T + x) = (T + 3 • T) + x := by abel
      _ = x := by rw [hT3T, zero_add]
  rw [← add_assoc T T x, hTT, h2TT, h3TT]
  ring

/-- Northcott finiteness passes to the four-orbit height because its first
summand is the base height and all remaining summands are nonnegative. -/
theorem fourOrbitHeight_northcott
    (T : G) (h : G → ℝ) [Northcott h]
    (hnonneg : ∀ x, 0 ≤ h x) :
    Northcott (fourOrbitHeight T h) where
  finite_le B := by
    refine (Northcott.finite_le (h := h) B).subset ?_
    intro x hx
    have hT1 := hnonneg (T + x)
    have hT2 := hnonneg (2 • T + x)
    have hT3 := hnonneg (3 • T + x)
    simp only [Set.mem_setOf_eq, fourOrbitHeight] at hx ⊢
    linarith

/-- If doubling expands the base height by a factor four, then it expands the
four-orbit height by a factor two.  Doubling identifies opposite translates
in the order-four orbit, while the two unused target summands are
nonnegative. -/
theorem fourOrbitHeight_double_lower
    (T : G) (h : G → ℝ) (C : ℝ)
    (hT : 4 • T = 0)
    (hnonneg : ∀ x, 0 ≤ h x)
    (hdouble : ∀ x, 4 * h x - C ≤ h (2 • x))
    (x : G) :
    2 * fourOrbitHeight T h x - 2 * C ≤
      fourOrbitHeight T h (2 • x) := by
  have h0 := hdouble x
  have h1 := hdouble (T + x)
  have h2 := hdouble (2 • T + x)
  have h3 := hdouble (3 • T + x)
  have hodd1 := hnonneg (T + 2 • x)
  have hodd3 := hnonneg (3 • T + 2 • x)
  have h2T : 2 • (T + x) = 2 • T + 2 • x := by
    rw [nsmul_add]
  have h4T : 2 • (2 • T + x) = 2 • x := by
    rw [nsmul_add, ← mul_nsmul, show 2 * 2 = 4 by norm_num, hT, zero_add]
  have h6T : 2 • (3 • T + x) = 2 • T + 2 • x := by
    rw [nsmul_add, ← mul_nsmul]
    have h6 : 6 • T = 2 • T := by
      rw [show (6 : ℕ) = 4 + 2 by norm_num, add_nsmul, hT, zero_add]
    rw [h6]
  rw [h2T] at h1
  rw [h4T] at h2
  rw [h6T] at h3
  simp only [fourOrbitHeight]
  linarith

/-- A two-coset cover and the standard duplication bound imply finite
generation without any separate formula for translation by `T`.  The descent
uses expansion constants `a = 1` and `b = 2` for the symmetrized height. -/
theorem fg_of_fourOrbitHeight
    (T : G) (h : G → ℝ) [Northcott h]
    (C : ℝ) (hC : 0 ≤ C)
    (hT : 4 • T = 0)
    (hrep :
      TwoCosetExhaustion (nsmulAddMonoidHom (α := G) 2) T)
    (hnonneg : ∀ x, 0 ≤ h x)
    (hdouble : ∀ x, 4 * h x - C ≤ h (2 • x)) :
    AddGroup.FG G := by
  let H : G → ℝ := fourOrbitHeight T h
  letI : Northcott H := fourOrbitHeight_northcott T h hnonneg
  apply AddGroup.fg_of_descent
    (f := nsmulAddMonoidHom (α := G) 2)
    (s := ({0, T} : Set G))
    (h := H) (a := 1) (b := 2) (c := 2 * C)
  · intro U x hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa using U.nsmul_mem hy 2
  · norm_num
  · norm_num
  · simp
  · exact twoCosetExhaustion_set_cover T hrep
  · intro g hg x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      dsimp [H]
      simp only [zero_add, one_mul]
      linarith
    · rw [hg]
      dsimp [H]
      rw [one_mul, fourOrbitHeight_add_left T h hT x]
      linarith
  · intro x
    dsimp [H]
    exact fourOrbitHeight_double_lower T h C hT hnonneg hdouble x

end MazurProof.X017HeightDescent

end

-- ===== FLT.Assumptions.MazurProof.StandardTwoIsogenyDualHom =====
section
/-!
# The bundled dual map on a standard two-isogeny

The explicit dual formula on

`E' : y² = x(x² - 2ax + a² - 4b)`

lands back on `E : y² = x(x² + ax + b)`.  To prove its additivity without
repeating elliptic-curve group-law algebra, apply the already additive
standard point map once more to `E'`.  Its target is the fourth-power scaling
of `E`; the variable change with scale factor two identifies that curve with
`E`.  Coordinate calculation then identifies the transported homomorphism
with the existing `dualPoint` formula.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.StandardTwoIsogenyDualHom

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.N18RouteC.VariableChangePoints
open MazurProof.VeluTwoIsogeny
open MazurProof.VeluTwoIsogeny.StandardTwoIsogeny

noncomputable section

/-! ## The scaling equivalence after applying the standard map twice -/

/-- Scaling factor two from the twice-quotiented curve back to the original
standard curve. -/
def dualScaleChange : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 (2 : ℚ) (by norm_num)
  r := 0
  s := 0
  t := 0

/-- The inverse scaling constructs the twice-quotiented curve from the
original standard curve. -/
def dualScaleChangeInv : WeierstrassCurve.VariableChange ℚ where
  u := Units.mk0 (1 / 2 : ℚ) (by norm_num)
  r := 0
  s := 0
  t := 0

/-- The raw target obtained by applying `pointMap` to the standard dual. -/
@[reducible] def twiceQuotientCurve (a b : ℚ) : WeierstrassCurve ℚ :=
  curve (-2 * (-2 * a))
    ((-2 * a) ^ 2 - 4 * (a ^ 2 - 4 * b))

/-- Inverse scaling identifies the original curve with the raw twice
quotient. -/
theorem dualScaleChangeInv_curve (a b : ℚ) :
    dualScaleChangeInv • curve a b = twiceQuotientCurve a b := by
  rw [WeierstrassCurve.variableChange_def]
  ext <;>
    norm_num [dualScaleChangeInv, twiceQuotientCurve, curve] <;>
    ring

/-- Forward scaling identifies the raw twice quotient with the original
standard curve. -/
theorem dualScaleChange_curve (a b : ℚ) :
    dualScaleChange • twiceQuotientCurve a b = curve a b := by
  rw [WeierstrassCurve.variableChange_def]
  ext <;>
    norm_num [dualScaleChange, twiceQuotientCurve, curve] <;>
    ring

/-- The raw twice quotient is elliptic because it is a variable-change image
of the original elliptic curve. -/
@[implicit_reducible] noncomputable def twiceQuotientIsElliptic
    (a b : ℚ) [hE : (curve a b).IsElliptic] :
    (twiceQuotientCurve a b).IsElliptic :=
  dualScaleChangeInv_curve a b ▸
    (inferInstance :
      (dualScaleChangeInv • curve a b).IsElliptic)

/-- Additive equivalence from the raw twice quotient back to the original
standard curve. -/
noncomputable def dualScaleEquiv
    (a b : ℚ) [hE : (curve a b).IsElliptic] :
    Point (twiceQuotientCurve a b) ≃+ Point (curve a b) :=
  letI : (twiceQuotientCurve a b).IsElliptic :=
    twiceQuotientIsElliptic a b
  (variableChangePointAddEquiv
      (twiceQuotientCurve a b) dualScaleChange).trans
    (curveCastAddEquiv (dualScaleChange_curve a b))

/-! ## Identification with the explicit dual formula -/

/-- Applying the standard forward homomorphism to the standard dual and then
scaling its target produces an additive map back to the source. -/
noncomputable def transportedDualHom
    (a b : ℚ)
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic] :
    Point (curve (-2 * a) (a ^ 2 - 4 * b)) →+ Point (curve a b) :=
  letI : (twiceQuotientCurve a b).IsElliptic :=
    twiceQuotientIsElliptic a b
  (dualScaleEquiv a b).toAddMonoidHom.comp
    { toFun := pointMap
      map_zero' := pointMap_zero
      map_add' := pointMap_add }

/-- The transported additive map agrees pointwise with `dualPoint`. -/
theorem transportedDualHom_apply
    {a b : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (Q : Point (curve (-2 * a) (a ^ 2 - 4 * b))) :
    transportedDualHom a b Q = dualPoint Q := by
  letI : (twiceQuotientCurve a b).IsElliptic :=
    twiceQuotientIsElliptic a b
  cases Q with
  | zero =>
      change dualScaleEquiv a b (pointMap 0) = dualPoint 0
      rw [pointMap_zero, map_zero, dualPoint_zero]
  | some x y h =>
      by_cases hx : x = 0
      · have hforward :
            pointMap
                (a := -2 * a) (b := a ^ 2 - 4 * b)
                (Point.some x y h) =
              0 := by
          unfold pointMap
          exact dif_pos hx
        have hdual :
            dualPoint (a := a) (b := b) (Point.some x y h) = 0 := by
          unfold dualPoint
          exact dif_pos hx
        change
          dualScaleEquiv a b
              (pointMap
                (a := -2 * a) (b := a ^ 2 - 4 * b)
                (Point.some x y h)) =
            dualPoint (a := a) (b := b) (Point.some x y h)
        rw [hforward, map_zero, hdual]
      · change
          dualScaleEquiv a b
              (pointMap
                (a := -2 * a) (b := a ^ 2 - 4 * b)
                (Point.some x y h)) =
            dualPoint (a := a) (b := b) (Point.some x y h)
        rw [pointMap_some h hx, dualPoint_some h hx]
        unfold dualScaleEquiv
        rw [AddEquiv.trans_apply, variableChangeEquiv_some,
          curveCastAddEquiv_some]
        rw [Point.some.injEq]
        constructor
        · norm_num [variableChangePointX, dualScaleChange, fx, dx]
          ring
        · norm_num [variableChangePointY, dualScaleChange, fy, dy]
          ring

/-- The explicit standard dual formula bundled as an additive
homomorphism. -/
noncomputable def dualPointHom
    (a b : ℚ)
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic] :
    Point (curve (-2 * a) (a ^ 2 - 4 * b)) →+ Point (curve a b) where
  toFun := dualPoint
  map_zero' := dualPoint_zero
  map_add' P Q := by
    rw [← transportedDualHom_apply (P + Q), map_add,
      transportedDualHom_apply, transportedDualHom_apply]

end

end MazurProof.StandardTwoIsogenyDualHom

end

-- ===== FLT.Assumptions.MazurProof.X017IsogenySequence =====
section
/-!
# The rational two-isogeny pair on the standard `X₀(17)` model

The forward homomorphism transports the general Vélu map through the explicit
source and target changes used by `X017Model`.  The dual homomorphism uses the
bundled standard-coordinate dual formula: it applies the standard isogeny a
second time and scales the twice-quotiented curve back to the source.  The
resulting maps have exactly the types needed by the two-isogeny exact
sequence.

The distinguished point on the target is the transported Vélu kernel point.
Its standard coordinates are `(0,0)`; in particular, it is not the point
`U = (64,0)`, whose dual image is the nonzero source kernel point.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017IsogenySequence

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.VeluTwoIsogeny
open MazurProof.X017Model
open MazurProof.StandardTwoIsogenyDualHom

noncomputable section

/-! ## Transported additive homomorphisms -/

/-- The forward rational two-isogeny from the standard source model to its
standard dual. -/
noncomputable def forwardHom : Point standard →+ Point standardDual :=
  (StandardTwoIsogeny.targetEquiv ten_is_root).toAddMonoidHom.comp
    ((veluMapHom ten_is_root).comp ShortToStandard.symm.toAddMonoidHom)

/-- The transported forward homomorphism agrees pointwise with the explicit
standard-coordinate Vélu formula. -/
theorem forwardHom_apply (P : Point standard) :
    forwardHom P = StandardTwoIsogeny.pointMap P := by
  change
    StandardTwoIsogeny.targetEquiv ten_is_root
        (veluMapPoint ten_is_root (ShortToStandard.symm P)) =
      StandardTwoIsogeny.pointMap P
  calc
    _ = StandardTwoIsogeny.pointMap
        (StandardTwoIsogeny.sourceEquiv ten_is_root
          (ShortToStandard.symm P)) :=
      StandardTwoIsogeny.map_conjugacy ten_is_root
        (ShortToStandard.symm P)
    _ = StandardTwoIsogeny.pointMap P := by
      rw [show StandardTwoIsogeny.sourceEquiv ten_is_root =
          ShortToStandard by
        rfl, ShortToStandard.apply_symm_apply]

/-- The order-four point maps to the visible target point `(64,0)`. -/
@[simp] theorem forwardHom_T : forwardHom T = U := by
  rw [forwardHom_apply, pointMap_T]

/-- The visible source two-torsion point is the kernel of the forward
isogeny. -/
@[simp] theorem forwardHom_K : forwardHom K = 0 := by
  rw [forwardHom_apply]
  exact StandardTwoIsogeny.pointMap_kernel

/-- The dual rational two-isogeny from the standard dual back to the standard
source model. -/
noncomputable def dualHom : Point standardDual →+ Point standard :=
  dualPointHom a17 b17

/-- The transported dual homomorphism agrees with the explicit
standard-coordinate dual formula. -/
theorem dualHom_apply (Q : Point standardDual) :
    dualHom Q = StandardTwoIsogeny.dualPoint Q := by
  rfl

/-- The transported dual isogeny composed with the transported forward
isogeny is multiplication by two on the standard source model. -/
theorem dual_comp_forward (P : Point standard) :
    dualHom (forwardHom P) = 2 • P := by
  rw [dualHom_apply, forwardHom_apply,
    StandardTwoIsogeny.dual_comp_pointMap]

/-! ## The correct target-kernel representative -/

/-- The nonzero kernel point of the transported dual isogeny.  Before the
target coordinate change it is the Vélu point `(-20,0)`. -/
noncomputable def eta : Point standardDual :=
  StandardTwoIsogeny.targetEquiv ten_is_root (etaPoint ten_is_root)

/-- In standard target coordinates the dual-kernel representative is the
visible point `(0,0)`. -/
theorem eta_eq_standardDualKernel :
    eta =
      StandardTwoIsogeny.kernelPoint
        (-2 * a17) (a17 ^ 2 - 4 * b17) := by
  change
    StandardTwoIsogeny.targetEquiv ten_is_root
        (Point.some (-2 * (10 : ℚ)) 0
          (eta_nonsingular ten_is_root)) =
      StandardTwoIsogeny.kernelPoint
        (-2 * a17) (a17 ^ 2 - 4 * b17)
  rw [StandardTwoIsogeny.targetEquiv_some]
  unfold StandardTwoIsogeny.kernelPoint
  rw [Point.some.injEq]
  constructor
  · norm_num [StandardTwoIsogeny.targetChange_x]
  · norm_num [StandardTwoIsogeny.targetChange_y]

/-- The transported dual isogeny kills its distinguished target-kernel
point. -/
@[simp] theorem dualHom_eta : dualHom eta = 0 := by
  rw [dualHom_apply, eta_eq_standardDualKernel]
  rfl

/-- The dual sends the visible target point `(64,0)` to the visible source
kernel point `(0,0)`. -/
@[simp] theorem dualHom_U : dualHom U = K := by
  rw [← forwardHom_T, dual_comp_forward, two_nsmul_T_eq_K]

end

end MazurProof.X017IsogenySequence

end

-- ===== FLT.Assumptions.MazurProof.X017Descent =====
section
/-!
# First-coordinate descent on the standard `X₀(17)` curve

The standard source model is

`y² = x(x² + 30x + 289)`.

The quadratic factor is everywhere positive over `ℚ`, so every nonzero
rational first coordinate is positive.  Clearing square denominators and
extracting the squarefree core shows that this coordinate has squareclass
`1` or `17`.  This is the arithmetic input for the right endpoint of the
two-isogeny exact sequence; no quotient-cardinality conclusion is asserted
until explicit dual-isogeny preimages are constructed.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017Descent

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.RationalPointsN15Descent
open MazurProof.VeluTwoIsogeny
open MazurProof.X017Model

/-! ## Squarefree divisors of the constant coefficient -/

/-- A squarefree divisor of `17²` is either `1` or `17`. -/
theorem squarefree_dvd_289 {d : ℕ} (hd : Squarefree d)
    (hdiv : d ∣ 289) :
    d = 1 ∨ d = 17 := by
  have hpow : d ∣ 17 ^ 2 := by
    norm_num at hdiv ⊢
    exact hdiv
  have hd17 : d ∣ 17 :=
    (hd.dvd_pow_iff_dvd (by norm_num : 2 ≠ 0)).mp hpow
  exact (Nat.dvd_prime (by norm_num : Nat.Prime 17)).mp hd17

/-! ## Rational squareclasses on the source model -/

/-- A nonzero affine point on the standard source model has positive first
coordinate of squareclass `1` or `17`. -/
theorem source_x_squareclass {x y : ℚ}
    (h : Equation standard x y) (hx0 : x ≠ 0) :
    ∃ q : ℚ, x = q ^ 2 ∨ x = 17 * q ^ 2 := by
  have hcurve0 :=
    (StandardTwoIsogeny.curve_equation
      (a := a17) (b := b17)).mp h
  have hcurve :
      y ^ 2 = x ^ 3 + (30 : ℚ) * x ^ 2 + (289 : ℚ) * x := by
    norm_num [a17, b17, veluT] at hcurve0
    nlinarith
  have hquad_pos : 0 < x ^ 2 + 30 * x + 289 := by
    nlinarith [sq_nonneg (x + 15)]
  have hx_nonneg : 0 ≤ x := by
    have hfactor : y ^ 2 = x * (x ^ 2 + 30 * x + 289) := by
      nlinarith
    nlinarith [sq_nonneg y]
  have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
  obtain ⟨A, B, C, hBpos, hcop, hx, hmodel⟩ :=
    integral_model_monic 30 289 x y hcurve
  have hA0 : A ≠ 0 := by
    intro hA
    apply hx0
    rw [hx, hA]
    norm_num
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    first_coordinate_squareclass hcop hA0 hmodel
  rcases squarefree_dvd_289 hd (by simpa using hdiv) with rfl | rfl
  · rcases hsign with hA | hA
    · refine ⟨(r : ℚ) / (B : ℚ), Or.inl ?_⟩
      rw [hx, hA]
      push_cast
      ring
    · exfalso
      rw [hx, hA] at hx_pos
      push_cast at hx_pos
      have hnum : -(1 * (r : ℚ) ^ 2) ≤ 0 :=
        neg_nonpos.mpr (mul_nonneg (by norm_num) (sq_nonneg _))
      have hden : 0 ≤ (B : ℚ) ^ 2 := sq_nonneg _
      exact (not_lt_of_ge
        (div_nonpos_of_nonpos_of_nonneg hnum hden)) hx_pos
  · rcases hsign with hA | hA
    · refine ⟨(r : ℚ) / (B : ℚ), Or.inr ?_⟩
      rw [hx, hA]
      push_cast
      ring
    · exfalso
      rw [hx, hA] at hx_pos
      push_cast at hx_pos
      have hnum : -(17 * (r : ℚ) ^ 2) ≤ 0 :=
        neg_nonpos.mpr (mul_nonneg (by norm_num) (sq_nonneg _))
      have hden : 0 ≤ (B : ℚ) ^ 2 := sq_nonneg _
      exact (not_lt_of_ge
        (div_nonpos_of_nonpos_of_nonneg hnum hden)) hx_pos

end MazurProof.X017Descent

end

-- ===== FLT.Assumptions.MazurProof.StandardTwoIsogenyPreimages =====
section
/-!
# Square-coordinate preimages for the standard two-isogeny

For the standard isogeny

`E : y² = x(x² + ax + b) → E' : y² = x(x² - 2ax + a² - 4b)`,

an affine target point with nonzero square first coordinate has an explicit
rational preimage.  This is the coefficient-generic form of the preimage
calculation previously specialized to the order-15 curve.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.StandardTwoIsogenyPreimages

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.VeluTwoIsogeny.StandardTwoIsogeny

noncomputable section

/-- The first coordinate of the source preimage associated with a square
target coordinate `x=r²`. -/
def preimageX (a r y : ℚ) : ℚ :=
  (r ^ 2 - a - y / r) / 2

/-- The second coordinate of the source preimage. -/
def preimageY (a r y : ℚ) : ℚ :=
  r * preimageX a r y

/-- The first coordinate of a dual-isogeny preimage associated with a square
source coordinate `x=r²`. -/
def dualPreimageX (a r y : ℚ) : ℚ :=
  a + 2 * r ^ 2 - 2 * y / r

/-- The second coordinate of the dual-isogeny preimage. -/
def dualPreimageY (a r y : ℚ) : ℚ :=
  2 * r * dualPreimageX a r y

/-- A nonzero square first coordinate on the target of the standard
two-isogeny gives an explicit rational source preimage. -/
theorem exists_pointMap_preimage_of_x_eq_sq
    {a b x y r : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h : Nonsingular (curve (-2 * a) (a ^ 2 - 4 * b)) x y)
    (hx : x ≠ 0) (hr : x = r ^ 2) :
    ∃ P : Point (curve a b),
      pointMap P = Point.some x y h := by
  have hr0 : r ≠ 0 := by
    intro hrz
    apply hx
    rw [hr, hrz]
    norm_num
  have hcurve :
      y ^ 2 = x * (x ^ 2 + (-2 * a) * x + (a ^ 2 - 4 * b)) :=
    curve_equation.mp h.left
  have hcurveR :
      y ^ 2 =
        r ^ 6 - 2 * a * r ^ 4 + (a ^ 2 - 4 * b) * r ^ 2 := by
    rw [hr] at hcurve
    nlinarith
  let px := preimageX a r y
  let py := preimageY a r y
  have hprod :
      px * ((r ^ 2 - a + y / r) / 2) = b := by
    dsimp [px, preimageX]
    field_simp [hr0]
    linear_combination -hcurveR
  have hpx : px ≠ 0 := by
    intro hp
    rw [hp, zero_mul] at hprod
    exact (b_ne_zero a b) hprod.symm
  have hnum : b - px ^ 2 = px * y / r := by
    rw [← hprod]
    dsimp [px, preimageX]
    field_simp [hr0]
    ring
  have hpeq : Equation (curve a b) px py := by
    rw [curve_equation]
    dsimp [px, py, preimageX, preimageY]
    field_simp [hr0]
    linear_combination
      (-r ^ 3 + a * r + y) * hcurveR
  have hpns : Nonsingular (curve a b) px py :=
    equation_iff_nonsingular.mp hpeq
  let P : Point (curve a b) := Point.some px py hpns
  refine ⟨P, ?_⟩
  dsimp [P]
  rw [pointMap_some hpns hpx]
  rw [Point.some.injEq]
  constructor
  · change (r * px) ^ 2 / px ^ 2 = x
    rw [hr]
    field_simp [hpx]
  · change (r * px) * (b - px ^ 2) / px ^ 2 = y
    rw [hnum]
    field_simp [hpx, hr0]

/-- A nonzero square first coordinate on the source of the standard
two-isogeny gives an explicit rational preimage under the dual formula. -/
theorem exists_dualPoint_preimage_of_x_eq_sq
    {a b x y r : ℚ}
    [hE : (curve a b).IsElliptic]
    [hE' : (curve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic]
    (h : Nonsingular (curve a b) x y)
    (hx : x ≠ 0) (hr : x = r ^ 2) :
    ∃ Q : Point (curve (-2 * a) (a ^ 2 - 4 * b)),
      dualPoint Q = Point.some x y h := by
  have hr0 : r ≠ 0 := by
    intro hrz
    apply hx
    rw [hr, hrz]
    norm_num
  have hcurve :
      y ^ 2 = x * (x ^ 2 + a * x + b) :=
    curve_equation.mp h.left
  have hcurveR :
      y ^ 2 = r ^ 6 + a * r ^ 4 + b * r ^ 2 := by
    rw [hr] at hcurve
    nlinarith
  let qx := dualPreimageX a r y
  let qy := dualPreimageY a r y
  have hprod :
      qx * (a + 2 * r ^ 2 + 2 * y / r) = a ^ 2 - 4 * b := by
    dsimp [qx, dualPreimageX]
    field_simp [hr0]
    linear_combination -4 * hcurveR
  have hqx : qx ≠ 0 := by
    intro hq
    rw [hq, zero_mul] at hprod
    exact
      (b_ne_zero (-2 * a) (a ^ 2 - 4 * b)) hprod.symm
  have hnum : (a ^ 2 - 4 * b) - qx ^ 2 = 4 * qx * y / r := by
    rw [← hprod]
    dsimp [qx, dualPreimageX]
    field_simp [hr0]
    ring
  have hqeq :
      Equation (curve (-2 * a) (a ^ 2 - 4 * b)) qx qy := by
    rw [curve_equation]
    dsimp [qx, qy, dualPreimageX, dualPreimageY]
    field_simp [hr0]
    linear_combination
      4 * (-2 * r ^ 3 - a * r + 2 * y) * hcurveR
  have hqns :
      Nonsingular (curve (-2 * a) (a ^ 2 - 4 * b)) qx qy :=
    equation_iff_nonsingular.mp hqeq
  let Q : Point (curve (-2 * a) (a ^ 2 - 4 * b)) :=
    Point.some qx qy hqns
  refine ⟨Q, ?_⟩
  dsimp [Q]
  rw [dualPoint_some hqns hqx]
  rw [Point.some.injEq]
  constructor
  · change (2 * r * qx) ^ 2 / qx ^ 2 / 4 = x
    rw [hr]
    field_simp [hqx]
    ring
  · change
      (2 * r * qx) * ((a ^ 2 - 4 * b) - qx ^ 2) /
          qx ^ 2 / 8 =
        y
    rw [hnum]
    field_simp [hqx, hr0]
    ring

end

end MazurProof.StandardTwoIsogenyPreimages

end

-- ===== FLT.Assumptions.MazurProof.X017FirstCoset =====
section
/-!
# The target squareclasses in the `X₀(17)` two-isogeny descent

The standard dual curve is

`y² = x(x² - 60x - 256)`.

Primitive denominator clearing initially permits first-coordinate
squareclasses `±1` and `±2`.  The two classes supported by `2` are excluded
by a three-stage parity descent.  Each parity step is certified by a small
kernel reduction over `ZMod 8`; the intervening divisions by `2` and `4` are
performed over the integers.

This file stops at the squareclass statement.  Converting square and
negative-square coordinates into the two forward-isogeny cosets is the next
separate layer.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017FirstCoset

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.RationalPointsN15Descent
open MazurProof.StandardTwoIsogenyPreimages
open MazurProof.VeluTwoIsogeny
open MazurProof.X017Model
open MazurProof.X017IsogenySequence

/-! ## Small parity certificates -/

private def reduce8to2 : ZMod 8 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the `8³` residue triples in the first positive stage.
private theorem pos_stage0_mod8 :
    ∀ r B z : ZMod 8,
      z ^ 2 = 2 * r ^ 4 - 60 * r ^ 2 * B ^ 2 - 128 * B ^ 4 →
      reduce8to2 r = 0 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- With `B` odd, the first divided equation forces `s` to be even.
private theorem pos_stage1_mod8 :
    ∀ s B u : ZMod 8,
      reduce8to2 B ≠ 0 →
      u ^ 2 = 2 * s ^ 4 - 15 * s ^ 2 * B ^ 2 - 8 * B ^ 4 →
      reduce8to2 s = 0 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The second divided positive equation has no solution when `B` is odd.
private theorem no_pos_stage2_mod8 :
    ∀ t B v : ZMod 8,
      reduce8to2 B ≠ 0 →
      v ^ 2 ≠ 8 * t ^ 4 - 15 * t ^ 2 * B ^ 2 - 2 * B ^ 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the `8³` residue triples in the first negative stage.
private theorem neg_stage0_mod8 :
    ∀ r B z : ZMod 8,
      z ^ 2 = -(2 * r ^ 4) - 60 * r ^ 2 * B ^ 2 + 128 * B ^ 4 →
      reduce8to2 r = 0 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- With `B` odd, the first divided negative equation forces `s` to be even.
private theorem neg_stage1_mod8 :
    ∀ s B u : ZMod 8,
      reduce8to2 B ≠ 0 →
      u ^ 2 = -(2 * s ^ 4) - 15 * s ^ 2 * B ^ 2 + 8 * B ^ 4 →
      reduce8to2 s = 0 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The second divided negative equation has no solution when `B` is odd.
private theorem no_neg_stage2_mod8 :
    ∀ t B v : ZMod 8,
      reduce8to2 B ≠ 0 →
      v ^ 2 ≠ -(8 * t ^ 4) - 15 * t ^ 2 * B ^ 2 + 2 * B ^ 4 := by
  decide

/-- Coprime integers cannot both vanish after reduction modulo two. -/
private theorem primitive_mod_two {r B : ℤ} (hcop : Int.gcd r B = 1) :
    reduce8to2 (r : ZMod 8) ≠ 0 ∨
      reduce8to2 (B : ZMod 8) ≠ 0 := by
  have hnot : ¬ ((2 : ℤ) ∣ r ∧ (2 : ℤ) ∣ B) := by
    rintro ⟨hr, hB⟩
    have h2g : (2 : ℤ) ∣ ((Int.gcd r B : ℕ) : ℤ) :=
      Int.dvd_coe_gcd hr hB
    rw [hcop] at h2g
    norm_num at h2g
  have hmod2 : (r : ZMod 2) ≠ 0 ∨ (B : ZMod 2) ≠ 0 := by
    by_contra h
    push Not at h
    exact hnot
      ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd r 2).mp h.1,
        (ZMod.intCast_zmod_eq_zero_iff_dvd B 2).mp h.2⟩
  simpa [reduce8to2, ZMod.castHom_apply] using hmod2

/-- Vanishing modulo two is equivalent to integer divisibility by two. -/
private theorem two_dvd_of_reduce8to2_eq_zero {r : ℤ}
    (h : reduce8to2 (r : ZMod 8) = 0) :
    (2 : ℤ) ∣ r := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd r 2).mp
  simpa [reduce8to2, ZMod.castHom_apply] using h

/-! ## Exclusion of the two provisional `2`-classes -/

/-- The positive provisional `2`-squareclass has no primitive integral point
on its homogeneous quartic cover. -/
theorem no_standardDual_pos_two_cover
    (r B z : ℤ) (hcop : Int.gcd r B = 1)
    (h :
      z ^ 2 =
        2 * r ^ 4 - 60 * r ^ 2 * B ^ 2 - 128 * B ^ 4) :
    False := by
  have hmod0 := congrArg (fun n : ℤ => (n : ZMod 8)) h
  push_cast at hmod0
  have hrEvenMod :=
    pos_stage0_mod8 (r : ZMod 8) (B : ZMod 8) (z : ZMod 8) hmod0
  have hrEven : (2 : ℤ) ∣ r :=
    two_dvd_of_reduce8to2_eq_zero hrEvenMod
  obtain ⟨s, rfl⟩ := hrEven
  have hBOdd : reduce8to2 (B : ZMod 8) ≠ 0 := by
    rcases primitive_mod_two hcop with hs | hB
    · exact (hs hrEvenMod).elim
    · exact hB
  have hz4 : (4 : ℤ) ∣ z := by
    rw [← Int.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)]
    refine ⟨2 * s ^ 4 - 15 * s ^ 2 * B ^ 2 - 8 * B ^ 4, ?_⟩
    rw [h]
    ring
  obtain ⟨u, rfl⟩ := hz4
  have h1 :
      u ^ 2 = 2 * s ^ 4 - 15 * s ^ 2 * B ^ 2 - 8 * B ^ 4 := by
    nlinarith [h]
  have hmod1 := congrArg (fun n : ℤ => (n : ZMod 8)) h1
  push_cast at hmod1
  have hsEvenMod :=
    pos_stage1_mod8 (s : ZMod 8) (B : ZMod 8) (u : ZMod 8)
      hBOdd hmod1
  have hsEven : (2 : ℤ) ∣ s :=
    two_dvd_of_reduce8to2_eq_zero hsEvenMod
  obtain ⟨t, rfl⟩ := hsEven
  have hu2 : (2 : ℤ) ∣ u := by
    rw [← Int.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)]
    refine ⟨8 * t ^ 4 - 15 * t ^ 2 * B ^ 2 - 2 * B ^ 4, ?_⟩
    rw [h1]
    ring
  obtain ⟨v, rfl⟩ := hu2
  have h2 :
      v ^ 2 = 8 * t ^ 4 - 15 * t ^ 2 * B ^ 2 - 2 * B ^ 4 := by
    nlinarith [h1]
  have hmod2 := congrArg (fun n : ℤ => (n : ZMod 8)) h2
  push_cast at hmod2
  exact
    (no_pos_stage2_mod8 (t : ZMod 8) (B : ZMod 8) (v : ZMod 8)
      hBOdd) hmod2

/-- The negative provisional `2`-squareclass has no primitive integral point
on its homogeneous quartic cover. -/
theorem no_standardDual_neg_two_cover
    (r B z : ℤ) (hcop : Int.gcd r B = 1)
    (h :
      z ^ 2 =
        -(2 * r ^ 4) - 60 * r ^ 2 * B ^ 2 + 128 * B ^ 4) :
    False := by
  have hmod0 := congrArg (fun n : ℤ => (n : ZMod 8)) h
  push_cast at hmod0
  have hrEvenMod :=
    neg_stage0_mod8 (r : ZMod 8) (B : ZMod 8) (z : ZMod 8) hmod0
  have hrEven : (2 : ℤ) ∣ r :=
    two_dvd_of_reduce8to2_eq_zero hrEvenMod
  obtain ⟨s, rfl⟩ := hrEven
  have hBOdd : reduce8to2 (B : ZMod 8) ≠ 0 := by
    rcases primitive_mod_two hcop with hs | hB
    · exact (hs hrEvenMod).elim
    · exact hB
  have hz4 : (4 : ℤ) ∣ z := by
    rw [← Int.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)]
    refine ⟨-(2 * s ^ 4) - 15 * s ^ 2 * B ^ 2 + 8 * B ^ 4, ?_⟩
    rw [h]
    ring
  obtain ⟨u, rfl⟩ := hz4
  have h1 :
      u ^ 2 = -(2 * s ^ 4) - 15 * s ^ 2 * B ^ 2 + 8 * B ^ 4 := by
    nlinarith [h]
  have hmod1 := congrArg (fun n : ℤ => (n : ZMod 8)) h1
  push_cast at hmod1
  have hsEvenMod :=
    neg_stage1_mod8 (s : ZMod 8) (B : ZMod 8) (u : ZMod 8)
      hBOdd hmod1
  have hsEven : (2 : ℤ) ∣ s :=
    two_dvd_of_reduce8to2_eq_zero hsEvenMod
  obtain ⟨t, rfl⟩ := hsEven
  have hu2 : (2 : ℤ) ∣ u := by
    rw [← Int.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)]
    refine ⟨-(8 * t ^ 4) - 15 * t ^ 2 * B ^ 2 + 2 * B ^ 4, ?_⟩
    rw [h1]
    ring
  obtain ⟨v, rfl⟩ := hu2
  have h2 :
      v ^ 2 = -(8 * t ^ 4) - 15 * t ^ 2 * B ^ 2 + 2 * B ^ 4 := by
    nlinarith [h1]
  have hmod2 := congrArg (fun n : ℤ => (n : ZMod 8)) h2
  push_cast at hmod2
  exact
    (no_neg_stage2_mod8 (t : ZMod 8) (B : ZMod 8) (v : ZMod 8)
      hBOdd) hmod2

/-! ## Integral and rational squareclass exhaustion -/

/-- A squarefree divisor of `2⁸` is either `1` or `2`. -/
theorem squarefree_dvd_256 {d : ℕ} (hd : Squarefree d)
    (hdiv : d ∣ 256) :
    d = 1 ∨ d = 2 := by
  have hpow : d ∣ 2 ^ 8 := by
    norm_num at hdiv ⊢
    exact hdiv
  have hd2 : d ∣ 2 :=
    (hd.dvd_pow_iff_dvd (by norm_num : 8 ≠ 0)).mp hpow
  exact (Nat.dvd_prime Nat.prime_two).mp hd2

/-- Only squareclasses `1` and `-1` remain for a nonzero primitive first
coordinate on the standard dual curve. -/
theorem standardDual_first_squareclasses_reduced
    {A B C : ℤ} (hcop : Int.gcd A B = 1) (hA0 : A ≠ 0)
    (hmodel :
      C ^ 2 = A * (A ^ 2 - 60 * A * B ^ 2 - 256 * B ^ 4)) :
    ∃ r : ℤ, A = r ^ 2 ∨ A = -(r ^ 2) := by
  have hmodel' :
      C ^ 2 =
        A * (A ^ 2 + (-60) * A * B ^ 2 + (-256) * B ^ 4) := by
    simpa [sub_eq_add_neg] using hmodel
  obtain ⟨d, r, hd, hdiv, hsign⟩ :=
    first_coordinate_squareclass hcop hA0 hmodel'
  rcases squarefree_dvd_256 hd (by simpa using hdiv) with rfl | rfl
  · refine ⟨(r : ℤ), ?_⟩
    rcases hsign with h | h
    · left
      simpa using h
    · right
      simpa using h
  · rcases hsign with hA | hA
    · have hr0 : (r : ℤ) ≠ 0 := by
        intro hr
        apply hA0
        rw [hA, hr]
        norm_num
      obtain ⟨z, hz⟩ :=
        quartic_cover_of_squareclass
          (a := -60) (b := -256) (d := 2) (e := -128)
          (by norm_num) hr0 (by norm_num) hA hmodel'
      exact
        (no_standardDual_pos_two_cover r B z
          (root_coprime_denominator hcop hA)
          (by simpa [sub_eq_add_neg] using hz)).elim
    · have hA' : A = (-2) * (r : ℤ) ^ 2 := by
        simpa using hA
      have hr0 : (r : ℤ) ≠ 0 := by
        intro hr
        apply hA0
        rw [hA', hr]
        norm_num
      obtain ⟨z, hz⟩ :=
        quartic_cover_of_squareclass
          (a := -60) (b := -256) (d := -2) (e := 128)
          (by norm_num) hr0 (by norm_num) hA' hmodel'
      exact
        (no_standardDual_neg_two_cover r B z
          (root_coprime_denominator hcop hA')
          (by simpa [sub_eq_add_neg] using hz)).elim

/-- Every nonkernel rational affine point on the standard dual curve has
square or negative-square first coordinate. -/
theorem standardDual_x_squareclass {x y : ℚ}
    (h : Equation standardDual x y) (hx0 : x ≠ 0) :
    ∃ q : ℚ, x = q ^ 2 ∨ x = -(q ^ 2) := by
  have hcurve0 :=
    (StandardTwoIsogeny.curve_equation
      (a := -2 * a17) (b := a17 ^ 2 - 4 * b17)).mp h
  have hcurve :
      y ^ 2 = x ^ 3 + (-60 : ℚ) * x ^ 2 + (-256 : ℚ) * x := by
    norm_num [a17, b17, veluT] at hcurve0
    nlinarith
  obtain ⟨A, B, C, hBpos, hcop, hx, hmodel⟩ :=
    integral_model_monic (-60) (-256) x y hcurve
  have hA0 : A ≠ 0 := by
    intro hA
    apply hx0
    rw [hx, hA]
    norm_num
  obtain ⟨r, hr | hr⟩ :=
    standardDual_first_squareclasses_reduced hcop hA0 (by
      simpa [sub_eq_add_neg] using hmodel)
  · refine ⟨(r : ℚ) / (B : ℚ), Or.inl ?_⟩
    rw [hx, hr]
    push_cast
    ring
  · refine ⟨(r : ℚ) / (B : ℚ), Or.inr ?_⟩
    rw [hx, hr]
    push_cast
    ring

/-! ## The first concrete isogeny quotient -/

/-- A nonzero square first coordinate on the standard dual has a preimage
under the transported forward isogeny. -/
theorem exists_forwardHom_preimage_of_x_eq_sq
    {x y r : ℚ} (h : Nonsingular standardDual x y)
    (hx : x ≠ 0) (hr : x = r ^ 2) :
    ∃ P : Point standard,
      forwardHom P = Point.some x y h := by
  obtain ⟨P, hP⟩ :=
    exists_pointMap_preimage_of_x_eq_sq
      (a := a17) (b := b17) h hx hr
  exact ⟨P, by rw [forwardHom_apply, hP]⟩

/-- The transported target-kernel representative has additive order two in
the form needed for coset arithmetic. -/
private theorem eta_add_self : eta + eta = 0 := by
  rw [eta_eq_standardDualKernel]
  exact StandardTwoIsogeny.kernel_add_self

/-- The target of the standard N17 two-isogeny is covered by the two cosets
represented by zero and the dual-kernel point `(0,0)`. -/
theorem standardDual_twoCosetExhaustion :
    MazurProof.X017ExactSequence.TwoCosetExhaustion forwardHom eta := by
  intro Q
  cases Q with
  | zero =>
      exact ⟨0, Or.inl (map_zero forwardHom).symm⟩
  | some x y h =>
      by_cases hx : x = 0
      · have hy : y = 0 :=
          StandardTwoIsogeny.y_zero_of_x_zero h hx
        have hQeta :
            (Point.some x y h : Point standardDual) = eta := by
          rw [eta_eq_standardDualKernel]
          unfold StandardTwoIsogeny.kernelPoint
          rw [Point.some.injEq]
          exact ⟨hx, hy⟩
        refine ⟨0, Or.inr ?_⟩
        rw [hQeta, map_zero, add_zero]
      · obtain ⟨q, hq | hq⟩ :=
          standardDual_x_squareclass h.left hx
        · obtain ⟨P, hP⟩ :=
            exists_forwardHom_preimage_of_x_eq_sq h hx hq
          exact ⟨P, Or.inl hP.symm⟩
        · have hq0 : q ≠ 0 := by
            intro hqz
            apply hx
            rw [hq, hqz]
            norm_num
          generalize hR :
              (Point.some x y h : Point standardDual) + eta = R
          cases R with
          | zero =>
              have hR' := hR
              rw [eta_eq_standardDualKernel] at hR'
              unfold StandardTwoIsogeny.kernelPoint at hR'
              rw [Point.add_of_X_ne hx] at hR'
              exact ((Point.some_ne_zero _) hR').elim
          | some x' y' h' =>
              have hx' :
                  x' = (a17 ^ 2 - 4 * b17) / x := by
                have hR' := hR
                rw [eta_eq_standardDualKernel] at hR'
                unfold StandardTwoIsogeny.kernelPoint at hR'
                rw [Point.add_of_X_ne hx] at hR'
                rw [Point.some.injEq] at hR'
                calc
                  x' =
                      addX standardDual x 0
                        (slope standardDual x 0 y 0) :=
                    hR'.1.symm
                  _ = (a17 ^ 2 - 4 * b17) / x :=
                    StandardTwoIsogeny.add_kernel_x h hx
              have hxSquare : x' = (16 / q) ^ 2 := by
                rw [hx', hq]
                norm_num [a17, b17, veluT]
                field_simp [hq0]
                norm_num
              have hx'0 : x' ≠ 0 := by
                rw [hxSquare]
                exact pow_ne_zero 2 (div_ne_zero (by norm_num) hq0)
              obtain ⟨P, hP⟩ :=
                exists_forwardHom_preimage_of_x_eq_sq h' hx'0 hxSquare
              have hrange :
                  (Point.some x y h : Point standardDual) + eta =
                    forwardHom P :=
                hR.trans hP.symm
              refine ⟨P, Or.inr ?_⟩
              calc
                (Point.some x y h : Point standardDual) =
                    Point.some x y h + 0 := (add_zero _).symm
                _ = Point.some x y h + (eta + eta) := by
                  rw [eta_add_self]
                _ = eta + (Point.some x y h + eta) := by
                  ac_rfl
                _ = eta + forwardHom P := by
                  rw [hrange]

end MazurProof.X017FirstCoset

end

-- ===== FLT.Assumptions.MazurProof.X017SecondCoset =====
section
/-!
# The source quotient in the `X₀(17)` two-isogeny descent

The remaining isogeny quotient is the source modulo the image of the dual
map.  Its nontrivial first-coordinate squareclass is represented by the
order-four point `T=(17,136)`.  Translation by `-T` converts that class into
a square, after which the explicit dual-isogeny preimage formula applies.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017SecondCoset

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurProof.StandardTwoIsogenyPreimages
open MazurProof.VeluTwoIsogeny
open MazurProof.X017Descent
open MazurProof.X017FirstCoset
open MazurProof.X017IsogenySequence
open MazurProof.X017Model

noncomputable section

/-! ## Translation of the `17`-squareclass by `T` -/

/-- For a nonzero affine source point with `x=17r²` and `x≠17`, the first
coordinate after translating by `-T` is an explicit rational square. -/
theorem sub_T_addX_square
    {x y r : ℚ} (h : Nonsingular standard x y)
    (hx0 : x ≠ 0) (hx17 : x ≠ 17) (hr : x = 17 * r ^ 2) :
    addX standard x 17
        (slope standard x 17 y (-136)) =
      ((y + 8 * x) / (r * (x - 17))) ^ 2 := by
  have hr0 : r ≠ 0 := by
    intro hrz
    apply hx0
    rw [hr, hrz]
    norm_num
  have hcurve :=
    (StandardTwoIsogeny.curve_equation
      (a := a17) (b := b17)).mp h.left
  norm_num [a17, b17, veluT] at hcurve
  have hrsq1 : r ^ 2 ≠ 1 := by
    intro hrsq
    apply hx17
    rw [hr, hrsq]
    norm_num
  rw [slope_of_X_ne hx17]
  norm_num [standard, StandardTwoIsogeny.curve, addX]
  rw [hr] at hcurve ⊢
  field_simp [hr0, hrsq1]
  nlinarith [hcurve]

/-! ## Explicit dual preimages -/

/-- A nonzero square first coordinate on the standard source has a preimage
under the bundled dual isogeny. -/
theorem exists_dualHom_preimage_of_x_eq_sq
    {x y r : ℚ} (h : Nonsingular standard x y)
    (hx : x ≠ 0) (hr : x = r ^ 2) :
    ∃ Q : Point standardDual,
      dualHom Q = Point.some x y h := by
  obtain ⟨Q, hQ⟩ :=
    exists_dualPoint_preimage_of_x_eq_sq
      (a := a17) (b := b17) h hx hr
  exact ⟨Q, by rw [dualHom_apply, hQ]⟩

/-! ## Exceptional visible points -/

/-- The negative of `T` has the expected affine coordinates. -/
private theorem neg_T_eq_some :
    -T =
      Point.some 17 (-136)
        (equation_iff_nonsingular.mp
          (StandardTwoIsogeny.curve_equation.mpr (by
            norm_num [a17, b17, veluT]))) := by
  unfold T
  rw [Point.neg_some, Point.some.injEq]
  constructor
  · rfl
  · norm_num [StandardTwoIsogeny.curve_negY]

/-- The other point over the first coordinate `17` differs from `T` by the
source kernel point. -/
private theorem neg_T_eq_T_add_K : -T = T + K := by
  apply add_left_cancel (a := T)
  rw [add_neg_cancel, ← add_assoc, ← two_nsmul, two_nsmul_T_eq_K]
  exact (StandardTwoIsogeny.kernel_add_self
    (a := a17) (b := b17)).symm

/-- The two affine source points above `x=17` are `T` and `-T`. -/
private theorem source_x_seventeen
    {y : ℚ} (h : Nonsingular standard 17 y) :
    (Point.some 17 y h : Point standard) = T ∨
      (Point.some 17 y h : Point standard) = -T := by
  have hcurve :=
    (StandardTwoIsogeny.curve_equation
      (a := a17) (b := b17)).mp h.left
  norm_num [a17, b17, veluT] at hcurve
  have hfactor : (y - 136) * (y + 136) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hy | hy
  · left
    unfold T
    rw [Point.some.injEq]
    exact ⟨rfl, by linarith⟩
  · right
    rw [neg_T_eq_some, Point.some.injEq]
    exact ⟨rfl, by linarith⟩

/-! ## The second concrete isogeny quotient -/

/-- The source of the standard N17 two-isogeny is covered by the dual image
and its translate by the visible order-four point `T`. -/
theorem source_twoCosetExhaustion :
    MazurProof.X017ExactSequence.TwoCosetExhaustion dualHom T := by
  intro P
  cases P with
  | zero =>
      exact ⟨0, Or.inl (map_zero dualHom).symm⟩
  | some x y h =>
      by_cases hx0 : x = 0
      · have hy : y = 0 :=
          StandardTwoIsogeny.y_zero_of_x_zero h hx0
        have hPK :
            (Point.some x y h : Point standard) = K := by
          unfold K StandardTwoIsogeny.kernelPoint
          rw [Point.some.injEq]
          exact ⟨hx0, hy⟩
        exact ⟨U, Or.inl (by rw [hPK, dualHom_U])⟩
      · obtain ⟨q, hq | hq⟩ :=
          source_x_squareclass h.left hx0
        · obtain ⟨Q, hQ⟩ :=
            exists_dualHom_preimage_of_x_eq_sq h hx0 hq
          exact ⟨Q, Or.inl hQ.symm⟩
        · by_cases hx17 : x = 17
          · have h17 : Nonsingular standard 17 y := hx17 ▸ h
            have hP17 :
                (Point.some x y h : Point standard) =
                  Point.some 17 y h17 := by
              rw [Point.some.injEq]
              exact ⟨hx17, rfl⟩
            rcases source_x_seventeen h17 with hT | hnegT
            · exact
                ⟨0, Or.inr (by
                  rw [hP17, hT, map_zero, add_zero])⟩
            · refine ⟨U, Or.inr ?_⟩
              rw [hP17, hnegT, dualHom_U, neg_T_eq_T_add_K]
          · have hq0 : q ≠ 0 := by
              intro hqz
              apply hx0
              rw [hq, hqz]
              norm_num
            have hnum0 : y + 8 * x ≠ 0 := by
              intro hnum
              have hy : y = -8 * x := by linarith
              have hcurve :=
                (StandardTwoIsogeny.curve_equation
                  (a := a17) (b := b17)).mp h.left
              norm_num [a17, b17, veluT] at hcurve
              rw [hy] at hcurve
              have hfactor : x * (x - 17) ^ 2 = 0 := by
                nlinarith
              have hsquare : (x - 17) ^ 2 = 0 :=
                (mul_eq_zero.mp hfactor).resolve_left hx0
              exact hx17 (sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare))
            generalize hR :
                (Point.some x y h : Point standard) - T = R
            cases R with
            | zero =>
                have hR' := hR
                rw [sub_eq_add_neg, neg_T_eq_some,
                  Point.add_of_X_ne hx17] at hR'
                exact ((Point.some_ne_zero _) hR').elim
            | some x' y' h' =>
                have hx' :
                    x' =
                      addX standard x 17
                        (slope standard x 17 y (-136)) := by
                  have hR' := hR
                  rw [sub_eq_add_neg, neg_T_eq_some,
                    Point.add_of_X_ne hx17] at hR'
                  rw [Point.some.injEq] at hR'
                  exact hR'.1.symm
                let q' : ℚ :=
                  (y + 8 * x) / (q * (x - 17))
                have hxSquare : x' = q' ^ 2 := by
                  rw [hx', sub_T_addX_square h hx0 hx17 hq]
                have hq'0 : q' ≠ 0 := by
                  exact div_ne_zero hnum0
                    (mul_ne_zero hq0 (sub_ne_zero.mpr hx17))
                have hx'0 : x' ≠ 0 := by
                  rw [hxSquare]
                  exact pow_ne_zero 2 hq'0
                obtain ⟨Q, hQ⟩ :=
                  exists_dualHom_preimage_of_x_eq_sq h' hx'0 hxSquare
                have hrange :
                    (Point.some x y h : Point standard) - T =
                      dualHom Q :=
                  hR.trans hQ.symm
                refine ⟨Q, Or.inr ?_⟩
                calc
                  (Point.some x y h : Point standard) =
                      T + (Point.some x y h - T) := by
                    abel
                  _ = T + dualHom Q := by
                    rw [hrange]

/-! ## Cardinality of the right endpoint and the doubling quotient -/

/-! ## Representatives modulo doubling -/

/-- Combining the two independent isogeny covers shows directly that every
source point is a double or `T` plus a double. -/
theorem double_twoCosetExhaustion :
    MazurProof.X017ExactSequence.TwoCosetExhaustion
      (nsmulAddMonoidHom (α := Point standard) 2) T := by
  intro P
  obtain ⟨Q, hP | hP⟩ := source_twoCosetExhaustion P
  · obtain ⟨R, hQ | hQ⟩ :=
      standardDual_twoCosetExhaustion Q
    · refine ⟨R, Or.inl ?_⟩
      rw [hP, hQ, dual_comp_forward]
      rfl
    · refine ⟨R, Or.inl ?_⟩
      rw [hP, hQ, map_add, dualHom_eta, zero_add,
        dual_comp_forward]
      rfl
  · obtain ⟨R, hQ | hQ⟩ :=
      standardDual_twoCosetExhaustion Q
    · refine ⟨R, Or.inr ?_⟩
      rw [hP, hQ, dual_comp_forward]
      rfl
    · refine ⟨R, Or.inr ?_⟩
      rw [hP, hQ, map_add, dualHom_eta, zero_add,
        dual_comp_forward]
      rfl

end

end MazurProof.X017SecondCoset

end

-- ===== FLT.Assumptions.MazurProof.X017TwoTorsion =====
section
/-!
# Rational two-torsion on the standard X₀(17) model

A nonzero rational two-torsion point on

`Y² = X(X² + 30X + 289)`

has vertical coordinate zero.  Its horizontal coordinate therefore vanishes
or is a rational root of `X²+30X+289`.  The latter polynomial is
`(X+15)²+64`, so it has no rational root.  Thus the only rational
two-torsion points are the point at infinity and `(0,0)`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017TwoTorsion

open WeierstrassCurve.Affine
open MazurProof.VeluTwoIsogeny
open MazurProof.X017Model
open MazurProof.RationalPointsN15ExactSequence

noncomputable section

/-- Every rational two-torsion point is either the point at infinity or the
visible kernel point `(0,0)`. -/
theorem twoTorsion_value_eq_zero_or_K
    (P : TwoTorsion (Point standard)) :
    P.1 = 0 ∨ P.1 = K := by
  rcases P with ⟨P, hP⟩
  cases P with
  | zero =>
      exact Or.inl rfl
  | some x y hns =>
      right
      have h2 :
          (Point.some x y hns : Point standard) +
              Point.some x y hns = 0 := by
        simpa [two_nsmul] using hP
      have hyneg : y = negY standard x y := by
        by_contra hne
        have hs := Point.add_self_of_Y_ne
          (W := standard) (h₁ := hns) hne
        rw [h2] at hs
        exact Point.some_ne_zero _ hs.symm
      have hy : y = 0 := by
        rw [StandardTwoIsogeny.curve_negY] at hyneg
        linarith
      have hcurve := StandardTwoIsogeny.curve_equation.mp hns.left
      have hprod :
          x * (x ^ 2 + a17 * x + b17) = 0 := by
        rw [hy] at hcurve
        exact hcurve.symm
      rcases mul_eq_zero.mp hprod with hx | hquad
      · unfold K StandardTwoIsogeny.kernelPoint
        rw [Point.some.injEq]
        exact ⟨hx, hy⟩
      · exfalso
        have hpositive :
            0 < x ^ 2 + a17 * x + b17 := by
          norm_num [a17, b17, veluT]
          nlinarith [sq_nonneg (x + 15)]
        exact (ne_of_gt hpositive) hquad

end

end MazurProof.X017TwoTorsion

end

-- ===== scratch.A6HeightProto =====
section
/-!
# A6 height prototype

This file is intentionally standalone. It prototypes the algebraic backbone for
the duplication-map height argument without importing or wiring into the FLT
torsion files.
-/

open Polynomial

namespace WeierstrassCurve.HeightDoubling

noncomputable section

variable {R : Type*} [CommRing R]

def dupNumPoly (W : WeierstrassCurve R) : Polynomial R :=
  monomial 4 1 - monomial 2 W.b₄ - monomial 1 (2 * W.b₆) - C W.b₈

def dupDenPoly (W : WeierstrassCurve R) : Polynomial R :=
  monomial 3 4 + monomial 2 W.b₂ + monomial 1 (2 * W.b₄) + C W.b₆

def dupNumH (W : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=
  X ^ 4 - W.b₄ * X ^ 2 * Z ^ 2 - 2 * W.b₆ * X * Z ^ 3 - W.b₈ * Z ^ 4

def dupDenH (W : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=
  4 * X ^ 3 * Z + W.b₂ * X ^ 2 * Z ^ 2 + 2 * W.b₄ * X * Z ^ 3 + W.b₆ * Z ^ 4

namespace DupResultantUniversal

end DupResultantUniversal

def dupNumPolyB (b4 b6 b8 : ℚ) : Polynomial ℚ :=
  monomial 4 1 - monomial 2 b4 - monomial 1 (2 * b6) - C b8

def dupDenPolyB (b2 b4 b6 : ℚ) : Polynomial ℚ :=
  monomial 3 4 + monomial 2 b2 + monomial 1 (2 * b4) + C b6

def quotientPolyB (b2 : ℚ) : Polynomial ℚ :=
  monomial 1 (-(1 / 4 : ℚ)) + C (b2 / 16)

def reducedNumPolyB (b2 b4 b6 b8 : ℚ) : Polynomial ℚ :=
  monomial 2 (b2 ^ 2 / 16 - 3 * b4 / 2)
    + monomial 1 (b2 * b4 / 8 - 9 * b6 / 4)
    + C (b2 * b6 / 16 - b8)

abbrev rawResB (b2 b4 b6 b8 : ℚ) : ℚ :=
  b2 ^ 4 * b8 ^ 2
    - 6 * b2 ^ 3 * b4 * b6 * b8
    + 4 * b2 ^ 3 * b6 ^ 3
    + 4 * b2 ^ 2 * b4 ^ 3 * b8
    - 3 * b2 ^ 2 * b4 ^ 2 * b6 ^ 2
    - 48 * b2 ^ 2 * b4 * b8 ^ 2
    + 6 * b2 ^ 2 * b6 ^ 2 * b8
    + 240 * b2 * b4 ^ 2 * b6 * b8
    - 162 * b2 * b4 * b6 ^ 3
    + 192 * b2 * b6 * b8 ^ 2
    - 144 * b4 ^ 4 * b8
    + 108 * b4 ^ 3 * b6 ^ 2
    + 384 * b4 ^ 2 * b8 ^ 2
    - 1296 * b4 * b6 ^ 2 * b8
    + 729 * b6 ^ 4
    - 256 * b8 ^ 3

abbrev rawResCofactor (b2 b4 b6 b8 : ℚ) : ℚ :=
  3 * b2 ^ 2 * b4 * b8
    + b2 ^ 2 * b6 ^ 2
    - 20 * b2 * b4 ^ 2 * b6
    - 8 * b2 * b6 * b8
    + 16 * b4 ^ 4
    - 28 * b4 ^ 2 * b8
    + 81 * b4 * b6 ^ 2
    + 16 * b8 ^ 2

def quadCubicSylvester (a b c d e h k : ℚ) : Matrix (Fin 5) (Fin 5) ℚ :=
  !![k, 0, c, 0, 0;
     h, k, b, c, 0;
     e, h, a, b, c;
     d, e, 0, a, b;
     0, d, 0, 0, a]

lemma det_quadCubicSylvester
    (a b c d e h k : ℚ) :
    (quadCubicSylvester a b c d e h k).det =
      a ^ 3 * k ^ 2 - a ^ 2 * b * h * k - 2 * a ^ 2 * c * e * k
        + a ^ 2 * c * h ^ 2 + a * b ^ 2 * e * k + 3 * a * b * c * d * k
        - a * b * c * e * h - 2 * a * c ^ 2 * d * h + a * c ^ 2 * e ^ 2
        - b ^ 3 * d * k + b ^ 2 * c * d * h - b * c ^ 2 * d * e
        + c ^ 3 * d ^ 2 := by
  rw [Matrix.det_succ_row (quadCubicSylvester a b c d e h k) (4 : Fin 5)]
  simp [quadCubicSylvester, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring_nf

lemma resultant_quadratic_cubic
    (a b c d e h k : ℚ) :
    (monomial 2 a + monomial 1 b + C c).resultant
        (monomial 3 d + monomial 2 e + monomial 1 h + C k) 2 3 =
      a ^ 3 * k ^ 2 - a ^ 2 * b * h * k - 2 * a ^ 2 * c * e * k
        + a ^ 2 * c * h ^ 2 + a * b ^ 2 * e * k + 3 * a * b * c * d * k
        - a * b * c * e * h - 2 * a * c ^ 2 * d * h + a * c ^ 2 * e ^ 2
        - b ^ 3 * d * k + b ^ 2 * c * d * h - b * c ^ 2 * d * e
        + c ^ 3 * d ^ 2 := by
  have hM :
      (monomial 2 a + monomial 1 b + C c).sylvester
          (monomial 3 d + monomial 2 e + monomial 1 h + C k) 2 3 =
        quadCubicSylvester a b c d e h k := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Polynomial.sylvester, quadCubicSylvester, Fin.addCases,
        Polynomial.coeff_monomial]
  rw [Polynomial.resultant, hM, det_quadCubicSylvester]

lemma reduced_resultant_eq_rawResB (b2 b4 b6 b8 : ℚ) :
    16 * (reducedNumPolyB b2 b4 b6 b8).resultant (dupDenPolyB b2 b4 b6) 2 3 =
      rawResB b2 b4 b6 b8 := by
  unfold reducedNumPolyB dupDenPolyB
  rw [resultant_quadratic_cubic]
  ring_nf

lemma resultant_B_eq_rawResB (b2 b4 b6 b8 : ℚ) :
    (dupNumPolyB b4 b6 b8).resultant (dupDenPolyB b2 b4 b6) 4 4 =
      rawResB b2 b4 b6 b8 := by
  let f := dupNumPolyB b4 b6 b8
  let g := dupDenPolyB b2 b4 b6
  let p := quotientPolyB b2
  let r := reducedNumPolyB b2 b4 b6 b8
  have hg3 : g.natDegree ≤ 3 := by
    dsimp [g, dupDenPolyB]
    compute_degree
  have hp1 : p.natDegree ≤ 1 := by
    dsimp [p, quotientPolyB]
    compute_degree
  have hpdeg : p.natDegree + 3 ≤ 4 := by omega
  have hr2 : r.natDegree ≤ 2 := by
    dsimp [r, reducedNumPolyB]
    compute_degree
  have hfgp : f + g * p = r := by
    dsimp [f, g, p, r, dupNumPolyB, dupDenPolyB, quotientPolyB, reducedNumPolyB]
    simp_rw [← Polynomial.monomial_zero_left]
    ring_nf
    rw [Polynomial.monomial_mul_monomial 3 1 (4 : ℚ) (-1 / 4 : ℚ)]
    rw [Polynomial.monomial_mul_monomial 3 0 (4 : ℚ) (b2 * (1 / 16))]
    rw [Polynomial.monomial_mul_monomial 2 1 b2 (-1 / 4 : ℚ)]
    rw [Polynomial.monomial_mul_monomial 2 0 b2 (b2 * (1 / 16))]
    rw [Polynomial.monomial_mul_monomial 1 1 (b4 * 2) (-1 / 4 : ℚ)]
    rw [Polynomial.monomial_mul_monomial 1 0 (b4 * 2) (b2 * (1 / 16))]
    rw [Polynomial.monomial_mul_monomial 0 1 b6 (-1 / 4 : ℚ)]
    rw [Polynomial.monomial_mul_monomial 0 0 b6 (b2 * (1 / 16))]
    ext n
    simp [Polynomial.coeff_monomial, Polynomial.coeff_C]
    split_ifs <;> ring_nf
  calc
    (dupNumPolyB b4 b6 b8).resultant (dupDenPolyB b2 b4 b6) 4 4 =
        f.resultant g 4 4 := rfl
    _ = f.coeff 4 ^ 1 * f.resultant g 4 3 := by
      simpa using
        (Polynomial.resultant_add_right_deg (f := f) (g := g) (m := 4) (n := 3)
          (k := 1) hg3)
    _ = f.resultant g 4 3 := by
      dsimp [f, dupNumPolyB]
      simp [Polynomial.coeff_monomial]
    _ = (f + g * p).resultant g 4 3 := by
      exact
        (Polynomial.resultant_add_mul_left (f := f) (g := g) (p := p) (m := 4) (n := 3)
          hpdeg hg3).symm
    _ = r.resultant g 4 3 := by
      rw [hfgp]
    _ = (-1 : ℚ) ^ (3 * 2) * g.coeff 3 ^ 2 * r.resultant g 2 3 := by
      simpa using
        (Polynomial.resultant_add_left_deg (f := r) (g := g) (m := 2) (n := 3)
          (k := 2) hr2)
    _ = 16 * r.resultant g 2 3 := by
      dsimp [g, dupDenPolyB]
      simp [Polynomial.coeff_monomial]
      norm_num
    _ = rawResB b2 b4 b6 b8 := by
      dsimp [r, g]
      exact reduced_resultant_eq_rawResB b2 b4 b6 b8

lemma rawResB_eq_delta_sq_of_b_relation
    (b2 b4 b6 b8 delta : ℚ)
    (hDelta : delta = -b2 ^ 2 * b8 - 8 * b4 ^ 3 - 27 * b6 ^ 2 + 9 * b2 * b4 * b6)
    (hrel : b2 * b6 - b4 ^ 2 - 4 * b8 = 0) :
    rawResB b2 b4 b6 b8 = delta ^ 2 := by
  subst delta
  calc
    rawResB b2 b4 b6 b8 =
        (-b2 ^ 2 * b8 - 8 * b4 ^ 3 - 27 * b6 ^ 2 + 9 * b2 * b4 * b6) ^ 2
          + 4 * rawResCofactor b2 b4 b6 b8 * (b2 * b6 - b4 ^ 2 - 4 * b8) := by
      ring_nf
    _ = (-b2 ^ 2 * b8 - 8 * b4 ^ 3 - 27 * b6 ^ 2 + 9 * b2 * b4 * b6) ^ 2 := by
      rw [hrel]
      ring

theorem resultant_dupNum_dupDen (W : WeierstrassCurve ℚ) :
    (dupNumPoly W).resultant (dupDenPoly W) 4 4 = W.Δ ^ 2 := by
  have hspec :
      (dupNumPoly W).resultant (dupDenPoly W) 4 4 =
        rawResB W.b₂ W.b₄ W.b₆ W.b₈ := by
    simpa [dupNumPoly, dupDenPoly, dupNumPolyB, dupDenPolyB] using
      resultant_B_eq_rawResB W.b₂ W.b₄ W.b₆ W.b₈
  rw [hspec]
  have hrel : W.b₂ * W.b₆ - W.b₄ ^ 2 - 4 * W.b₈ = 0 := by
    rw [← W.b_relation]
    ring
  exact rawResB_eq_delta_sq_of_b_relation W.b₂ W.b₄ W.b₆ W.b₈ W.Δ rfl hrel

structure DupBezoutAffine (W : WeierstrassCurve ℚ) where
  A : Polynomial ℚ
  B : Polynomial ℚ
  hAdeg : A.degree < (4 : WithBot ℕ)
  hBdeg : B.degree < (4 : WithBot ℕ)
  bezout :
    dupNumPoly W * A + dupDenPoly W * B = C (W.Δ ^ 2)

noncomputable def dup_bezout_affine (W : WeierstrassCurve ℚ) : DupBezoutAffine W :=
  Classical.choice <| by
    have hFdeg : (dupNumPoly W).natDegree ≤ 4 := by
      dsimp [dupNumPoly]
      compute_degree
    have hGdeg : (dupDenPoly W).natDegree ≤ 4 := by
      dsimp [dupDenPoly]
      compute_degree
      omega
    rcases Polynomial.exists_mul_add_mul_eq_C_resultant
        (dupNumPoly W) (dupDenPoly W) hFdeg hGdeg
        (Or.inl (by norm_num : (4 : ℕ) ≠ 0)) with
      ⟨A, B, hAdeg, hBdeg, hbez⟩
    rw [resultant_dupNum_dupDen] at hbez
    exact ⟨
      { A := A
        B := B
        hAdeg := hAdeg
        hBdeg := hBdeg
        bezout := hbez }⟩

noncomputable def naiveLogHeightP1Q (X Z : ℚ) : ℝ :=
  Real.log (max |(X : ℝ)| |(Z : ℝ)|)

private def dupNumHReal (W : WeierstrassCurve ℚ) (X Z : ℝ) : ℝ :=
  X ^ 4 - (W.b₄ : ℝ) * X ^ 2 * Z ^ 2
    - 2 * (W.b₆ : ℝ) * X * Z ^ 3 - (W.b₈ : ℝ) * Z ^ 4

private def dupDenHReal (W : WeierstrassCurve ℚ) (X Z : ℝ) : ℝ :=
  4 * X ^ 3 * Z + (W.b₂ : ℝ) * X ^ 2 * Z ^ 2
    + 2 * (W.b₄ : ℝ) * X * Z ^ 3 + (W.b₆ : ℝ) * Z ^ 4

private def dupHeightRawReal (W : WeierstrassCurve ℚ) (P : ℝ × ℝ) : ℝ :=
  max |dupNumHReal W P.1 P.2| |dupDenHReal W P.1 P.2|

private def p1SupUnit : Set (ℝ × ℝ) :=
  {P | max |P.1| |P.2| = 1}

private lemma ratCast_dupNumH (W : WeierstrassCurve ℚ) (X Z : ℚ) :
    ((dupNumH W X Z : ℚ) : ℝ) = dupNumHReal W (X : ℝ) (Z : ℝ) := by
  simp [dupNumH, dupNumHReal]

private lemma ratCast_dupDenH (W : WeierstrassCurve ℚ) (X Z : ℚ) :
    ((dupDenH W X Z : ℚ) : ℝ) = dupDenHReal W (X : ℝ) (Z : ℝ) := by
  simp [dupDenH, dupDenHReal]

private lemma continuous_dupHeightRawReal (W : WeierstrassCurve ℚ) :
    Continuous (dupHeightRawReal W) := by
  unfold dupHeightRawReal dupNumHReal dupDenHReal
  continuity

private lemma p1SupUnit_isCompact : IsCompact p1SupUnit := by
  let box : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1
  have hbox : IsCompact box := isCompact_Icc.prod isCompact_Icc
  have hclosed : IsClosed p1SupUnit := by
    unfold p1SupUnit
    exact isClosed_eq
      ((continuous_fst.abs).max continuous_snd.abs)
      continuous_const
  have hsubset : p1SupUnit ⊆ box := by
    intro P hP
    change max |P.1| |P.2| = (1 : ℝ) at hP
    have hX : |P.1| ≤ (1 : ℝ) := by
      rw [← hP]
      exact le_max_left |P.1| |P.2|
    have hZ : |P.2| ≤ (1 : ℝ) := by
      rw [← hP]
      exact le_max_right |P.1| |P.2|
    exact ⟨abs_le.mp hX, abs_le.mp hZ⟩
  exact hbox.of_isClosed_subset hclosed hsubset

private lemma dupNumHReal_affine_eval
    (W : WeierstrassCurve ℚ) {X Z : ℝ} (hZ : Z ≠ 0) :
    dupNumHReal W X Z =
      Z ^ 4 * ((dupNumPoly W).map (algebraMap ℚ ℝ)).eval (X / Z) := by
  simp [dupNumHReal, dupNumPoly]
  field_simp [hZ]

private lemma dupDenHReal_affine_eval
    (W : WeierstrassCurve ℚ) {X Z : ℝ} (hZ : Z ≠ 0) :
    dupDenHReal W X Z =
      Z ^ 4 * ((dupDenPoly W).map (algebraMap ℚ ℝ)).eval (X / Z) := by
  simp [dupDenHReal, dupDenPoly]
  field_simp [hZ]

private lemma dupHeightRawReal_ne_zero_on_unit
    (W : WeierstrassCurve ℚ) [W.IsElliptic] {P : ℝ × ℝ}
    (hP : P ∈ p1SupUnit) :
    dupHeightRawReal W P ≠ 0 := by
  intro hheight
  have hmaxle : dupHeightRawReal W P ≤ 0 := by
    simp [hheight]
  have hFabs_le : |dupNumHReal W P.1 P.2| ≤ 0 := (max_le_iff.mp hmaxle).1
  have hGabs_le : |dupDenHReal W P.1 P.2| ≤ 0 := (max_le_iff.mp hmaxle).2
  have hF : dupNumHReal W P.1 P.2 = 0 :=
    abs_eq_zero.mp (le_antisymm hFabs_le (abs_nonneg _))
  have hG : dupDenHReal W P.1 P.2 = 0 :=
    abs_eq_zero.mp (le_antisymm hGabs_le (abs_nonneg _))
  by_cases hZ : P.2 = 0
  · have hXabs : |P.1| = (1 : ℝ) := by
      simpa [p1SupUnit, hZ] using hP
    have hXne : P.1 ≠ 0 := by
      intro hX
      norm_num [hX] at hXabs
    have hX4 : P.1 ^ 4 = 0 := by
      simpa [dupNumHReal, hZ] using hF
    exact (pow_ne_zero 4 hXne) hX4
  · let t : ℝ := P.1 / P.2
    have hF_eval :
        ((dupNumPoly W).map (algebraMap ℚ ℝ)).eval t = 0 := by
      have hscale := dupNumHReal_affine_eval (W := W) (X := P.1) (Z := P.2) hZ
      have hmul : P.2 ^ 4 *
          ((dupNumPoly W).map (algebraMap ℚ ℝ)).eval t = 0 := by
        simpa [t, hscale] using hF
      exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 4 hZ)
    have hG_eval :
        ((dupDenPoly W).map (algebraMap ℚ ℝ)).eval t = 0 := by
      have hscale := dupDenHReal_affine_eval (W := W) (X := P.1) (Z := P.2) hZ
      have hmul : P.2 ^ 4 *
          ((dupDenPoly W).map (algebraMap ℚ ℝ)).eval t = 0 := by
        simpa [t, hscale] using hG
      exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 4 hZ)
    let cert := dup_bezout_affine W
    have hbezR :
        ((dupNumPoly W).map (algebraMap ℚ ℝ)) * (cert.A.map (algebraMap ℚ ℝ))
          + ((dupDenPoly W).map (algebraMap ℚ ℝ)) * (cert.B.map (algebraMap ℚ ℝ))
            = Polynomial.C (((W.Δ ^ 2 : ℚ) : ℝ)) := by
      have hmap := congrArg (Polynomial.map (algebraMap ℚ ℝ)) cert.bezout
      simpa using hmap
    have hzeroDelta : (((W.Δ ^ 2 : ℚ) : ℝ)) = 0 := by
      have hEval := congrArg (fun p : Polynomial ℝ => p.eval t) hbezR
      simpa [hF_eval, hG_eval] using hEval.symm
    have hDelta_ne : (((W.Δ ^ 2 : ℚ) : ℝ)) ≠ 0 := by
      exact_mod_cast (pow_ne_zero 2 W.isUnit_Δ.ne_zero)
    exact hDelta_ne hzeroDelta

private lemma dupHeightRawReal_pos_on_unit
    (W : WeierstrassCurve ℚ) [W.IsElliptic] {P : ℝ × ℝ}
    (hP : P ∈ p1SupUnit) :
    0 < dupHeightRawReal W P := by
  refine lt_of_le_of_ne ?_ ?_
  · exact le_trans (abs_nonneg _) (le_max_left _ _)
  · exact (dupHeightRawReal_ne_zero_on_unit (W := W) hP).symm

private lemma dupHeightRawReal_uniform_lower
    (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ P ∈ p1SupUnit, δ ≤ dupHeightRawReal W P := by
  have hnonempty : p1SupUnit.Nonempty := by
    exact ⟨(1, 0), by norm_num [p1SupUnit]⟩
  obtain ⟨P₀, hP₀, hmin⟩ :=
    p1SupUnit_isCompact.exists_isMinOn hnonempty
      (continuous_dupHeightRawReal W).continuousOn
  exact ⟨dupHeightRawReal W P₀, dupHeightRawReal_pos_on_unit (W := W) hP₀,
    fun P hP => (isMinOn_iff.mp hmin) P hP⟩

private lemma dupNumHReal_scale
    (W : WeierstrassCurve ℚ) {M X Z : ℝ} (hM : M ≠ 0) :
    dupNumHReal W X Z =
      M ^ 4 * dupNumHReal W (X / M) (Z / M) := by
  simp [dupNumHReal]
  field_simp [hM]

private lemma dupDenHReal_scale
    (W : WeierstrassCurve ℚ) {M X Z : ℝ} (hM : M ≠ 0) :
    dupDenHReal W X Z =
      M ^ 4 * dupDenHReal W (X / M) (Z / M) := by
  simp [dupDenHReal]
  field_simp [hM]

private lemma dupHeightRawReal_scale
    (W : WeierstrassCurve ℚ) {M X Z : ℝ} (hMnonneg : 0 ≤ M) (hM : M ≠ 0) :
    dupHeightRawReal W (X, Z) =
      M ^ 4 * dupHeightRawReal W (X / M, Z / M) := by
  have hM4nonneg : 0 ≤ M ^ 4 := pow_nonneg hMnonneg 4
  rw [dupHeightRawReal, dupHeightRawReal,
    dupNumHReal_scale (W := W) (M := M) (X := X) (Z := Z) hM,
    dupDenHReal_scale (W := W) (M := M) (X := X) (Z := Z) hM]
  simp only [abs_mul]
  rw [abs_of_nonneg hM4nonneg, ← mul_max_of_nonneg _ _ hM4nonneg]

/--
Current raw `max |X| |Z|` height lower bound for the duplication binary forms.

The proof uses the affine Bezout certificate to rule out common zeros on the
real sup-unit boundary, extracts a positive minimum by compactness, and scales
back by homogeneity.
-/
theorem dup_projective_height_lower_height_api_seam
    (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    ∃ C0 : ℝ, ∀ X Z : ℚ, (X, Z) ≠ (0, 0) →
      naiveLogHeightP1Q (dupNumH W X Z) (dupDenH W X Z) ≥
        4 * naiveLogHeightP1Q X Z - C0 := by
  obtain ⟨δ, hδpos, hδlower⟩ := dupHeightRawReal_uniform_lower W
  refine ⟨-Real.log δ, ?_⟩
  intro X Z hXZ
  let x : ℝ := X
  let z : ℝ := Z
  let M : ℝ := max |x| |z|
  have hxz_ne : x ≠ 0 ∨ z ≠ 0 := by
    by_contra h
    push Not at h
    apply hXZ
    ext <;> exact_mod_cast (by simp [x, z] at h ⊢; tauto)
  have hMpos : 0 < M := by
    rcases hxz_ne with hx | hz
    · exact lt_of_lt_of_le (abs_pos.mpr hx) (le_max_left |x| |z|)
    · exact lt_of_lt_of_le (abs_pos.mpr hz) (le_max_right |x| |z|)
  have hMnonneg : 0 ≤ M := le_of_lt hMpos
  have hMne : M ≠ 0 := ne_of_gt hMpos
  have hunit : (x / M, z / M) ∈ p1SupUnit := by
    have hMabs : |M| = M := abs_of_nonneg hMnonneg
    simp [p1SupUnit, M, abs_div, hMabs, max_div_div_right hMnonneg, hMne]
  have hscale :
      dupHeightRawReal W (x, z) =
        M ^ 4 * dupHeightRawReal W (x / M, z / M) :=
    dupHeightRawReal_scale (W := W) hMnonneg hMne
  have hM4nonneg : 0 ≤ M ^ 4 := pow_nonneg hMnonneg 4
  have hraw_lower : M ^ 4 * δ ≤ dupHeightRawReal W (x, z) := by
    rw [hscale]
    exact mul_le_mul_of_nonneg_left (hδlower (x / M, z / M) hunit) hM4nonneg
  have hpos_lower : 0 < M ^ 4 * δ :=
    mul_pos (pow_pos hMpos 4) hδpos
  have hlog_lower :
      Real.log (M ^ 4 * δ) ≤ Real.log (dupHeightRawReal W (x, z)) :=
    Real.log_le_log hpos_lower hraw_lower
  have hheight_eq :
      naiveLogHeightP1Q (dupNumH W X Z) (dupDenH W X Z) =
        Real.log (dupHeightRawReal W (x, z)) := by
    simp [naiveLogHeightP1Q, dupHeightRawReal, x, z,
      ratCast_dupNumH, ratCast_dupDenH]
  have hbase_eq :
      naiveLogHeightP1Q X Z = Real.log M := by
    simp [naiveLogHeightP1Q, M, x, z]
  rw [hheight_eq, hbase_eq]
  calc
    Real.log (dupHeightRawReal W (x, z)) ≥ Real.log (M ^ 4 * δ) := hlog_lower
    _ = 4 * Real.log M + Real.log δ := by
      rw [Real.log_mul (pow_ne_zero 4 hMne) (ne_of_gt hδpos), Real.log_pow]
      norm_num
    _ = 4 * Real.log M - -Real.log δ := by
      ring

end

end WeierstrassCurve.HeightDoubling

end

-- ===== scratch.A6TorsionFinite =====
section
/-!
# A6 torsion finiteness via projective x-height

Scratch assembly file for replacing the Mordell-Weil finite-generation input in
`MazurProof.rational_torsion_finite_alias`.

This file follows `scratch/A6_R8_Adversarial_FULL.md`: the height lives on primitive
integer representatives of `P¹(ℚ)`, not on raw rational pairs.
-/

open scoped Matrix
open WeierstrassCurve
open WeierstrassCurve.Affine

noncomputable section

set_option maxHeartbeats 2000000

namespace MazurProof

/-- Primitive integral representatives for `P¹(ℚ)`. -/
structure P1Q where
  X : ℤ
  Z : ℤ
  prim : IsCoprime X Z
  not_both_zero : X ≠ 0 ∨ Z ≠ 0

namespace P1Q

/-- Projective equality between a primitive representative and a raw rational pair. -/
def SameQ (x : P1Q) (A B : ℚ) : Prop :=
  (x.X : ℚ) * B = A * (x.Z : ℚ)

def mulHeight (x : P1Q) : ℕ :=
  max x.X.natAbs x.Z.natAbs

def logHeight (x : P1Q) : ℝ :=
  Real.log (x.mulHeight : ℝ)

def coord (x : P1Q) : ℤ × ℤ :=
  (x.X, x.Z)

lemma one_le_mulHeight (x : P1Q) : 1 ≤ x.mulHeight := by
  rcases x.not_both_zero with hX | hZ
  · have hpos : 0 < x.X.natAbs := Int.natAbs_pos.mpr hX
    exact le_trans hpos (le_max_left _ _)
  · have hpos : 0 < x.Z.natAbs := Int.natAbs_pos.mpr hZ
    exact le_trans hpos (le_max_right _ _)

/-- The logarithmic height of a primitive projective representative is
nonnegative because its multiplicative height is a positive integer. -/
theorem logHeight_nonneg (x : P1Q) : 0 ≤ x.logHeight := by
  rw [logHeight]
  exact Real.log_nonneg (by exact_mod_cast x.one_le_mulHeight)

def infinity : P1Q :=
  { X := 1
    Z := 0
    prim := by simp [isCoprime_zero_right]
    not_both_zero := Or.inl one_ne_zero }

def affine (q : ℚ) : P1Q :=
  { X := q.num
    Z := q.den
    prim := Rat.isCoprime_num_den q
    not_both_zero := Or.inr (by exact_mod_cast q.den_nz) }

private lemma finite_int_natAbs_le (N : ℕ) :
    ({z : ℤ | z.natAbs ≤ N} : Set ℤ).Finite := by
  refine (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset ?_
  intro z hz
  rw [Set.mem_Icc]
  have hzN : |z| ≤ (N : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hz
  exact abs_le.mp hzN

private lemma finite_box (N : ℕ) :
    ({p : ℤ × ℤ | p.1.natAbs ≤ N ∧ p.2.natAbs ≤ N} : Set (ℤ × ℤ)).Finite := by
  simpa [Set.prod_eq, Set.setOf_and] using
    (finite_int_natAbs_le N).prod (finite_int_natAbs_le N)

theorem mulHeight_northcott_nat (N : ℕ) :
    ({x : P1Q | x.mulHeight ≤ N} : Set P1Q).Finite := by
  let S : Set P1Q := {x | x.mulHeight ≤ N}
  let box : Set (ℤ × ℤ) := {p | p.1.natAbs ≤ N ∧ p.2.natAbs ≤ N}
  have hbox : box.Finite := finite_box N
  have himage : (coord '' S).Finite := by
    refine hbox.subset ?_
    intro p hp
    rcases hp with ⟨x, hx, rfl⟩
    dsimp [box, coord]
    dsimp [S, mulHeight] at hx
    exact ⟨le_trans (le_max_left _ _) hx, le_trans (le_max_right _ _) hx⟩
  exact Set.Finite.of_finite_image himage (by
    intro x _ y _ hxy
    cases x
    cases y
    simp [coord] at hxy
    aesop)

theorem logHeight_northcott : Northcott logHeight where
  finite_le B := by
    obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp B)
    refine (mulHeight_northcott_nat N).subset ?_
    intro x hx
    dsimp [logHeight] at hx
    have hle_exp : (x.mulHeight : ℝ) ≤ Real.exp B :=
      Real.le_exp_of_log_le hx
    have hlt : (x.mulHeight : ℝ) < (N : ℝ) :=
      lt_of_le_of_lt hle_exp hN
    exact_mod_cast le_of_lt hlt

end P1Q

noncomputable def xRep (E : WeierstrassCurve ℚ) : (E⁄ℚ).Point → P1Q
  | 0 => P1Q.infinity
  | Point.some x _ _ => P1Q.affine x

noncomputable def xHeight (E : WeierstrassCurve ℚ) (P : (E⁄ℚ).Point) : ℝ :=
  P1Q.logHeight (xRep E P)

private lemma point_xRep_eq_of_xRep_eq
    (E : WeierstrassCurve ℚ) {P Q : (E⁄ℚ).Point}
    (h : xRep E P = xRep E Q) :
    P.xRep = Q.xRep := by
  rcases P with _ | ⟨xP, yP, hP⟩
  · rcases Q with _ | ⟨xQ, yQ, hQ⟩
    · simp
    · exfalso
      have hz := congrArg P1Q.Z h
      have hz' : (0 : ℤ) = xQ.den := by
        simpa [xRep, P1Q.infinity, P1Q.affine] using hz
      have hden : (xQ.den : ℤ) ≠ 0 := by exact_mod_cast xQ.den_nz
      exact hden hz'.symm
  · rcases Q with _ | ⟨xQ, yQ, hQ⟩
    · exfalso
      have hz := congrArg P1Q.Z h
      simp [xRep, P1Q.infinity, P1Q.affine] at hz
    · have hxnum := congrArg P1Q.X h
      have hxden := congrArg P1Q.Z h
      simp [xRep, P1Q.affine] at hxnum hxden
      have hx : xP = xQ := Rat.ext hxnum hxden
      ext i
      fin_cases i <;> simp [Point.xRep_some, hx]

theorem xRep_finite_fibers
    (E : WeierstrassCurve ℚ) (x : P1Q) :
    ({P : (E⁄ℚ).Point | xRep E P = x} : Set (E⁄ℚ).Point).Finite := by
  classical
  by_cases hnonempty : ∃ P : (E⁄ℚ).Point, xRep E P = x
  · rcases hnonempty with ⟨P0, hP0⟩
    have hfin : ({P0, -P0} : Set (E⁄ℚ).Point).Finite := by
      exact (Set.finite_singleton (-P0)).insert P0
    refine hfin.subset ?_
    intro P hP
    have hsame : xRep E P = xRep E P0 := hP.trans hP0.symm
    have hxraw : P.xRep = P0.xRep := point_xRep_eq_of_xRep_eq E hsame
    have h_or := (Point.xRep_eq_xRep_iff (W := E⁄ℚ) (P := P) (Q := P0)).mp hxraw
    rcases h_or with rfl | hneg
    · simp
    · simp [hneg]
  · have hempty : ({P : (E⁄ℚ).Point | xRep E P = x} : Set (E⁄ℚ).Point) = ∅ := by
      ext P
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hP
      exact hnonempty ⟨P, hP⟩
    rw [hempty]
    exact Set.finite_empty

theorem xHeight_northcott (E : WeierstrassCurve ℚ) :
    Northcott (xHeight E) := by
  haveI : Northcott P1Q.logHeight := P1Q.logHeight_northcott
  change Northcott (P1Q.logHeight ∘ xRep E)
  haveI : Filter.TendstoCofinite (xRep E) :=
    (Filter.tendstoCofinite_iff_finite_preimage_singleton _).mpr (by
      intro y
      simpa [Set.preimage] using xRep_finite_fibers E y)
  exact Northcott.comp_of_finite_fibers (h := xRep E) (h' := P1Q.logHeight)

open WeierstrassCurve.HeightDoubling

private def SameP1 (u v : Fin 2 → ℚ) : Prop :=
  ∃ c : ℚ, c ≠ 0 ∧ v = c • u

namespace SameP1

private lemma mk_vec
    {u v : Fin 2 → ℚ} {c : ℚ}
    (hc : c ≠ 0)
    (h0 : v 0 = c * u 0)
    (h1 : v 1 = c * u 1) :
    SameP1 u v := by
  refine ⟨c, hc, ?_⟩
  ext i
  fin_cases i
  · simpa [Pi.smul_apply] using h0
  · simpa [Pi.smul_apply] using h1

private lemma smul_right {u v : Fin 2 → ℚ} (h : SameP1 u v) {c : ℚ} (hc : c ≠ 0) :
    SameP1 u (c • v) := by
  rcases h with ⟨a, ha, rfl⟩
  refine ⟨c * a, mul_ne_zero hc ha, ?_⟩
  ext i
  simp [Pi.smul_apply, mul_assoc]

end SameP1

private lemma dupNumH_scale
    (E : WeierstrassCurve ℚ) (c X Z : ℚ) :
    dupNumH E (c * X) (c * Z) = c ^ 4 * dupNumH E X Z := by
  simp [dupNumH]
  ring

private lemma dupDenH_scale
    (E : WeierstrassCurve ℚ) (c X Z : ℚ) :
    dupDenH E (c * X) (c * Z) = c ^ 4 * dupDenH E X Z := by
  simp [dupDenH]
  ring

private lemma rat_num_eq_self_mul_den (q : ℚ) :
    (q.num : ℚ) = q * (q.den : ℚ) := by
  have hden : ((q.den : ℕ) : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  calc
    (q.num : ℚ) = ((q.num : ℚ) / (q.den : ℚ)) * (q.den : ℚ) := by
      field_simp [hden]
    _ = q * (q.den : ℚ) := by
      rw [Rat.num_div_den]

private lemma p1q_sameQ_of_sameP1_xRep
    (E : WeierstrassCurve ℚ) {Q : (E⁄ℚ).Point} {A B : ℚ}
    (h : SameP1 Q.xRep ![A, B]) :
    P1Q.SameQ (xRep E Q) A B := by
  rcases h with ⟨c, hc, hv⟩
  rcases Q with _ | ⟨x, y, hQ⟩
  · have hB : B = 0 := by
      have h1 := congrFun hv 1
      simpa [Affine.Point.xRep, Pi.smul_apply] using h1
    simp [P1Q.SameQ, xRep, P1Q.infinity, hB]
  · have hA : A = c * x := by
      have h0 := congrFun hv 0
      simpa [Pi.smul_apply] using h0
    have hB : B = c := by
      have h1 := congrFun hv 1
      simpa [Pi.smul_apply] using h1
    simp only [P1Q.SameQ, xRep, P1Q.affine]
    rw [hA, hB]
    have hden_cast : (x.den : ℚ) = (((x.den : ℤ) : ℚ)) := by norm_num
    have hxnum : (x.num : ℚ) = x * (((x.den : ℤ) : ℚ)) := by
      rw [rat_num_eq_self_mul_den, hden_cast]
    rw [hxnum]
    ring

private lemma dupDenH_eq_Yder_sq
    (W : WeierstrassCurve ℚ)
    {x y : ℚ} (hE : Affine.Equation W x y) :
    dupDenH W x 1 = (y - Affine.negY W x y) ^ 2 := by
  have hE0 : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    simpa [Affine.equation_iff'] using hE
  rw [dupDenH, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, Affine.negY]
  linear_combination (norm := ring1) -4 * hE0

private lemma dupNumH_eq_polynomialX_sq_of_Yder_zero
    (W : WeierstrassCurve ℚ)
    {x y : ℚ} (hE : Affine.Equation W x y)
    (hY : y - Affine.negY W x y = 0) :
    dupNumH W x 1 =
      (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) ^ 2 := by
  have hE0 : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    simpa [Affine.equation_iff'] using hE
  have hY0 : 2 * y + W.a₁ * x + W.a₃ = 0 := by
    rw [Affine.negY] at hY
    linear_combination (norm := ring1) hY
  rw [dupNumH, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  linear_combination (norm := ring1)
      (W.a₁ ^ 2 + 4 * W.a₂ + 8 * x) * hE0
    + (-(W.a₁ ^ 2) * y + W.a₁ * W.a₂ * x + W.a₁ * W.a₄
        + W.a₁ * x ^ 2 - W.a₂ * W.a₃ - 2 * W.a₂ * y
        - 2 * W.a₃ * x - 4 * x * y) * hY0

private lemma dupNumH_eq_dupDenH_mul_addX_of_Yder_ne
    (W : WeierstrassCurve ℚ)
    {x y : ℚ} (hE : Affine.Equation W x y)
    (hy : y ≠ Affine.negY W x y) :
    dupNumH W x 1 =
      dupDenH W x 1 * Affine.addX W x x (Affine.slope W x x y y) := by
  have hE0 : y ^ 2 + W.a₁ * x * y + W.a₃ * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    simpa [Affine.equation_iff'] using hE
  have hden : y - Affine.negY W x y ≠ 0 := sub_ne_zero.mpr hy
  rw [dupNumH, dupDenH, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, Affine.addX]
  rw [Affine.slope_of_Y_ne (W := W) rfl hy]
  field_simp [hden]
  rw [Affine.negY]
  linear_combination (norm := ring1)
    (W.a₁ ^ 2 * x + W.a₁ * W.a₃ + 4 * W.a₂ * x
      + 2 * W.a₄ + 6 * x ^ 2) ^ 2 * hE0

private lemma dupNumH_ne_zero_of_Yder_zero
    (W : WeierstrassCurve ℚ)
    {x y : ℚ} (h : Affine.Nonsingular W x y)
    (hY : y - Affine.negY W x y = 0) :
    dupNumH W x 1 ≠ 0 := by
  have hYpoly : (Affine.polynomialY W).evalEval x y = 0 := by
    rw [Affine.evalEval_polynomialY]
    rw [Affine.negY] at hY
    linear_combination (norm := ring1) hY
  have hXpoly : (Affine.polynomialX W).evalEval x y ≠ 0 :=
    h.2.resolve_right (by simpa [hYpoly])
  have hX :
      W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) ≠ 0 := by
    simpa [Affine.evalEval_polynomialX] using hXpoly
  have hN := dupNumH_eq_polynomialX_sq_of_Yder_zero (W := W) h.1 hY
  rw [hN]
  exact pow_ne_zero 2 hX

private theorem xRep_two_nsmul_same_dup_affine
    (W : WeierstrassCurve ℚ)
    (P : Affine.Point W) :
    SameP1 ((2 • P).xRep)
      ![dupNumH W (P.xRep 0) (P.xRep 1),
        dupDenH W (P.xRep 0) (P.xRep 1)] := by
  classical
  rcases P with _ | ⟨x, y, h⟩
  · refine SameP1.mk_vec
      (u := ((2 • (0 : Affine.Point W)).xRep))
      (v := ![dupNumH W ((0 : Affine.Point W).xRep 0) ((0 : Affine.Point W).xRep 1),
        dupDenH W ((0 : Affine.Point W).xRep 0) ((0 : Affine.Point W).xRep 1)])
      (c := 1) one_ne_zero ?_ ?_
    · simp [dupNumH]
    · simp [dupDenH]
  · by_cases hy : y = Affine.negY W x y
    · have hY : y - Affine.negY W x y = 0 := sub_eq_zero.mpr hy
      have htwo :
          2 • (Point.some x y h : Affine.Point W) = 0 := by
        simpa [two_nsmul] using
          (Point.add_self_of_Y_eq (W := W) (h₁ := h) hy)
      have hD0 : dupDenH W x 1 = 0 := by
        rw [dupDenH_eq_Yder_sq (W := W) h.1, hY]
        norm_num
      have hN0 : dupNumH W x 1 ≠ 0 :=
        dupNumH_ne_zero_of_Yder_zero (W := W) h hY
      refine SameP1.mk_vec
        (u := ((2 • (Point.some x y h : Affine.Point W)).xRep))
        (v := ![dupNumH W ((Point.some x y h).xRep 0) ((Point.some x y h).xRep 1),
          dupDenH W ((Point.some x y h).xRep 0) ((Point.some x y h).xRep 1)])
        (c := dupNumH W x 1) hN0 ?_ ?_
      · simp [htwo]
      · simp [htwo, hD0]
    · have hYne : y - Affine.negY W x y ≠ 0 := sub_ne_zero.mpr hy
      have hD_eq : dupDenH W x 1 = (y - Affine.negY W x y) ^ 2 :=
        dupDenH_eq_Yder_sq (W := W) h.1
      have hDne : dupDenH W x 1 ≠ 0 := by
        rw [hD_eq]
        exact pow_ne_zero 2 hYne
      have htwo :
          2 • (Point.some x y h : Affine.Point W) =
            Point.some _ _ (Affine.nonsingular_add h h (fun hxy => hy hxy.right)) := by
        simpa [two_nsmul] using
          (Point.add_self_of_Y_ne (W := W) (h₁ := h) hy)
      have hN :
          dupNumH W x 1 =
            dupDenH W x 1 * Affine.addX W x x (Affine.slope W x x y y) :=
        dupNumH_eq_dupDenH_mul_addX_of_Yder_ne (W := W) h.1 hy
      refine SameP1.mk_vec
        (u := ((2 • (Point.some x y h : Affine.Point W)).xRep))
        (v := ![dupNumH W ((Point.some x y h).xRep 0) ((Point.some x y h).xRep 1),
          dupDenH W ((Point.some x y h).xRep 0) ((Point.some x y h).xRep 1)])
        (c := dupDenH W x 1) hDne ?_ ?_
      · simp [htwo, hN]
      · simp [htwo]

/--
Projective duplication formula, stated against the primitive `P1Q` x-representative.

This is the isolated EC group-law seam from audit §2.A/§5.2.  It should be closed by adapting
the `SameP1` proof in `scratch/A6_R5_EC_Duplication_FULL.md` and then using degree-4
homogeneity to pass from the raw point vector `[x:1]` to the primitive integer rep `[num:den]`.
-/
theorem xRep_two_nsmul_same_dup
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (P : (E⁄ℚ).Point) :
    P1Q.SameQ (xRep E (2 • P))
      (dupNumH E ((xRep E P).X : ℚ) ((xRep E P).Z : ℚ))
      (dupDenH E ((xRep E P).X : ℚ) ((xRep E P).Z : ℚ)) := by
  rcases P with _ | ⟨x, y, hP⟩
  · have htwo : 2 • (Point.zero : (E⁄ℚ).Point) = Point.zero := by
      change 2 • (0 : (E⁄ℚ).Point) = (0 : (E⁄ℚ).Point)
      simp
    rw [htwo]
    simp [P1Q.SameQ, xRep, P1Q.infinity, dupNumH, dupDenH]
  · let d : ℚ := (x.den : ℚ)
    have hd : d ≠ 0 := by
      dsimp [d]
      exact_mod_cast x.den_nz
    have hraw :
        SameP1 ((2 • (Point.some x y hP : (E⁄ℚ).Point)).xRep)
          ![dupNumH E x 1, dupDenH E x 1] := by
      simpa [dupNumH, dupDenH, WeierstrassCurve.baseChange] using
        xRep_two_nsmul_same_dup_affine (W := E⁄ℚ) (Point.some x y hP)
    have hX : ((P1Q.affine x).X : ℚ) = d * x := by
      dsimp [P1Q.affine, d]
      rw [rat_num_eq_self_mul_den]
      ring
    have hZ : ((P1Q.affine x).Z : ℚ) = d * 1 := by
      dsimp [P1Q.affine, d]
      norm_num
    have hscale :
        ![dupNumH E ((P1Q.affine x).X : ℚ) ((P1Q.affine x).Z : ℚ),
          dupDenH E ((P1Q.affine x).X : ℚ) ((P1Q.affine x).Z : ℚ)]
          =
        d ^ 4 • ![dupNumH E x 1, dupDenH E x 1] := by
      ext i <;> fin_cases i
      · rw [hX, hZ, dupNumH_scale]
        simp
      · rw [hX, hZ, dupDenH_scale]
        simp
    have hprim :
        SameP1 ((2 • (Point.some x y hP : (E⁄ℚ).Point)).xRep)
          ![dupNumH E ((P1Q.affine x).X : ℚ) ((P1Q.affine x).Z : ℚ),
            dupDenH E ((P1Q.affine x).X : ℚ) ((P1Q.affine x).Z : ℚ)] := by
      rw [hscale]
      exact SameP1.smul_right hraw (pow_ne_zero 4 hd)
    exact p1q_sameQ_of_sameP1_xRep E hprim

private structure HomogeneousBezoutCertificate where
  F : ℤ → ℤ → ℤ
  G : ℤ → ℤ → ℤ
  D : ℤ
  Ux : ℤ → ℤ → ℤ
  Vx : ℤ → ℤ → ℤ
  Uz : ℤ → ℤ → ℤ
  Vz : ℤ → ℤ → ℤ
  bezoutX : ∀ X Z : ℤ,
    D * X ^ 7 = Ux X Z * F X Z + Vx X Z * G X Z
  bezoutZ : ∀ X Z : ℤ,
    D * Z ^ 7 = Uz X Z * F X Z + Vz X Z * G X Z

namespace HomogeneousBezoutCertificate

private lemma dvd_natAbs_add_mul_of_dvd_natAbs
    {d : ℕ} {a b u v : ℤ}
    (ha : d ∣ a.natAbs) (hb : d ∣ b.natAbs) :
    d ∣ (u * a + v * b).natAbs := by
  have haZ : (d : ℤ) ∣ a := by
    exact Int.natCast_dvd.mpr ha
  have hbZ : (d : ℤ) ∣ b := by
    exact Int.natCast_dvd.mpr hb
  have hlinZ : (d : ℤ) ∣ u * a + v * b := by
    exact dvd_add (dvd_mul_of_dvd_right haZ u) (dvd_mul_of_dvd_right hbZ v)
  exact Int.natCast_dvd.mp hlinZ

private theorem gcd_dvd_D_natAbs_of_natAbs_coprime
    (C : HomogeneousBezoutCertificate)
    {X Z : ℤ}
    (hcop : Nat.Coprime X.natAbs Z.natAbs) :
    Nat.gcd (C.F X Z).natAbs (C.G X Z).natAbs ∣ C.D.natAbs := by
  let d : ℕ := Nat.gcd (C.F X Z).natAbs (C.G X Z).natAbs
  have hdF : d ∣ (C.F X Z).natAbs := Nat.gcd_dvd_left _ _
  have hdG : d ∣ (C.G X Z).natAbs := Nat.gcd_dvd_right _ _
  have hd_comboX :
      d ∣ (C.Ux X Z * C.F X Z + C.Vx X Z * C.G X Z).natAbs :=
    dvd_natAbs_add_mul_of_dvd_natAbs hdF hdG
  have hd_comboZ :
      d ∣ (C.Uz X Z * C.F X Z + C.Vz X Z * C.G X Z).natAbs :=
    dvd_natAbs_add_mul_of_dvd_natAbs hdF hdG
  have hd_DX : d ∣ (C.D * X ^ 7).natAbs := by
    simpa [C.bezoutX X Z] using hd_comboX
  have hd_DZ : d ∣ (C.D * Z ^ 7).natAbs := by
    simpa [C.bezoutZ X Z] using hd_comboZ
  have hd_DX' : d ∣ C.D.natAbs * X.natAbs ^ 7 := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using hd_DX
  have hd_DZ' : d ∣ C.D.natAbs * Z.natAbs ^ 7 := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using hd_DZ
  have hpowcop : Nat.Coprime (X.natAbs ^ 7) (Z.natAbs ^ 7) := by
    exact hcop.pow 7 7
  have hd_gcd :
      d ∣ Nat.gcd (C.D.natAbs * X.natAbs ^ 7)
                   (C.D.natAbs * Z.natAbs ^ 7) :=
    Nat.dvd_gcd hd_DX' hd_DZ'
  have hgcd_eval :
      Nat.gcd (C.D.natAbs * X.natAbs ^ 7)
                   (C.D.natAbs * Z.natAbs ^ 7) = C.D.natAbs := by
    calc
      Nat.gcd (C.D.natAbs * X.natAbs ^ 7)
          (C.D.natAbs * Z.natAbs ^ 7)
          = C.D.natAbs * Nat.gcd (X.natAbs ^ 7) (Z.natAbs ^ 7) := by
            exact Nat.gcd_mul_left (C.D.natAbs) (X.natAbs ^ 7) (Z.natAbs ^ 7)
      _ = C.D.natAbs := by
        rw [hpowcop.gcd_eq_one]
        simp
  simpa [hgcd_eval] using hd_gcd

end HomogeneousBezoutCertificate

private def dupBezoutUZ (E : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=
  E.Δ * ((E.b₂ ^ 2 - 32 * E.b₄) * Z ^ 3
    - 8 * E.b₂ * X * Z ^ 2 - 48 * X ^ 2 * Z)

private def dupBezoutVZ (E : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=
  E.Δ * ((E.b₂ * E.b₄ - 27 * E.b₆) * Z ^ 3
    - 10 * E.b₄ * X * Z ^ 2 - E.b₂ * X ^ 2 * Z + 12 * X ^ 3)

private def dupBezoutUX (E : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=
  let A := E.b₂ ^ 2 * E.b₄ * E.b₆ - E.b₂ * E.b₄ ^ 3
    - 5 * E.b₂ * E.b₆ ^ 2 + E.b₄ ^ 2 * E.b₆
  let B := E.b₂ ^ 2 * E.b₆ ^ 2 - 13 * E.b₂ * E.b₄ ^ 2 * E.b₆
    + 12 * E.b₄ ^ 4 + 44 * E.b₄ * E.b₆ ^ 2
  let C := E.b₂ * E.b₄ * E.b₆ - E.b₄ ^ 3 - 4 * E.b₆ ^ 2
  E.Δ ^ 2 * X ^ 3 + A * E.Δ * Z * X ^ 2
    - (B * E.Δ / 4) * Z ^ 2 * X + ((3 / 2 : ℚ) * E.b₆ * C * E.Δ) * Z ^ 3

private def dupBezoutVX (E : WeierstrassCurve ℚ) (X Z : ℚ) : ℚ :=
  let A := E.b₂ ^ 2 * E.b₄ * E.b₆ - E.b₂ * E.b₄ ^ 3
    - 5 * E.b₂ * E.b₆ ^ 2 + E.b₄ ^ 2 * E.b₆
  let C := E.b₂ * E.b₄ * E.b₆ - E.b₄ ^ 3 - 4 * E.b₆ ^ 2
  let D := E.b₂ ^ 2 * E.b₆ ^ 2 - 6 * E.b₂ * E.b₄ ^ 2 * E.b₆
    + 5 * E.b₄ ^ 4 + 16 * E.b₄ * E.b₆ ^ 2
  let fcoef := E.b₂ ^ 3 * E.b₆ ^ 2 - 2 * E.b₂ ^ 2 * E.b₄ ^ 2 * E.b₆
    + E.b₂ * E.b₄ ^ 4 - 52 * E.b₂ * E.b₄ * E.b₆ ^ 2
    + 52 * E.b₄ ^ 3 * E.b₆ + 192 * E.b₆ ^ 3
  0 - (A * E.Δ / 4) * X ^ 3 - (D * E.Δ / 4) * Z * X ^ 2
    - (fcoef * E.Δ / 16) * Z ^ 2 * X
    + ((3 / 8 : ℚ) * (E.b₂ * E.b₆ - E.b₄ ^ 2) * C * E.Δ) * Z ^ 3

private lemma b₈_eq_of_b_relation (E : WeierstrassCurve ℚ) :
    E.b₈ = (E.b₂ * E.b₆ - E.b₄ ^ 2) / 4 := by
  have hrel : E.b₂ * E.b₆ - E.b₄ ^ 2 - 4 * E.b₈ = 0 := by
    rw [← E.b_relation]
    ring
  linear_combination (norm := ring1) (-1 / 4 : ℚ) * hrel

private lemma dup_bezoutZ_Q
    (E : WeierstrassCurve ℚ) (X Z : ℚ) :
    E.Δ ^ 2 * Z ^ 7 =
      dupBezoutUZ E X Z * dupNumH E X Z + dupBezoutVZ E X Z * dupDenH E X Z := by
  simp [dupBezoutUZ, dupBezoutVZ, dupNumH, dupDenH, WeierstrassCurve.Δ,
    b₈_eq_of_b_relation]
  ring

private lemma dup_bezoutX_Q
    (E : WeierstrassCurve ℚ) (X Z : ℚ) :
    E.Δ ^ 2 * X ^ 7 =
      dupBezoutUX E X Z * dupNumH E X Z + dupBezoutVX E X Z * dupDenH E X Z := by
  simp [dupBezoutUX, dupBezoutVX, dupNumH, dupDenH, WeierstrassCurve.Δ,
    b₈_eq_of_b_relation]
  ring_nf

private def IsRatInt (q : ℚ) : Prop :=
  ∃ z : ℤ, q = z

namespace IsRatInt

private lemma add {a b : ℚ} (ha : IsRatInt a) (hb : IsRatInt b) :
    IsRatInt (a + b) := by
  rcases ha with ⟨m, rfl⟩
  rcases hb with ⟨n, rfl⟩
  exact ⟨m + n, by norm_num⟩

private lemma den_eq_one {q : ℚ} (hq : IsRatInt q) :
    q.den = 1 := by
  rcases hq with ⟨z, rfl⟩
  simp

private lemma of_eq {a b : ℚ} (ha : IsRatInt a) (h : a = b) :
    IsRatInt b := by
  rw [← h]
  exact ha

end IsRatInt

private def denProd (qs : List ℚ) : ℕ :=
  qs.foldr (fun q n => q.den * n) 1

private lemma den_dvd_denProd_of_mem {q : ℚ} {qs : List ℚ} (h : q ∈ qs) :
    q.den ∣ denProd qs := by
  induction qs with
  | nil => simp at h
  | cons r rs ih =>
      simp [denProd] at h ⊢
      rcases h with hqr | hmem
      · subst q
        exact Nat.dvd_mul_right r.den (denProd rs)
      · exact dvd_mul_of_dvd_right (ih hmem) r.den

private lemma denProd_pos (qs : List ℚ) :
    0 < denProd qs := by
  induction qs with
  | nil => simp [denProd]
  | cons q qs ih =>
      change 0 < q.den * denProd qs
      exact Nat.mul_pos q.den_pos ih

private lemma isRatInt_nat_mul_of_den_dvd {L : ℕ} {q : ℚ} (h : q.den ∣ L) :
    IsRatInt ((L : ℚ) * q) := by
  rcases h with ⟨k, hk⟩
  refine ⟨q.num * (k : ℤ), ?_⟩
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  calc
    (L : ℚ) * q = ((q.den * k : ℕ) : ℚ) * q := by rw [← hk]
    _ = ((q.den * k : ℕ) : ℚ) * ((q.num : ℚ) / (q.den : ℚ)) := by
      rw [Rat.num_div_den]
    _ = ((q.num * (k : ℤ) : ℤ) : ℚ) := by
      field_simp [hden]
      norm_num
      ring

private lemma isRatInt_nat_mul_coeff_monomial {L : ℕ} (X Z : ℤ) {c : ℚ}
    (hc : c.den ∣ L) (a b : ℕ) :
    IsRatInt ((L : ℚ) * (c * (X : ℚ) ^ a * (Z : ℚ) ^ b)) := by
  obtain ⟨m, hm⟩ := isRatInt_nat_mul_of_den_dvd (L := L) hc
  refine ⟨m * X ^ a * Z ^ b, ?_⟩
  calc
    (L : ℚ) * (c * (X : ℚ) ^ a * (Z : ℚ) ^ b) =
        ((L : ℚ) * c) * (X : ℚ) ^ a * (Z : ℚ) ^ b := by ring
    _ = (m * X ^ a * Z ^ b : ℤ) := by
      rw [hm]
      norm_num

private def dupUXA (E : WeierstrassCurve ℚ) : ℚ :=
  E.b₂ ^ 2 * E.b₄ * E.b₆ - E.b₂ * E.b₄ ^ 3
    - 5 * E.b₂ * E.b₆ ^ 2 + E.b₄ ^ 2 * E.b₆

private def dupUXB (E : WeierstrassCurve ℚ) : ℚ :=
  E.b₂ ^ 2 * E.b₆ ^ 2 - 13 * E.b₂ * E.b₄ ^ 2 * E.b₆
    + 12 * E.b₄ ^ 4 + 44 * E.b₄ * E.b₆ ^ 2

private def dupUXC (E : WeierstrassCurve ℚ) : ℚ :=
  E.b₂ * E.b₄ * E.b₆ - E.b₄ ^ 3 - 4 * E.b₆ ^ 2

private def dupVXD (E : WeierstrassCurve ℚ) : ℚ :=
  E.b₂ ^ 2 * E.b₆ ^ 2 - 6 * E.b₂ * E.b₄ ^ 2 * E.b₆
    + 5 * E.b₄ ^ 4 + 16 * E.b₄ * E.b₆ ^ 2

private def dupVXf (E : WeierstrassCurve ℚ) : ℚ :=
  E.b₂ ^ 3 * E.b₆ ^ 2 - 2 * E.b₂ ^ 2 * E.b₄ ^ 2 * E.b₆
    + E.b₂ * E.b₄ ^ 4 - 52 * E.b₂ * E.b₄ * E.b₆ ^ 2
    + 52 * E.b₄ ^ 3 * E.b₆ + 192 * E.b₆ ^ 3

private def cUZ0 (E : WeierstrassCurve ℚ) : ℚ :=
  E.Δ * (E.b₂ ^ 2 - 32 * E.b₄)

private def cUZ1 (E : WeierstrassCurve ℚ) : ℚ :=
  -8 * E.Δ * E.b₂

private def cUZ2 (E : WeierstrassCurve ℚ) : ℚ :=
  -48 * E.Δ

private def cVZ0 (E : WeierstrassCurve ℚ) : ℚ :=
  E.Δ * (E.b₂ * E.b₄ - 27 * E.b₆)

private def cVZ1 (E : WeierstrassCurve ℚ) : ℚ :=
  -10 * E.Δ * E.b₄

private def cVZ2 (E : WeierstrassCurve ℚ) : ℚ :=
  -E.Δ * E.b₂

private def cVZ3 (E : WeierstrassCurve ℚ) : ℚ :=
  12 * E.Δ

private def cUX0 (E : WeierstrassCurve ℚ) : ℚ :=
  (3 / 2 : ℚ) * E.b₆ * dupUXC E * E.Δ

private def cUX1 (E : WeierstrassCurve ℚ) : ℚ :=
  -(dupUXB E * E.Δ / 4)

private def cUX2 (E : WeierstrassCurve ℚ) : ℚ :=
  dupUXA E * E.Δ

private def cUX3 (E : WeierstrassCurve ℚ) : ℚ :=
  E.Δ ^ 2

private def cVX0 (E : WeierstrassCurve ℚ) : ℚ :=
  (3 / 8 : ℚ) * (E.b₂ * E.b₆ - E.b₄ ^ 2) * dupUXC E * E.Δ

private def cVX1 (E : WeierstrassCurve ℚ) : ℚ :=
  -(dupVXf E * E.Δ / 16)

private def cVX2 (E : WeierstrassCurve ℚ) : ℚ :=
  -(dupVXD E * E.Δ / 4)

private def cVX3 (E : WeierstrassCurve ℚ) : ℚ :=
  -(dupUXA E * E.Δ / 4)

private def dupClearCoeffs (E : WeierstrassCurve ℚ) : List ℚ :=
  [1, -E.b₄, -(2 * E.b₆), -E.b₈, 4, E.b₂, 2 * E.b₄, E.b₆,
    E.Δ ^ 2,
    cUZ0 E, cUZ1 E, cUZ2 E,
    cVZ0 E, cVZ1 E, cVZ2 E, cVZ3 E,
    cUX0 E, cUX1 E, cUX2 E, cUX3 E,
    cVX0 E, cVX1 E, cVX2 E, cVX3 E]

@[irreducible] private def dupClearDen (E : WeierstrassCurve ℚ) : ℕ :=
  denProd (dupClearCoeffs E)

private lemma dupClearDen_pos (E : WeierstrassCurve ℚ) :
    0 < dupClearDen E := by
  rw [dupClearDen]
  exact denProd_pos _

private lemma dupCoeff_dvd_clearDen {E : WeierstrassCurve ℚ} {c : ℚ}
    (h : c ∈ dupClearCoeffs E) :
    c.den ∣ dupClearDen E := by
  rw [dupClearDen]
  exact den_dvd_denProd_of_mem h

private lemma dupCoeff_clear_isRatInt {E : WeierstrassCurve ℚ} (X Z : ℤ)
    {c : ℚ} (h : c ∈ dupClearCoeffs E) (a b : ℕ) :
    IsRatInt ((dupClearDen E : ℚ) * (c * (X : ℚ) ^ a * (Z : ℚ) ^ b)) :=
  isRatInt_nat_mul_coeff_monomial (L := dupClearDen E) X Z
    (dupCoeff_dvd_clearDen h) a b

private lemma dupNumH_clear_isRatInt
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    IsRatInt ((dupClearDen E : ℚ) * dupNumH E (X : ℚ) (Z : ℚ)) := by
  have h1 := dupCoeff_clear_isRatInt (E := E) X Z (c := (1 : ℚ))
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 4 0
  have h2 := dupCoeff_clear_isRatInt (E := E) X Z (c := -E.b₄)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 2 2
  have h3 := dupCoeff_clear_isRatInt (E := E) X Z (c := -(2 * E.b₆))
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 1 3
  have h4 := dupCoeff_clear_isRatInt (E := E) X Z (c := -E.b₈)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 0 4
  refine IsRatInt.of_eq (((h1.add h2).add h3).add h4) ?_
  simp [dupNumH]
  ring

private lemma dupDenH_clear_isRatInt
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    IsRatInt ((dupClearDen E : ℚ) * dupDenH E (X : ℚ) (Z : ℚ)) := by
  have h1 := dupCoeff_clear_isRatInt (E := E) X Z (c := (4 : ℚ))
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 3 1
  have h2 := dupCoeff_clear_isRatInt (E := E) X Z (c := E.b₂)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 2 2
  have h3 := dupCoeff_clear_isRatInt (E := E) X Z (c := 2 * E.b₄)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 1 3
  have h4 := dupCoeff_clear_isRatInt (E := E) X Z (c := E.b₆)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 0 4
  refine IsRatInt.of_eq (((h1.add h2).add h3).add h4) ?_
  simp [dupDenH]
  ring

private lemma dupBezoutUZ_clear_isRatInt
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    IsRatInt ((dupClearDen E : ℚ) * dupBezoutUZ E (X : ℚ) (Z : ℚ)) := by
  have h1 := dupCoeff_clear_isRatInt (E := E) X Z (c := cUZ0 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 0 3
  have h2 := dupCoeff_clear_isRatInt (E := E) X Z (c := cUZ1 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 1 2
  have h3 := dupCoeff_clear_isRatInt (E := E) X Z (c := cUZ2 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 2 1
  refine IsRatInt.of_eq ((h1.add h2).add h3) ?_
  simp [dupBezoutUZ, cUZ0, cUZ1, cUZ2]
  ring

private lemma dupBezoutVZ_clear_isRatInt
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    IsRatInt ((dupClearDen E : ℚ) * dupBezoutVZ E (X : ℚ) (Z : ℚ)) := by
  have h1 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVZ0 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 0 3
  have h2 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVZ1 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 1 2
  have h3 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVZ2 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 2 1
  have h4 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVZ3 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 3 0
  refine IsRatInt.of_eq (((h1.add h2).add h3).add h4) ?_
  simp [dupBezoutVZ, cVZ0, cVZ1, cVZ2, cVZ3]
  ring

private lemma dupBezoutUX_clear_isRatInt
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    IsRatInt ((dupClearDen E : ℚ) * dupBezoutUX E (X : ℚ) (Z : ℚ)) := by
  have h1 := dupCoeff_clear_isRatInt (E := E) X Z (c := cUX3 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 3 0
  have h2 := dupCoeff_clear_isRatInt (E := E) X Z (c := cUX2 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 2 1
  have h3 := dupCoeff_clear_isRatInt (E := E) X Z (c := cUX1 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 1 2
  have h4 := dupCoeff_clear_isRatInt (E := E) X Z (c := cUX0 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 0 3
  refine IsRatInt.of_eq (((h1.add h2).add h3).add h4) ?_
  simp [dupBezoutUX, cUX0, cUX1, cUX2, cUX3, dupUXA, dupUXB, dupUXC]
  ring

private lemma dupBezoutVX_clear_isRatInt
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    IsRatInt ((dupClearDen E : ℚ) * dupBezoutVX E (X : ℚ) (Z : ℚ)) := by
  have h1 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVX3 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 3 0
  have h2 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVX2 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 2 1
  have h3 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVX1 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 1 2
  have h4 := dupCoeff_clear_isRatInt (E := E) X Z (c := cVX0 E)
    (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]) 0 3
  refine IsRatInt.of_eq (((h1.add h2).add h3).add h4) ?_
  simp [dupBezoutVX, cVX0, cVX1, cVX2, cVX3, dupUXA, dupUXC, dupVXD, dupVXf]
  ring

private lemma deltaSq_clear_isRatInt (E : WeierstrassCurve ℚ) :
    IsRatInt (((dupClearDen E : ℚ) ^ 2) * E.Δ ^ 2) := by
  have hbase : IsRatInt ((dupClearDen E : ℚ) * (E.Δ ^ 2)) :=
    isRatInt_nat_mul_of_den_dvd (L := dupClearDen E)
      (q := E.Δ ^ 2)
      (dupCoeff_dvd_clearDen (E := E) (c := E.Δ ^ 2) (by simp only [dupClearCoeffs, List.mem_cons, List.not_mem_nil, true_or, or_true]))
  obtain ⟨m, hm⟩ := hbase
  refine ⟨(dupClearDen E : ℤ) * m, ?_⟩
  calc
    ((dupClearDen E : ℚ) ^ 2) * E.Δ ^ 2 =
        (dupClearDen E : ℚ) * ((dupClearDen E : ℚ) * E.Δ ^ 2) := by ring_nf
    _ = (((dupClearDen E : ℤ) * m : ℤ) : ℚ) := by
      rw [hm]
      norm_cast

private def clearRatInt (q : ℚ) : ℤ :=
  q.num

private lemma clearRatInt_spec {q : ℚ} (hq : IsRatInt q) :
    (clearRatInt q : ℚ) = q := by
  exact Rat.coe_int_num_of_den_eq_one (IsRatInt.den_eq_one hq)

private def dupFZ (E : WeierstrassCurve ℚ) (X Z : ℤ) : ℤ :=
  clearRatInt ((dupClearDen E : ℚ) * dupNumH E (X : ℚ) (Z : ℚ))

private def dupGZ (E : WeierstrassCurve ℚ) (X Z : ℤ) : ℤ :=
  clearRatInt ((dupClearDen E : ℚ) * dupDenH E (X : ℚ) (Z : ℚ))

private def dupUXZ (E : WeierstrassCurve ℚ) (X Z : ℤ) : ℤ :=
  clearRatInt ((dupClearDen E : ℚ) * dupBezoutUX E (X : ℚ) (Z : ℚ))

private def dupVXZ (E : WeierstrassCurve ℚ) (X Z : ℤ) : ℤ :=
  clearRatInt ((dupClearDen E : ℚ) * dupBezoutVX E (X : ℚ) (Z : ℚ))

private def dupUZZ (E : WeierstrassCurve ℚ) (X Z : ℤ) : ℤ :=
  clearRatInt ((dupClearDen E : ℚ) * dupBezoutUZ E (X : ℚ) (Z : ℚ))

private def dupVZZ (E : WeierstrassCurve ℚ) (X Z : ℤ) : ℤ :=
  clearRatInt ((dupClearDen E : ℚ) * dupBezoutVZ E (X : ℚ) (Z : ℚ))

private def dupDZ (E : WeierstrassCurve ℚ) : ℤ :=
  clearRatInt (((dupClearDen E : ℚ) ^ 2) * E.Δ ^ 2)

private lemma dupFZ_spec (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    (dupFZ E X Z : ℚ) =
      (dupClearDen E : ℚ) * dupNumH E (X : ℚ) (Z : ℚ) := by
  exact clearRatInt_spec (dupNumH_clear_isRatInt E X Z)

private lemma dupGZ_spec (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    (dupGZ E X Z : ℚ) =
      (dupClearDen E : ℚ) * dupDenH E (X : ℚ) (Z : ℚ) := by
  exact clearRatInt_spec (dupDenH_clear_isRatInt E X Z)

private lemma dupUXZ_spec (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    (dupUXZ E X Z : ℚ) =
      (dupClearDen E : ℚ) * dupBezoutUX E (X : ℚ) (Z : ℚ) := by
  exact clearRatInt_spec (dupBezoutUX_clear_isRatInt E X Z)

private lemma dupVXZ_spec (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    (dupVXZ E X Z : ℚ) =
      (dupClearDen E : ℚ) * dupBezoutVX E (X : ℚ) (Z : ℚ) := by
  exact clearRatInt_spec (dupBezoutVX_clear_isRatInt E X Z)

private lemma dupUZZ_spec (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    (dupUZZ E X Z : ℚ) =
      (dupClearDen E : ℚ) * dupBezoutUZ E (X : ℚ) (Z : ℚ) := by
  exact clearRatInt_spec (dupBezoutUZ_clear_isRatInt E X Z)

private lemma dupVZZ_spec (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    (dupVZZ E X Z : ℚ) =
      (dupClearDen E : ℚ) * dupBezoutVZ E (X : ℚ) (Z : ℚ) := by
  exact clearRatInt_spec (dupBezoutVZ_clear_isRatInt E X Z)

private lemma dupDZ_spec (E : WeierstrassCurve ℚ) :
    (dupDZ E : ℚ) = ((dupClearDen E : ℚ) ^ 2) * E.Δ ^ 2 := by
  exact clearRatInt_spec (deltaSq_clear_isRatInt E)

private lemma dup_bezoutX_Z
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    dupDZ E * X ^ 7 =
      dupUXZ E X Z * dupFZ E X Z + dupVXZ E X Z * dupGZ E X Z := by
  have hq :
      (dupDZ E : ℚ) * (X : ℚ) ^ 7 =
        (dupUXZ E X Z : ℚ) * (dupFZ E X Z : ℚ)
          + (dupVXZ E X Z : ℚ) * (dupGZ E X Z : ℚ) := by
    rw [dupDZ_spec, dupUXZ_spec, dupVXZ_spec, dupFZ_spec, dupGZ_spec]
    have h := dup_bezoutX_Q E (X : ℚ) (Z : ℚ)
    linear_combination (norm := ring1) ((dupClearDen E : ℚ) ^ 2) * h
  exact_mod_cast hq

private lemma dup_bezoutZ_Z
    (E : WeierstrassCurve ℚ) (X Z : ℤ) :
    dupDZ E * Z ^ 7 =
      dupUZZ E X Z * dupFZ E X Z + dupVZZ E X Z * dupGZ E X Z := by
  have hq :
      (dupDZ E : ℚ) * (Z : ℚ) ^ 7 =
        (dupUZZ E X Z : ℚ) * (dupFZ E X Z : ℚ)
          + (dupVZZ E X Z : ℚ) * (dupGZ E X Z : ℚ) := by
    rw [dupDZ_spec, dupUZZ_spec, dupVZZ_spec, dupFZ_spec, dupGZ_spec]
    have h := dup_bezoutZ_Q E (X : ℚ) (Z : ℚ)
    linear_combination (norm := ring1) ((dupClearDen E : ℚ) ^ 2) * h
  exact_mod_cast hq

private def dupIntegralCertificate (E : WeierstrassCurve ℚ) :
    HomogeneousBezoutCertificate where
  F := dupFZ E
  G := dupGZ E
  D := dupDZ E
  Ux := dupUXZ E
  Vx := dupVXZ E
  Uz := dupUZZ E
  Vz := dupVZZ E
  bezoutX := dup_bezoutX_Z E
  bezoutZ := dup_bezoutZ_Z E

private lemma p1q_naiveLogHeight_intCast_eq_logHeight (x : P1Q) :
    naiveLogHeightP1Q (x.X : ℚ) (x.Z : ℚ) = P1Q.logHeight x := by
  simp [naiveLogHeightP1Q, P1Q.logHeight, P1Q.mulHeight]

private lemma p1q_natAbs_coprime (x : P1Q) :
    Nat.Coprime x.X.natAbs x.Z.natAbs := by
  rw [Nat.coprime_iff_gcd_eq_one]
  rw [← Int.gcd_eq_natAbs]
  exact Int.isCoprime_iff_gcd_eq_one.mp x.prim

private lemma sameQ_int_scalar (y : P1Q) (A B : ℤ)
    (h : P1Q.SameQ y (A : ℚ) (B : ℚ)) :
    ∃ n : ℤ, A = n * y.X ∧ B = n * y.Z := by
  rcases y.prim with ⟨u, v, huv⟩
  let n : ℤ := u * A + v * B
  have hq : (y.X : ℚ) * (B : ℚ) = (A : ℚ) * (y.Z : ℚ) := by
    simpa [P1Q.SameQ] using h
  refine ⟨n, ?_, ?_⟩
  · have hcross : A * y.Z = y.X * B := by exact_mod_cast hq.symm
    calc
      A = (u * y.X + v * y.Z) * A := by rw [huv]; ring
      _ = (u * A + v * B) * y.X := by
        linear_combination (norm := ring1) v * hcross
  · have hcross : y.X * B = A * y.Z := by exact_mod_cast hq
    calc
      B = (u * y.X + v * y.Z) * B := by rw [huv]; ring
      _ = (u * A + v * B) * y.Z := by
        linear_combination (norm := ring1) u * hcross

private lemma logHeight_ge_log_int_pair_sub_log_of_gcd_dvd
    (y : P1Q) {A B : ℤ} {N : ℕ}
    (hSame : P1Q.SameQ y (A : ℚ) (B : ℚ))
    (hAB : A ≠ 0 ∨ B ≠ 0)
    (hNpos : 0 < N)
    (hgcd : Nat.gcd A.natAbs B.natAbs ∣ N) :
    P1Q.logHeight y ≥ Real.log (max A.natAbs B.natAbs : ℝ) - Real.log (N : ℝ) := by
  obtain ⟨n, hA, hB⟩ := sameQ_int_scalar y A B hSame
  have hnne : n ≠ 0 := by
    intro hn
    rcases hAB with hA0 | hB0
    · apply hA0
      rw [hA, hn]
      simp
    · apply hB0
      rw [hB, hn]
      simp
  have hycop := p1q_natAbs_coprime y
  have hgcd_eq : Nat.gcd A.natAbs B.natAbs = n.natAbs := by
    rw [hA, hB, Int.natAbs_mul, Int.natAbs_mul]
    calc
      Nat.gcd (n.natAbs * y.X.natAbs) (n.natAbs * y.Z.natAbs)
          = n.natAbs * Nat.gcd y.X.natAbs y.Z.natAbs := by
            exact Nat.gcd_mul_left n.natAbs y.X.natAbs y.Z.natAbs
      _ = n.natAbs := by
        rw [hycop.gcd_eq_one]
        simp
  have hn_dvd_N : n.natAbs ∣ N := by simpa [hgcd_eq] using hgcd
  have hn_le_N : n.natAbs ≤ N := Nat.le_of_dvd hNpos hn_dvd_N
  have hmax_eq : max A.natAbs B.natAbs = n.natAbs * y.mulHeight := by
    rw [hA, hB, Int.natAbs_mul, Int.natAbs_mul]
    exact max_mul_mul_left n.natAbs y.X.natAbs y.Z.natAbs
  have hmax_eqR : (max A.natAbs B.natAbs : ℝ) =
      (n.natAbs : ℝ) * (y.mulHeight : ℝ) := by
    exact_mod_cast hmax_eq
  have hmax_le : (max A.natAbs B.natAbs : ℝ) ≤
      (N : ℝ) * (y.mulHeight : ℝ) := by
    rw [hmax_eqR]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn_le_N) (by positivity)
  have hmax_pos_nat : 0 < max A.natAbs B.natAbs := by
    rcases hAB with hA0 | hB0
    · exact lt_of_lt_of_le (Int.natAbs_pos.mpr hA0) (le_max_left _ _)
    · exact lt_of_lt_of_le (Int.natAbs_pos.mpr hB0) (le_max_right _ _)
  have hmax_pos : 0 < (max A.natAbs B.natAbs : ℝ) := by
    exact_mod_cast hmax_pos_nat
  have hypos : 0 < (y.mulHeight : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (P1Q.one_le_mulHeight y))
  have hlog_le : Real.log (max A.natAbs B.natAbs : ℝ) ≤
      Real.log ((N : ℝ) * (y.mulHeight : ℝ)) :=
    Real.log_le_log hmax_pos hmax_le
  have hlog_prod : Real.log ((N : ℝ) * (y.mulHeight : ℝ)) =
      Real.log (N : ℝ) + Real.log (y.mulHeight : ℝ) := by
    rw [Real.log_mul]
    · exact_mod_cast ne_of_gt hNpos
    · exact ne_of_gt hypos
  dsimp [P1Q.logHeight]
  linarith

private lemma dupDZ_ne_zero
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    dupDZ E ≠ 0 := by
  intro hD
  have hq : ((dupClearDen E : ℚ) ^ 2) * E.Δ ^ 2 = 0 := by
    have hspec := dupDZ_spec E
    rw [hD] at hspec
    exact hspec.symm
  have hL : (dupClearDen E : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt (dupClearDen_pos E)
  exact (mul_ne_zero (pow_ne_zero 2 hL) (pow_ne_zero 2 E.isUnit_Δ.ne_zero)) hq

private lemma dupFG_not_both_zero
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (x : P1Q) :
    dupFZ E x.X x.Z ≠ 0 ∨ dupGZ E x.X x.Z ≠ 0 := by
  by_contra h
  push Not at h
  have hDX := dup_bezoutX_Z E x.X x.Z
  have hDZ := dup_bezoutZ_Z E x.X x.Z
  rw [h.1, h.2] at hDX hDZ
  have hDne : dupDZ E ≠ 0 := dupDZ_ne_zero E
  have hX0 : x.X = 0 := by
    have hxpow : x.X ^ 7 = 0 := by
      exact (mul_eq_zero.mp (by simpa using hDX)).resolve_left hDne
    exact (pow_eq_zero_iff (by norm_num : (7 : ℕ) ≠ 0)).mp hxpow
  have hZ0 : x.Z = 0 := by
    have hzpow : x.Z ^ 7 = 0 := by
      exact (mul_eq_zero.mp (by simpa using hDZ)).resolve_left hDne
    exact (pow_eq_zero_iff (by norm_num : (7 : ℕ) ≠ 0)).mp hzpow
  rcases x.not_both_zero with hX | hZ
  · exact hX hX0
  · exact hZ hZ0

private lemma sameQ_clear_dup
    (E : WeierstrassCurve ℚ) (x y : P1Q)
    (hSame : P1Q.SameQ y
      (dupNumH E (x.X : ℚ) (x.Z : ℚ))
      (dupDenH E (x.X : ℚ) (x.Z : ℚ))) :
    P1Q.SameQ y (dupFZ E x.X x.Z : ℚ) (dupGZ E x.X x.Z : ℚ) := by
  rw [dupFZ_spec, dupGZ_spec]
  dsimp [P1Q.SameQ] at hSame ⊢
  linear_combination (norm := ring1) (dupClearDen E : ℚ) * hSame

private lemma log_clear_pair_ge_raw
    (E : WeierstrassCurve ℚ) (x : P1Q) :
    Real.log (max (dupFZ E x.X x.Z).natAbs (dupGZ E x.X x.Z).natAbs : ℝ) ≥
      naiveLogHeightP1Q
        (dupNumH E (x.X : ℚ) (x.Z : ℚ))
        (dupDenH E (x.X : ℚ) (x.Z : ℚ)) := by
  let L : ℝ := dupClearDen E
  let F : ℝ := dupNumH E (x.X : ℚ) (x.Z : ℚ)
  let G : ℝ := dupDenH E (x.X : ℚ) (x.Z : ℚ)
  have hLpos_nat : 0 < dupClearDen E := dupClearDen_pos E
  have hLge1 : (1 : ℝ) ≤ L := by
    dsimp [L]
    exact_mod_cast hLpos_nat
  have hFabs :
      ((dupFZ E x.X x.Z).natAbs : ℝ) = L * |F| := by
    rw [show ((dupFZ E x.X x.Z).natAbs : ℝ) =
        |((dupFZ E x.X x.Z : ℤ) : ℝ)| by
          simpa using (Nat.cast_natAbs (α := ℝ) (dupFZ E x.X x.Z))]
    have hspecQ := dupFZ_spec E x.X x.Z
    have hspecR :
        ((dupFZ E x.X x.Z : ℤ) : ℝ) = L * F := by
      dsimp [L, F]
      exact_mod_cast hspecQ
    rw [hspecR]
    rw [abs_mul]
    have hLnonneg : 0 ≤ L := by
      dsimp [L]
      positivity
    rw [abs_of_nonneg hLnonneg]
  have hGabs :
      ((dupGZ E x.X x.Z).natAbs : ℝ) = L * |G| := by
    rw [show ((dupGZ E x.X x.Z).natAbs : ℝ) =
        |((dupGZ E x.X x.Z : ℤ) : ℝ)| by
          simpa using (Nat.cast_natAbs (α := ℝ) (dupGZ E x.X x.Z))]
    have hspecQ := dupGZ_spec E x.X x.Z
    have hspecR :
        ((dupGZ E x.X x.Z : ℤ) : ℝ) = L * G := by
      dsimp [L, G]
      exact_mod_cast hspecQ
    rw [hspecR]
    rw [abs_mul]
    have hLnonneg : 0 ≤ L := by
      dsimp [L]
      positivity
    rw [abs_of_nonneg hLnonneg]
  have hmax :
      (max (dupFZ E x.X x.Z).natAbs (dupGZ E x.X x.Z).natAbs : ℝ) =
        L * max |F| |G| := by
    rw [hFabs, hGabs]
    exact (mul_max_of_nonneg |F| |G| (by positivity)).symm
  by_cases hraw0 : max |F| |G| = 0
  · have hleft :
        (max (dupFZ E x.X x.Z).natAbs (dupGZ E x.X x.Z).natAbs : ℝ) = 0 := by
      rw [hmax, hraw0, mul_zero]
    rw [hleft]
    simp [naiveLogHeightP1Q, F, G, hraw0]
  · have hrawpos : 0 < max |F| |G| := by
      have hnonneg : 0 ≤ max |F| |G| :=
        le_trans (abs_nonneg F) (le_max_left |F| |G|)
      exact lt_of_le_of_ne hnonneg (Ne.symm hraw0)
    have hraw_le_clear : max |F| |G| ≤ L * max |F| |G| :=
      le_mul_of_one_le_left (le_of_lt hrawpos) hLge1
    have hlog := Real.log_le_log hrawpos hraw_le_clear
    rw [hmax]
    simpa [naiveLogHeightP1Q, F, G] using hlog

/--
The true projective height lower bound after cancellation.

This is the audit §3 bridge: start from
`dup_projective_height_lower_height_api_seam`, prove the integer gcd/resultant cancellation
bound including `G = 0`, and convert raw pair height to primitive `P1Q.logHeight`.
-/
theorem dup_projective_height_lower_from_raw_gcd
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x y : P1Q,
        P1Q.SameQ y
          (dupNumH E (x.X : ℚ) (x.Z : ℚ))
          (dupDenH E (x.X : ℚ) (x.Z : ℚ)) →
        P1Q.logHeight y ≥ 4 * P1Q.logHeight x - C := by
  obtain ⟨C0, hraw⟩ := dup_projective_height_lower_height_api_seam E
  let N : ℕ := (dupDZ E).natAbs
  let Cbase : ℝ := C0 + Real.log (N : ℝ)
  refine ⟨max Cbase 0, le_max_right Cbase 0, ?_⟩
  intro x y hSame
  have hxpair : ((x.X : ℚ), (x.Z : ℚ)) ≠ (0, 0) := by
    intro hpair
    have hXq : (x.X : ℚ) = 0 := congrArg Prod.fst hpair
    have hZq : (x.Z : ℚ) = 0 := congrArg Prod.snd hpair
    have hX : x.X = 0 := by exact_mod_cast hXq
    have hZ : x.Z = 0 := by exact_mod_cast hZq
    rcases x.not_both_zero with hXne | hZne
    · exact hXne hX
    · exact hZne hZ
  have hraw_bound :=
    hraw (x.X : ℚ) (x.Z : ℚ) hxpair
  rw [p1q_naiveLogHeight_intCast_eq_logHeight x] at hraw_bound
  have hNpos : 0 < N := by
    dsimp [N]
    exact Int.natAbs_pos.mpr (dupDZ_ne_zero E)
  have hfg_ne : dupFZ E x.X x.Z ≠ 0 ∨ dupGZ E x.X x.Z ≠ 0 :=
    dupFG_not_both_zero E x
  have hgcd :
      Nat.gcd (dupFZ E x.X x.Z).natAbs (dupGZ E x.X x.Z).natAbs ∣ N := by
    dsimp [N]
    exact
      (dupIntegralCertificate E).gcd_dvd_D_natAbs_of_natAbs_coprime
        (X := x.X) (Z := x.Z) (p1q_natAbs_coprime x)
  have hSameZ : P1Q.SameQ y (dupFZ E x.X x.Z : ℚ) (dupGZ E x.X x.Z : ℚ) :=
    sameQ_clear_dup E x y hSame
  have hproj :=
    logHeight_ge_log_int_pair_sub_log_of_gcd_dvd
      y hSameZ hfg_ne hNpos hgcd
  have hclear := log_clear_pair_ge_raw E x
  have hout_raw :
      P1Q.logHeight y ≥
        naiveLogHeightP1Q
          (dupNumH E (x.X : ℚ) (x.Z : ℚ))
          (dupDenH E (x.X : ℚ) (x.Z : ℚ)) - Real.log (N : ℝ) := by
    linarith
  have hbase :
      P1Q.logHeight y ≥ 4 * P1Q.logHeight x - Cbase := by
    dsimp [Cbase]
    linarith
  have hCge : Cbase ≤ max Cbase 0 := le_max_left Cbase 0
  linarith

theorem xHeight_double_lower
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ P : (E⁄ℚ).Point,
        xHeight E (2 • P) ≥ 4 * xHeight E P - C := by
  obtain ⟨C, hC0, hC⟩ := dup_projective_height_lower_from_raw_gcd E
  refine ⟨C, hC0, ?_⟩
  intro P
  exact hC (xRep E P) (xRep E (2 • P)) (xRep_two_nsmul_same_dup E P)

end MazurProof
end
end

-- ===== FLT.Assumptions.MazurProof.X017RankZero =====
section
/-!
# Rank zero for the standard X₀(17) model

The explicit two-isogeny descent gives two representatives modulo doubling.
The rational projective `x`-height has the Northcott property and expands by a
factor four under doubling, up to a uniform constant.  Summing this height over
the four translates by the visible order-four point removes the remaining
translation estimate and proves finite generation.  The exact cardinal bound
modulo doubling then forces the free rank to vanish.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017RankZero

open WeierstrassCurve.Affine
open MazurProof.X017ExactSequence
open MazurProof.X017HeightDescent
open MazurProof.X017Model
open MazurProof.X017SecondCoset
open MazurProof.X017TwoTorsion

noncomputable section

/-- The rational projective `x`-height is nonnegative on every point of the
standard model. -/
theorem xHeight_nonneg (P : Point standard) :
    0 ≤ MazurProof.xHeight standard P :=
  MazurProof.P1Q.logHeight_nonneg (MazurProof.xRep standard P)

/-- The visible point has order dividing four, as required by the
four-translate height symmetrization. -/
theorem four_nsmul_T : 4 • T = 0 := by
  simpa [T_order_four] using addOrderOf_nsmul_eq_zero T

/-- The rational points on the standard `X₀(17)` model form a finitely
generated abelian group.  This is an explicit height-descent proof rather than
an invocation of the general Mordell-Weil theorem. -/
noncomputable instance standardPoint_fg : AddGroup.FG (Point standard) := by
  obtain ⟨C, hC, hdouble⟩ :=
    MazurProof.xHeight_double_lower standard
  exact
    @fg_of_fourOrbitHeight (Point standard) inferInstance
      T (MazurProof.xHeight standard)
      (MazurProof.xHeight_northcott standard) C hC
      four_nsmul_T double_twoCosetExhaustion xHeight_nonneg hdouble

end

end MazurProof.X017RankZero

end

-- ===== FLT.Assumptions.MazurProof.X017FourTorsion =====
section
/-!
# Four-torsion on the standard X₀(17) model

Once a separate arithmetic argument proves that every rational point is
killed by four, the remaining point classification is elementary.  A point
killed by two is either infinity or `(0,0)`.  If instead its double is
`(0,0)`, the duplication formula forces `x² = 289`; the curve equation then
leaves exactly `(17,136)` and `(17,-136)`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017FourTorsion

open WeierstrassCurve.Affine
open MazurProof.VeluTwoIsogeny
open MazurProof.X017Model
open MazurProof.X017TwoTorsion

noncomputable section

/-- On a standard two-isogeny curve, the horizontal coordinate of a doubled
affine point is `(x²-b)²/(4y²)`. -/
private theorem tangent_x_eq_square_div
    {a b x y : ℚ} (hy : y ≠ 0)
    (hcurve : y ^ 2 = x * (x ^ 2 + a * x + b)) :
    StandardTwoIsogeny.tx a x
        (StandardTwoIsogeny.tangent a b x y) =
      (x ^ 2 - b) ^ 2 / (4 * y ^ 2) := by
  unfold StandardTwoIsogeny.tx StandardTwoIsogeny.tangent
  field_simp [hy]
  rw [hcurve]
  ring

/-- A rational point whose double is the visible kernel point has horizontal
coordinate `17`. -/
theorem x_eq_seventeen_of_two_nsmul_eq_K
    {x y : ℚ} (h : Nonsingular standard x y)
    (hdouble :
      2 • (Point.some x y h : Point standard) = K) :
    x = 17 := by
  have hy : y ≠ 0 := by
    intro hy
    have hzero :
        2 • (Point.some x y h : Point standard) = 0 :=
      StandardTwoIsogeny.double_eq_zero_of_y_zero h hy
    apply K_ne_zero
    calc
      K = 2 • (Point.some x y h : Point standard) := hdouble.symm
      _ = 0 := hzero
  have hx : x ≠ 0 := by
    intro hx
    have hy0 := StandardTwoIsogeny.y_zero_of_x_zero h hx
    exact hy hy0
  have hcurve :
      y ^ 2 = x * (x ^ 2 + a17 * x + b17) :=
    StandardTwoIsogeny.curve_equation.mp h.left
  have hfx : StandardTwoIsogeny.fx x y ≠ 0 := by
    unfold StandardTwoIsogeny.fx
    exact div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx)
  have hcomp :=
    StandardTwoIsogeny.dual_comp_pointMap
      (Point.some x y h : Point standard)
  rw [hdouble, StandardTwoIsogeny.pointMap_some h hx,
    StandardTwoIsogeny.dualPoint_some _ hfx] at hcomp
  have hxcoord :
      StandardTwoIsogeny.dx
          (StandardTwoIsogeny.fx x y)
          (StandardTwoIsogeny.fy b17 x y) = 0 := by
    unfold K StandardTwoIsogeny.kernelPoint at hcomp
    rw [Point.some.injEq] at hcomp
    exact hcomp.1
  rw [StandardTwoIsogeny.dual_forward_x hx hy hcurve] at hxcoord
  rw [tangent_x_eq_square_div hy hcurve] at hxcoord
  have hsq : (x ^ 2 - b17) ^ 2 = 0 := by
    field_simp [hy] at hxcoord
    simpa using hxcoord
  have hxb : x ^ 2 = b17 := by
    nlinarith [sq_nonneg (x ^ 2 - b17)]
  have hxcases : x = 17 ∨ x = -17 := by
    apply eq_or_eq_neg_of_sq_eq_sq x 17
    norm_num [b17, veluT] at hxb ⊢
    exact hxb
  rcases hxcases with hx | hx
  · exact hx
  · exfalso
    rw [hx] at hcurve
    norm_num [a17, b17, veluT] at hcurve
    nlinarith [sq_nonneg y]

/-- The two rational halves of `(0,0)` are precisely `T` and `-T`. -/
theorem eq_T_or_neg_T_of_two_nsmul_eq_K
    (P : Point standard) (hdouble : 2 • P = K) :
    P = T ∨ P = -T := by
  cases P with
  | zero =>
      exfalso
      simpa using K_ne_zero hdouble.symm
  | some x y h =>
      have hx : x = 17 :=
        x_eq_seventeen_of_two_nsmul_eq_K h hdouble
      have hcurve :
          y ^ 2 = x * (x ^ 2 + a17 * x + b17) :=
        StandardTwoIsogeny.curve_equation.mp h.left
      rw [hx] at hcurve
      have hycases : y = 136 ∨ y = -136 := by
        apply eq_or_eq_neg_of_sq_eq_sq y 136
        norm_num [a17, b17, veluT] at hcurve ⊢
        exact hcurve
      rcases hycases with hy | hy
      · left
        unfold T
        rw [Point.some.injEq]
        exact ⟨hx, hy⟩
      · right
        unfold T
        rw [Point.neg_some, Point.some.injEq]
        exact ⟨hx, by
          rw [StandardTwoIsogeny.curve_negY]
          exact hy⟩

/-- Every rational point killed by four is one of the four visible points. -/
theorem eq_zero_or_K_or_T_or_neg_T_of_four_nsmul_eq_zero
    (P : Point standard) (hfour : 4 • P = 0) :
    P = 0 ∨ P = K ∨ P = T ∨ P = -T := by
  have htwo : 2 • (2 • P) = 0 := by
    simpa [← mul_nsmul] using hfour
  let Q : MazurProof.RationalPointsN15ExactSequence.TwoTorsion
      (Point standard) :=
    ⟨2 • P, htwo⟩
  rcases twoTorsion_value_eq_zero_or_K Q with hQ | hQ
  · have hPtwo : 2 • P = 0 := hQ
    let R : MazurProof.RationalPointsN15ExactSequence.TwoTorsion
        (Point standard) :=
      ⟨P, hPtwo⟩
    rcases twoTorsion_value_eq_zero_or_K R with hP | hP
    · exact Or.inl hP
    · exact Or.inr (Or.inl hP)
  · rcases eq_T_or_neg_T_of_two_nsmul_eq_K P hQ with hP | hP
    · exact Or.inr (Or.inr (Or.inl hP))
    · exact Or.inr (Or.inr (Or.inr hP))

end

end MazurProof.X017FourTorsion

end

-- ===== FLT.Assumptions.MazurProof.X017RationalPoints =====
section
/-!
# Rational points on the standard X₀(17) model

The exact `{0,T}` cover modulo doubling makes `4P` divisible by every power
of two.  On the integral good model, four times every rational point is
formal, and the formal filtration is separated.  Transporting these two facts
through the explicit model equivalence proves `4P=0` for every rational point.
The four-torsion calculation then gives exactly the visible points
`0`, `K`, `T`, and `-T`.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof.X017RationalPoints

open WeierstrassCurve.Affine
open MazurProof.X017FormalTwoCore
open MazurProof.X017FormalTwoReduction
open MazurProof.X017FourTorsion
open MazurProof.X017Model
open MazurProof.X017RankZero
open MazurProof.X017SecondCoset

noncomputable section

/-- Iterating the two-coset cover makes four times any standard-model point
divisible by every power of two.  The representative term disappears because
`T` has order four. -/
theorem four_nsmul_two_power_divisible
    (P : Point standard) (n : ℕ) :
    ∃ Q : Point standard,
      4 • P = (2 ^ n : ℕ) • (4 • Q) := by
  induction n with
  | zero =>
      exact ⟨P, by simp⟩
  | succ n ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨R, hQR | hQR⟩ := double_twoCosetExhaustion Q
      · refine ⟨R, ?_⟩
        change Q = 2 • R at hQR
        rw [hQ, hQR]
        rw [pow_succ]
        simp only [← mul_nsmul]
        congr 1
        ring
      · refine ⟨R, ?_⟩
        change Q = T + 2 • R at hQR
        rw [hQ, hQR, nsmul_add, four_nsmul_T, zero_add]
        rw [pow_succ]
        simp only [← mul_nsmul]
        congr 1
        ring

/-- Every rational point on the standard model is killed by four.  This is
the completed good-reduction/formal-kernel arithmetic input. -/
theorem four_nsmul_eq_zero (P : Point standard) :
    4 • P = 0 := by
  let P0 : Point X017 := X017ToStandard.symm P
  have hP0formal : FormalAtTwo (4 • P0) :=
    four_nsmul_formal P0
  have hdiv : ∀ n : ℕ, ∃ Q0 : Point X017,
      FormalAtTwo Q0 ∧ 4 • P0 = (2 ^ n : ℕ) • Q0 := by
    intro n
    obtain ⟨Q, hQ⟩ := four_nsmul_two_power_divisible P n
    refine ⟨4 • X017ToStandard.symm Q,
      four_nsmul_formal (X017ToStandard.symm Q), ?_⟩
    have hm := congrArg X017ToStandard.symm hQ
    simpa only [map_nsmul, AddEquiv.symm_apply_apply, P0] using hm
  have hzero : 4 • P0 = 0 :=
    formal_separated (4 • P0) hP0formal hdiv
  have hm := congrArg X017ToStandard hzero
  simpa only [map_nsmul, AddEquiv.apply_symm_apply, map_zero, P0] using hm

/-- The complete rational-point classification on the standard model. -/
theorem eq_zero_or_K_or_T_or_neg_T (P : Point standard) :
    P = 0 ∨ P = K ∨ P = T ∨ P = -T :=
  eq_zero_or_K_or_T_or_neg_T_of_four_nsmul_eq_zero
    P (four_nsmul_eq_zero P)

end

end MazurProof.X017RationalPoints

end


theorem solution (X Y : ℚ)
    (h : Y ^ 2 = X ^ 3 + 30 * X ^ 2 + 289 * X) : X = 0 ∨ X = 17 := by
  have hns : MazurProof.X017Model.standard.toAffine.Nonsingular X Y :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp only [MazurProof.X017Model.a17, MazurProof.X017Model.b17,
        MazurProof.VeluTwoIsogeny.veluT]
      linear_combination h)
  rcases MazurProof.X017RationalPoints.eq_zero_or_K_or_T_or_neg_T
      (WeierstrassCurve.Affine.Point.some X Y hns) with hP | hP | hP | hP
  · exact absurd hP (WeierstrassCurve.Affine.Point.some_ne_zero _)
  · left
    simp only [MazurProof.X017Model.K, MazurProof.VeluTwoIsogeny.StandardTwoIsogeny.kernelPoint,
      WeierstrassCurve.Affine.Point.some.injEq] at hP
    exact hP.1
  · right
    simp only [MazurProof.X017Model.T, WeierstrassCurve.Affine.Point.some.injEq] at hP
    exact hP.1
  · right
    simp only [MazurProof.X017Model.T, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq] at hP
    exact hP.1
