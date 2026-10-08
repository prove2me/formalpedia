-- Prove2me | solution 1 for MazurHuang.eq_zero_of_X0_thirtyFive_equation
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T21:25:56.653099+00:00
-- url     : https://prove2.me/submissions/bf8314f9-faf8-43ad-870d-9858e6234768

/-
Rational points of Kubert's hyperelliptic model of X_0(35): x = 0.

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * FLT/Assumptions/MazurProof/RationalPointsX135.lean (the hyperelliptic model, the quotient map to 35a1, map_to_E35, quotientW_ne_one; the
    rational points of 35a1 are taken from the published theorem)
  * the published statement
-/
import Mathlib
import Theorems.Thm_MazurHuang_eq_one_of_curve_35a1_equation

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/RationalPointsX135.lean. -/
section

open scoped WeierstrassCurve.Affine

namespace MazurProof.RationalPointsX135

noncomputable section

open Polynomial

-- FLT/Assumptions/MazurProof/RationalPointsX135.lean, lines 34-119
/-- Kubert's hyperelliptic polynomial for `X₀(35)`. -/
def hyperellipticF35 (x : ℚ) : ℚ :=
  x ^ 8 - 4 * x ^ 7 - 6 * x ^ 6 - 4 * x ^ 5 - 9 * x ^ 4 +
    4 * x ^ 3 - 6 * x ^ 2 + 4 * x + 1

def OnX035 (x y : ℚ) : Prop := y ^ 2 = hyperellipticF35 x

/-! ## The degree-two quotient to `35A1` -/

def quotientU (x : ℚ) : ℚ := x - 1 / x

def quotientV (x y : ℚ) : ℚ := y * (1 + 1 / x ^ 4)

def quotientW (x : ℚ) : ℚ :=
  (x ^ 2 - 6 * x - 1) / (x ^ 2 + x - 1)

def quotientZ (x y : ℚ) : ℚ :=
  7 * y / (2 * (x ^ 2 + x - 1) ^ 2) - 1 / 2

/-- The optimal conductor-35 quotient, Cremona label `35a1`. -/
def E35Curve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 1
  a₃ := 1
  a₄ := 9
  a₆ := 1

def OnE35 (w z : ℚ) : Prop :=
  z ^ 2 + z = w ^ 3 + w ^ 2 + 9 * w + 1

theorem E35Curve_delta : E35Curve.Δ = (-42875 : ℚ) := by
  norm_num [E35Curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance E35Curve_isElliptic : E35Curve.IsElliptic where
  isUnit := by rw [E35Curve_delta]; norm_num

@[simp] theorem E35Curve_equation_iff (w z : ℚ) :
    WeierstrassCurve.Affine.Equation E35Curve w z ↔ OnE35 w z := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [E35Curve, OnE35]

private theorem quotientU_add_one_ne_zero {x : ℚ} (hx : x ≠ 0) :
    quotientU x + 1 ≠ 0 := by
  intro h
  have hquad : x ^ 2 + x - 1 = 0 := by
    unfold quotientU at h
    field_simp [hx] at h
    linarith
  have hsquare : (2 * x + 1) ^ 2 = 5 := by nlinarith
  have hnot : ¬ IsSquare (5 : ℚ) := by norm_num
  exact hnot ⟨2 * x + 1, by simpa [pow_two] using hsquare.symm⟩

private theorem quotientU_sq_add_two_ne_zero (x : ℚ) :
    quotientU x ^ 2 + 2 ≠ 0 := by
  nlinarith [sq_nonneg (quotientU x)]

private theorem quotientDenominator_ne_zero {x : ℚ} (hx : x ≠ 0) :
    x ^ 2 + x - 1 ≠ 0 := by
  intro h
  apply quotientU_add_one_ne_zero hx
  unfold quotientU
  field_simp [hx]
  linarith

/-- The literal rational-function identity for
`X₀(35) → X₀(35)/w₅ = 35a1`. -/
theorem map_to_E35 {x y : ℚ} (hx : x ≠ 0) (hxy : OnX035 x y) :
    OnE35 (quotientW x) (quotientZ x y) := by
  have hd := quotientDenominator_ne_zero hx
  unfold OnX035 hyperellipticF35 at hxy
  unfold OnE35 quotientW quotientZ
  set d : ℚ := x ^ 2 + x - 1 with hd_def
  have hd' : d ≠ 0 := by simpa [d] using hd
  field_simp [hd']
  ring_nf
  rw [hxy]
  ring

theorem quotientW_ne_one {x : ℚ} (hx : x ≠ 0) : quotientW x ≠ 1 := by
  have hd := quotientDenominator_ne_zero hx
  intro h
  unfold quotientW at h
  have h' := (div_eq_iff hd).mp h
  have : x = 0 := by linarith
  exact hx this

/-- The only affine rational points on the conductor-35 quotient have first coordinate one
(statement as in `FLT/Assumptions/MazurProof/RationalPointsX135Formal.lean`), here the published
theorem `MazurHuang.eq_one_of_curve_35a1_equation`. -/
theorem E35_affine_w_eq_one {w z : ℚ} (hE : OnE35 w z) : w = 1 :=
  MazurHuang.eq_one_of_curve_35a1_equation hE


end

end MazurProof.RationalPointsX135

end

theorem solution
    {x y : ℚ}
    (h : y ^ 2 = x ^ 8 - 4 * x ^ 7 - 6 * x ^ 6 - 4 * x ^ 5 - 9 * x ^ 4 + 4 * x ^ 3 - 6 * x ^ 2 + 4 * x + 1) :
    x = 0 := by
  by_contra hx
  exact MazurProof.RationalPointsX135.quotientW_ne_one hx
    (MazurProof.RationalPointsX135.E35_affine_w_eq_one
      (MazurProof.RationalPointsX135.map_to_E35 hx h))
