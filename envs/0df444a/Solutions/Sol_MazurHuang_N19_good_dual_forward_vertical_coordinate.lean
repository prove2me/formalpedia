-- Prove2me | solution 1 for MazurHuang.N19.good_dual_forward_vertical_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:22:53.168171+00:00
-- url     : https://prove2.me/submissions/d742b36b-654b-4915-8bdf-6ef1e5cdb995

/-
The vertical isogeny composition equals the tangent-chord tripling formula
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib


-- Source FLT/Assumptions/MazurProof/XDelta19GoodModel.lean:30-61; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodModel
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
/-- The integral model in the middle of the conductor-nineteen
three-isogeny chain. -/
def goodCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 64
  a₃ := 0
  a₄ := 1216
  a₆ := 5776

/-- The affine equation of the good integral model. -/
def OnGood (x y : ℚ) : Prop :=
  y ^ 2 = x ^ 3 + (8 * x + 76) ^ 2

/-- The good model has discriminant `-2^12 * 19^3`, hence in particular
good reduction at three. -/
theorem goodCurve_delta : goodCurve.Δ = (-28094464 : ℚ) := by
  norm_num [goodCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The good integral model is nonsingular. -/
instance goodCurve_isElliptic : goodCurve.IsElliptic where
  isUnit := by
    rw [goodCurve_delta]
    norm_num

/-- The bundled affine equation is the displayed good equation. -/
@[simp] theorem goodCurve_equation_iff (x y : ℚ) :
    Equation goodCurve x y ↔ OnGood x y := by
  rw [equation_iff]
  simp [goodCurve, OnGood]
  ring_nf

end
end MazurProof.XDelta19GoodModel
end

namespace MazurProof.XDelta19GoodModel
abbrev GoodPoint := WeierstrassCurve.Affine.Point goodCurve
end MazurProof.XDelta19GoodModel

-- Source FLT/Assumptions/MazurProof/XDelta19GoodModel.lean:153-170; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodModel
open WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
/-- Nonsingularity of the positive visible flex. -/
theorem goodT_nonsingular : Nonsingular goodCurve (0 : ℚ) 76 :=
  equation_iff_nonsingular.mp <|
    (goodCurve_equation_iff 0 76).mpr (by norm_num [OnGood])

/-- Nonsingularity of the negative visible flex. -/
theorem goodTNeg_nonsingular : Nonsingular goodCurve (0 : ℚ) (-76) :=
  equation_iff_nonsingular.mp <|
    (goodCurve_equation_iff 0 (-76)).mpr (by norm_num [OnGood])

/-- The positive rational flex on the good model. -/
def goodT : GoodPoint :=
  Point.some 0 76 goodT_nonsingular

/-- The negative rational flex on the good model. -/
def goodTNeg : GoodPoint :=
  Point.some 0 (-76) goodTNeg_nonsingular

end
end MazurProof.XDelta19GoodModel
end

-- Source FLT/Assumptions/MazurProof/XDelta19GoodIsogeny.lean:31-170; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodIsogeny
open WeierstrassCurve WeierstrassCurve.Affine Polynomial MazurProof.XDelta19GoodModel
noncomputable section
/-- The scaled Vélu quotient of the good integral model. -/
def quotientCurve : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -1728
  a₃ := 0
  a₄ := -1728
  a₆ := -432

/-- The affine equation of the small Vélu quotient. -/
def OnQuotient (s t : ℚ) : Prop :=
  t ^ 2 = s ^ 3 - 3 * (24 * s + 12) ^ 2

/-- The quotient model has nonzero discriminant. -/
theorem quotientCurve_delta :
    quotientCurve.Δ = (-41358864384 : ℚ) := by
  norm_num [quotientCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The quotient model is nonsingular. -/
instance quotientCurve_isElliptic : quotientCurve.IsElliptic where
  isUnit := by
    rw [quotientCurve_delta]
    norm_num

/-- The bundled affine equation is the displayed quotient equation. -/
@[simp] theorem quotientCurve_equation_iff (s t : ℚ) :
    Equation quotientCurve s t ↔ OnQuotient s t := by
  rw [equation_iff]
  simp [quotientCurve, OnQuotient]
  ring_nf

/-! ## Explicit isogeny formulas -/

/-- Horizontal coordinate of the forward degree-three isogeny. -/
def threeIsogenyX (x : ℚ) : ℚ :=
  (9 * x ^ 3 + 768 * x ^ 2 + 21888 * x + 207936) / x ^ 2

/-- Vertical coordinate of the forward degree-three isogeny. -/
def threeIsogenyY (x y : ℚ) : ℚ :=
  (27 * x ^ 3 * y - 65664 * x * y - 1247616 * y) / x ^ 3

/-- The forward formulas carry the good model to its small quotient. -/
theorem threeIsogeny_on_curve {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    OnQuotient (threeIsogenyX x) (threeIsogenyY x y) := by
  unfold OnGood at h
  unfold OnQuotient threeIsogenyX threeIsogenyY
  field_simp [hx]
  simp_rw [h]
  ring

/-- Horizontal coordinate of the dual degree-three isogeny. -/
def dualThreeIsogenyX (s : ℚ) : ℚ :=
  (s ^ 3 - 2304 * s ^ 2 - 3456 * s - 1728) / (81 * s ^ 2)

/-- Vertical coordinate of the dual degree-three isogeny. -/
def dualThreeIsogenyY (s t : ℚ) : ℚ :=
  (s ^ 3 * t + 3456 * s * t + 3456 * t) / (729 * s ^ 3)

/-- The dual formulas carry the small quotient back to the good model. -/
theorem dualThreeIsogeny_on_curve {s t : ℚ} (hs : s ≠ 0)
    (h : OnQuotient s t) :
    OnGood (dualThreeIsogenyX s) (dualThreeIsogenyY s t) := by
  unfold OnQuotient at h
  unfold OnGood dualThreeIsogenyX dualThreeIsogenyY
  field_simp [hs]
  simp_rw [h]
  ring

/-! ## Bundled point maps -/

/-- Rational points on the small quotient. -/
abbrev QuotientPoint := Point quotientCurve

/-- A rational affine point on the quotient cannot have first coordinate
zero. -/
theorem quotient_x_ne_zero_of_on_curve {s t : ℚ}
    (h : OnQuotient s t) :
    s ≠ 0 := by
  intro hs
  rw [hs] at h
  norm_num [OnQuotient] at h
  nlinarith [sq_nonneg t]

/-- Away from the visible kernel, the horizontal coordinate of the
forward isogeny is nonzero. -/
theorem threeIsogenyX_ne_zero {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    threeIsogenyX x ≠ 0 :=
  quotient_x_ne_zero_of_on_curve (threeIsogeny_on_curve hx h)

/-- The bundled forward degree-three isogeny. -/
noncomputable def threeIsogenyPoint : GoodPoint → QuotientPoint
  | .zero => .zero
  | .some _x _y h =>
      if hx : _x = 0 then .zero
      else Point.mk
        (quotientCurve_equation_iff _ _ |>.2 <|
          threeIsogeny_on_curve hx
            (goodCurve_equation_iff _ _ |>.1 h.1))

/-- The bundled dual degree-three isogeny. -/
noncomputable def dualThreeIsogenyPoint : QuotientPoint → GoodPoint
  | .zero => .zero
  | .some _s _t h =>
      if hs : _s = 0 then .zero
      else Point.mk
        (goodCurve_equation_iff _ _ |>.2 <|
          dualThreeIsogeny_on_curve hs
            (quotientCurve_equation_iff _ _ |>.1 h.1))

/-- The forward isogeny fixes the point at infinity. -/
@[simp] theorem threeIsogenyPoint_zero :
    threeIsogenyPoint 0 = 0 := rfl

/-- The dual isogeny fixes the point at infinity. -/
@[simp] theorem dualThreeIsogenyPoint_zero :
    dualThreeIsogenyPoint 0 = 0 := rfl

/-- Away from its kernel, the bundled forward map is given by the
displayed affine formulas. -/
theorem threeIsogenyPoint_some_of_x_ne_zero {x y : ℚ}
    (h : Nonsingular goodCurve x y) (hx : x ≠ 0) :
    threeIsogenyPoint (.some x y h) =
      Point.mk
        (quotientCurve_equation_iff _ _ |>.2 <|
          threeIsogeny_on_curve hx
            (goodCurve_equation_iff _ _ |>.1 h.1)) := by
  simp [threeIsogenyPoint, hx]

/-- The bundled dual map is given by the displayed affine formulas on
every affine rational point of the quotient. -/
theorem dualThreeIsogenyPoint_some_of_x_ne_zero {s t : ℚ}
    (h : Nonsingular quotientCurve s t) (hs : s ≠ 0) :
    dualThreeIsogenyPoint (.some s t h) =
      Point.mk
        (goodCurve_equation_iff _ _ |>.2 <|
          dualThreeIsogeny_on_curve hs
            (quotientCurve_equation_iff _ _ |>.1 h.1)) := by
  simp [dualThreeIsogenyPoint, hs]
end
end MazurProof.XDelta19GoodIsogeny
end

-- Source FLT/Assumptions/MazurProof/XDelta19GoodIsogeny.lean:209-277; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodIsogeny
open WeierstrassCurve WeierstrassCurve.Affine Polynomial MazurProof.XDelta19GoodModel
noncomputable section
/-- Negation on the good model changes only the sign of the vertical
coordinate. -/
@[simp] theorem goodCurve_negY (x y : ℚ) :
    negY goodCurve x y = -y := by
  simp [negY, goodCurve]

/-- The good Weierstrass cubic has no rational root. -/
private theorem goodCubic_ne_zero (x : ℚ) :
    x ^ 3 + 64 * x ^ 2 + 1216 * x + 5776 ≠ 0 := by
  intro h
  let p : ℤ[X] := X ^ 3 + C 64 * X ^ 2 + C 1216 * X + C 5776
  have hpmonic : p.Monic := by
    dsimp [p]
    monicity!
  have hroot : aeval x p = 0 := by
    simp [p, aeval_def]
    norm_cast
  obtain ⟨z, hx, _hzdiv⟩ :=
    exists_integer_of_is_root_of_monic (A := ℤ) (K := ℚ) hpmonic hroot
  rw [hx] at h
  have hz : z ^ 3 + 64 * z ^ 2 + 1216 * z + 5776 = 0 := by
    have hzcast :
        ((z ^ 3 + 64 * z ^ 2 + 1216 * z + 5776 : ℤ) : ℚ) = 0 := by
      push_cast
      exact h
    exact_mod_cast hzcast
  have hzmod : (z : ZMod 5) ^ 3 + 64 * (z : ZMod 5) ^ 2 +
      1216 * (z : ZMod 5) + 5776 = 0 := by
    have hz' := congrArg (fun n : ℤ => (n : ZMod 5)) hz
    push_cast at hz'
    exact hz'
  exact (by decide : ∀ u : ZMod 5,
    u ^ 3 + 64 * u ^ 2 + 1216 * u + 5776 ≠ 0) (z : ZMod 5) hzmod

/-- An affine rational point on the good model never has zero vertical
coordinate. -/
theorem good_y_ne_zero {x y : ℚ} (h : OnGood x y) :
    y ≠ 0 := by
  intro hy
  apply goodCubic_ne_zero x
  unfold OnGood at h
  rw [hy] at h
  norm_num at h
  linear_combination -h

/-- The tangent slope at an affine point of the good model. -/
private def goodTangent (x y : ℚ) : ℚ :=
  (3 * x ^ 2 + 128 * x + 1216) / (2 * y)

/-- Horizontal coordinate of twice an affine point. -/
private def goodDoubleX (x y : ℚ) : ℚ :=
  goodTangent x y ^ 2 - 64 - 2 * x

/-- Vertical coordinate of twice an affine point. -/
private def goodDoubleY (x y : ℚ) : ℚ :=
  -(goodTangent x y * (goodDoubleX x y - x) + y)

/-- Slope of the line from twice a point to the original point. -/
private def goodTripleSlope (x y : ℚ) : ℚ :=
  (goodDoubleY x y - y) / (goodDoubleX x y - x)

/-- Horizontal coordinate of three times an affine point. -/
private def goodTripleX (x y : ℚ) : ℚ :=
  goodTripleSlope x y ^ 2 - 64 - goodDoubleX x y - x

/-- Vertical coordinate of three times an affine point. -/
private def goodTripleY (x y : ℚ) : ℚ :=
  -(goodTripleSlope x y * (goodTripleX x y - goodDoubleX x y) +
      goodDoubleY x y)
end
end MazurProof.XDelta19GoodIsogeny
end

-- Source FLT/Assumptions/MazurProof/XDelta19GoodIsogeny.lean:331-362; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodIsogeny
open WeierstrassCurve WeierstrassCurve.Affine Polynomial MazurProof.XDelta19GoodModel
noncomputable section
/-- The denominator separating a point from its double is the numerator
of the forward isogeny's horizontal coordinate. -/
private theorem goodDoubleX_sub_identity {x y : ℚ} (hy : y ≠ 0)
    (h : OnGood x y) :
    4 * y ^ 2 * (goodDoubleX x y - x) =
      -x * (3 * x ^ 3 + 256 * x ^ 2 + 7296 * x + 69312) := by
  unfold goodDoubleX goodTangent
  unfold OnGood at h
  field_simp [hy]
  rw [h]
  ring

/-- Away from the visible three-torsion kernel, a point is distinct from
its double. -/
private theorem goodDoubleX_ne_self {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    goodDoubleX x y ≠ x := by
  have hy := good_y_ne_zero h
  have hid := goodDoubleX_sub_identity hy h
  have hphi := threeIsogenyX_ne_zero hx h
  have hnum :
      3 * x ^ 3 + 256 * x ^ 2 + 7296 * x + 69312 ≠ 0 := by
    intro hnum
    apply hphi
    unfold threeIsogenyX
    rw [show 9 * x ^ 3 + 768 * x ^ 2 + 21888 * x + 207936 =
      3 * (3 * x ^ 3 + 256 * x ^ 2 + 7296 * x + 69312) by ring]
    rw [hnum]
    simp
  intro heq
  rw [heq, sub_self, mul_zero] at hid
  exact (mul_ne_zero (neg_ne_zero.mpr hx) hnum) hid.symm
end
end MazurProof.XDelta19GoodIsogeny
end

-- Source FLT/Assumptions/MazurProof/XDelta19GoodIsogeny.lean:393-429; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodIsogeny
open WeierstrassCurve WeierstrassCurve.Affine Polynomial MazurProof.XDelta19GoodModel
noncomputable section
/-- The vertical coordinate of the dual-forward composition agrees with
chord-and-tangent tripling. -/
private theorem dual_three_comp_y {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y) =
      goodTripleY x y := by
  have hy := good_y_ne_zero h
  have hxx := goodDoubleX_ne_self hx h
  have hphi := threeIsogenyX_ne_zero hx h
  unfold dualThreeIsogenyY goodTripleY goodTripleX goodTripleSlope
  field_simp [hphi, hxx]
  unfold threeIsogenyX threeIsogenyY goodDoubleY goodDoubleX goodTangent
  unfold OnGood at h
  field_simp [hx, hy]
  have hy4 : y ^ 4 = (x ^ 3 + (8 * x + 76) ^ 2) ^ 2 := by
    calc
      y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = _ := by rw [h]
  have hy6 : y ^ 6 = (x ^ 3 + (8 * x + 76) ^ 2) ^ 3 := by
    calc
      y ^ 6 = (y ^ 2) ^ 3 := by ring
      _ = _ := by rw [h]
  have hy8 : y ^ 8 = (x ^ 3 + (8 * x + 76) ^ 2) ^ 4 := by
    calc
      y ^ 8 = (y ^ 2) ^ 4 := by ring
      _ = _ := by rw [h]
  have hy10 : y ^ 10 = (x ^ 3 + (8 * x + 76) ^ 2) ^ 5 := by
    calc
      y ^ 10 = (y ^ 2) ^ 5 := by ring
      _ = _ := by rw [h]
  have hy12 : y ^ 12 = (x ^ 3 + (8 * x + 76) ^ 2) ^ 6 := by
    calc
      y ^ 12 = (y ^ 2) ^ 6 := by ring
      _ = _ := by rw [h]
  ring_nf
  rw [hy4, hy6, hy8, hy10, hy12]
  ring
end
end MazurProof.XDelta19GoodIsogeny
end

theorem solution {x y : ℚ} (hx : x ≠ 0)
    (h : y ^ 2 = x ^ 3 + (8 * x + 76) ^ 2) :
    let tangent := (3 * x ^ 2 + 128 * x + 1216) / (2 * y)
    let doubleX := tangent ^ 2 - 64 - 2 * x
    let doubleY := -(tangent * (doubleX - x) + y)
    let tripleSlope := (doubleY - y) / (doubleX - x)
    let tripleX := tripleSlope ^ 2 - 64 - doubleX - x
    let s := (9 * x ^ 3 + 768 * x ^ 2 + 21888 * x + 207936) / x ^ 2
    let t := (27 * x ^ 3 * y - 65664 * x * y - 1247616 * y) / x ^ 3
    (s ^ 3 * t + 3456 * s * t + 3456 * t) / (729 * s ^ 3) =
      -(tripleSlope * (tripleX - doubleX) + doubleY) := by
  exact MazurProof.XDelta19GoodIsogeny.dual_three_comp_y hx h
