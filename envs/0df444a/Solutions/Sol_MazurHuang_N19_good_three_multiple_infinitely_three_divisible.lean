-- Prove2me | solution 1 for MazurHuang.N19.good_three_multiple_infinitely_three_divisible
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:27:50.014306+00:00
-- url     : https://prove2.me/submissions/aab0f994-51d3-4191-b65f-4862e77cb0b7

/-
Every triple is divisible by every power of three
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_MazurHuang_N19_good_flex_cubeclasses
import Theorems.Thm_MazurHuang_N19_quotient_affine_isogeny_preimage
import Theorems.Thm_MazurHuang_N19_good_affine_tripling_coordinates


namespace MazurProof.TateOriginDivision
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
/-- Evaluate the coordinate-ring square identity to connect the published
integer-scalar division-polynomial criterion to the natural-scalar square criterion. -/
theorem nsmul_eq_zero_iff_PsiSq_eval
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {n : ℕ} {x y : ℚ} (h : W.toAffine.Nonsingular x y) :
    n • (Point.some x y h : W.toAffine.Point) = 0 ↔
      (W.ΨSq (n : ℤ)).eval x = 0 := by
  have hsq : (W.ψ (n : ℤ)).evalEval x y ^ 2 = (W.ΨSq (n : ℤ)).eval x := by
    have hmk : Affine.CoordinateRing.mk W (W.ψ (n : ℤ) * W.ψ (n : ℤ)) =
        Affine.CoordinateRing.mk W (C (W.ΨSq (n : ℤ))) := by
      rw [map_mul, Affine.CoordinateRing.mk_ψ, ← sq, Affine.CoordinateRing.mk_Ψ_sq]
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp hmk
    have h0 : W.toAffine.polynomial.evalEval x y = 0 := h.1
    have h1 := congrArg (evalEval x y) hp
    rw [evalEval_sub, evalEval_mul, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_C] at h1
    rw [sq]
    exact h1
  constructor
  · intro hp
    have hp' : (n : ℤ) • (Point.some x y h : W.toAffine.Point) = 0 := by
      simpa only [natCast_zsmul] using hp
    have hz := (Point.smul_some_eq_zero_iff W h (n : ℤ)).mp hp'
    rw [← hsq, hz, zero_pow two_ne_zero]
  · intro hz
    have hzψ : (W.ψ (n : ℤ)).evalEval x y = 0 :=
      (sq_eq_zero_iff).mp (hsq.trans hz)
    have hp := (Point.smul_some_eq_zero_iff W h (n : ℤ)).mpr hzψ
    simpa only [natCast_zsmul] using hp
end MazurProof.TateOriginDivision

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

-- Source FLT/Assumptions/MazurProof/XDelta19GoodIsogeny.lean:31-252; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
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

/-! ## The visible three-torsion kernel -/

/-- Every affine good-model point with first coordinate zero is killed
by three. -/
theorem three_nsmul_of_x_zero {x y : ℚ}
    (h : Nonsingular goodCurve x y) (hx : x = 0) :
    3 • (Point.some x y h : GoodPoint) = 0 := by
  apply (TateOriginDivision.nsmul_eq_zero_iff_PsiSq_eval
    goodCurve h).mpr
  rw [goodCurve.ΨSq_ofNat 3]
  simp [show ¬ Even (3 : ℕ) by decide,
    WeierstrassCurve.preΨ'_three, WeierstrassCurve.Ψ₃,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, goodCurve, hx]
  norm_num

/-- The positive visible flex has order dividing three. -/
@[simp] theorem goodT_three_nsmul :
    3 • goodT = 0 :=
  three_nsmul_of_x_zero goodT_nonsingular rfl

/-- The negative visible flex has order dividing three. -/
@[simp] theorem goodTNeg_three_nsmul :
    3 • goodTNeg = 0 :=
  three_nsmul_of_x_zero goodTNeg_nonsingular rfl

/-- The negative visible flex is the group inverse of the positive
visible flex. -/
@[simp] theorem goodTNeg_eq_neg :
    goodTNeg = -goodT := by
  rw [goodTNeg, goodT, Point.neg_some, Point.some.injEq]
  constructor
  · rfl
  · simp [negY, goodCurve]

/-! ## Verification of the dual-forward composition -/

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
end
end MazurProof.XDelta19GoodIsogeny
end

namespace MazurProof.XDelta19GoodIsogeny
open WeierstrassCurve.Affine MazurProof.XDelta19GoodModel
/-- Recover the point-map composition from the published affine coordinate formula. -/
theorem dual_comp_threeIsogenyPoint (P : GoodPoint) :
    dualThreeIsogenyPoint (threeIsogenyPoint P) = 3 • P := by
  cases P with
  | zero => rfl
  | some x y h =>
    by_cases hx : x = 0
    · simp only [threeIsogenyPoint, dif_pos hx, dualThreeIsogenyPoint_zero]
      exact (three_nsmul_of_x_zero h hx).symm
    · obtain ⟨h', htriple⟩ := MazurHuang.N19.good_affine_tripling_coordinates goodCurve rfl h hx
      have hphi := threeIsogenyX_ne_zero hx ((goodCurve_equation_iff x y).mp h.1)
      rw [threeIsogenyPoint_some_of_x_ne_zero h hx]
      change dualThreeIsogenyPoint (.some (threeIsogenyX x) (threeIsogenyY x y) _) = _
      rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hphi]
      exact htriple.symm
end MazurProof.XDelta19GoodIsogeny

namespace MazurProof.XDelta19GoodDescent
open MazurProof.XDelta19GoodModel
/-- The published cubeclass classification in source notation. -/
theorem good_alpha_cubeclass {x y : ℚ} (h : OnGood x y) :
  ∃ r : ℚ, y - (8 * x + 76) = r ^ 3 ∨ y - (8 * x + 76) = 19 * r ^ 3 ∨ y - (8 * x + 76) = 361 * r ^ 3 :=
  MazurHuang.N19.good_flex_cubeclasses h
end MazurProof.XDelta19GoodDescent

-- Source FLT/Assumptions/MazurProof/XDelta19GoodDescent.lean:373-471; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodDescent
open MazurProof.XDelta19GoodModel MazurProof.XDelta19GoodIsogeny
noncomputable section
/-- A nonzero cube value of the flex function constructs an explicit
preimage under the dual degree-three isogeny. -/
theorem exists_dualThreeIsogeny_preimage_of_alpha_cube
    {x y r : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y)
    (hr : r ^ 3 = y - (8 * x + 76)) (hr0 : r ≠ 0) :
    ∃ Q : QuotientPoint,
      dualThreeIsogenyPoint Q =
        WeierstrassCurve.Affine.Point.some x y h := by
  have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
  have hy : y = r ^ 3 + 8 * x + 76 := by
    linarith
  have hrel : x ^ 3 = r ^ 3 * (r ^ 3 + 16 * x + 152) := by
    unfold OnGood at hcurve
    rw [hy] at hcurve
    linear_combination -hcurve
  let d : ℚ := 3 * x - 3 * r ^ 2 - 16 * r
  have hd : d ≠ 0 := by
    intro hd
    have hx : x = r ^ 2 + 16 * r / 3 := by
      dsimp [d] at hd
      linarith
    rw [hx] at hrel
    ring_nf at hrel
    apply hr0
    have : r ^ 3 = 0 := by
      linarith
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp this
  let s : ℚ := 24 * r / d
  let t : ℚ := 9 * s * r + 24 * s + 36
  have hs : s ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) hr0) hd
  have hquotient : OnQuotient s t := by
    unfold OnQuotient
    dsimp only [t, s]
    field_simp [hd]
    dsimp only [d]
    linear_combination 46656 * hrel
  have hxmap : dualThreeIsogenyX s = x := by
    unfold dualThreeIsogenyX
    dsimp only [s]
    field_simp [hd, hr0]
    dsimp only [d]
    linear_combination -46656 * hrel
  have hymap : dualThreeIsogenyY s t = y := by
    rw [hy]
    unfold dualThreeIsogenyY
    dsimp only [t, s]
    field_simp [hd, hr0]
    dsimp only [d]
    linear_combination
      10077696 * (-2 * r ^ 2 - 8 * r + x) * hrel
  have hquotientns :
      WeierstrassCurve.Affine.Nonsingular quotientCurve s t :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((quotientCurve_equation_iff s t).mpr hquotient)
  let Q : QuotientPoint :=
    WeierstrassCurve.Affine.Point.some s t hquotientns
  refine ⟨Q, ?_⟩
  rw [dualThreeIsogenyPoint_some_of_x_ne_zero hquotientns hs]
  change WeierstrassCurve.Affine.Point.some
      (dualThreeIsogenyX s) (dualThreeIsogenyY s t) _ =
    WeierstrassCurve.Affine.Point.some x y h
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hxmap, hymap⟩

/-- Translation by the positive visible flex multiplies the flex
function by the stated rational cube factor. -/
theorem add_goodT_alpha_identity {x y : ℚ} (hx : x ≠ 0)
    (hcurve : OnGood x y) :
    let L := WeierstrassCurve.Affine.slope goodCurve x 0 y 76
    let X := WeierstrassCurve.Affine.addX goodCurve x 0 L
    let Y := WeierstrassCurve.Affine.addY goodCurve x 0 y L
    Y - (8 * X + 76) =
      -23104 * (y - (8 * x + 76)) / x ^ 3 := by
  dsimp
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX goodCurve
  field_simp [hx]
  unfold OnGood at hcurve
  linear_combination -(x ^ 3) * (8 * x + y - 228) * hcurve

/-- Translation by the negative visible flex transforms the conjugate
factor by the stated rational cube factor. -/
theorem add_goodTNeg_alpha_identity {x y : ℚ} (hx : x ≠ 0)
    (hcurve : OnGood x y) :
    let L := WeierstrassCurve.Affine.slope goodCurve x 0 y (-76)
    let X := WeierstrassCurve.Affine.addX goodCurve x 0 L
    let Y := WeierstrassCurve.Affine.addY goodCurve x 0 y L
    Y - (8 * X + 76) =
      -152 * (y + (8 * x + 76)) ^ 2 / x ^ 3 := by
  dsimp
  rw [WeierstrassCurve.Affine.slope_of_X_ne hx]
  unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negAddY
    WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.addX goodCurve
  field_simp [hx]
  unfold OnGood at hcurve
  linear_combination -(x ^ 3) * (8 * x + y + 76) * hcurve
end
end MazurProof.XDelta19GoodDescent
end

namespace MazurProof.XDelta19GoodDualDescent
open MazurProof.XDelta19GoodModel MazurProof.XDelta19GoodIsogeny
/-- The rational preimage facade in source notation. -/
theorem quotient_affine_has_threeIsogeny_preimage {s t : ℚ} (h : OnQuotient s t) :
  ∃ x y : ℚ, x ≠ 0 ∧ OnGood x y ∧ threeIsogenyX x = s ∧ threeIsogenyY x y = t :=
  MazurHuang.N19.quotient_affine_isogeny_preimage h
end MazurProof.XDelta19GoodDualDescent

-- Source FLT/Assumptions/MazurProof/XDelta19GoodDualDescent.lean:655-675; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodDualDescent
open MazurProof.XDelta19GoodModel MazurProof.XDelta19GoodIsogeny
noncomputable section
/-- The forward degree-three isogeny is surjective on rational points of
the small quotient. -/
theorem threeIsogenyPoint_surjective (Q : QuotientPoint) :
    ∃ P : GoodPoint, threeIsogenyPoint P = Q := by
  cases Q with
  | zero => exact ⟨0, threeIsogenyPoint_zero⟩
  | some s t h =>
      have hquotient : OnQuotient s t :=
        (quotientCurve_equation_iff s t).mp h.1
      obtain ⟨x, y, hx, hgood, hX, hY⟩ :=
        quotient_affine_has_threeIsogeny_preimage hquotient
      have hns : WeierstrassCurve.Affine.Nonsingular goodCurve x y :=
        WeierstrassCurve.Affine.equation_iff_nonsingular.mp
          ((goodCurve_equation_iff x y).mpr hgood)
      refine ⟨WeierstrassCurve.Affine.Point.some x y hns, ?_⟩
      rw [threeIsogenyPoint_some_of_x_ne_zero hns hx]
      change WeierstrassCurve.Affine.Point.some
          (threeIsogenyX x) (threeIsogenyY x y) _ =
        WeierstrassCurve.Affine.Point.some s t h
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hX, hY⟩
end
end MazurProof.XDelta19GoodDualDescent
end

-- Source FLT/Assumptions/MazurProof/XDelta19GoodWeakDescent.lean:4-212; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section

/-!
# Weak three-descent on the good conductor-nineteen model

The flex function has cubeclass `1`, `19`, or `19²`.  Translation by the
two visible rational flexes converts the latter two cases to the cube
case.  Surjectivity of the complementary isogeny and the verified
dual-forward composition then show that every rational point is a
threefold multiple up to one of the two nonzero visible three-torsion
points.
-/

namespace MazurProof.XDelta19GoodWeakDescent

open MazurProof.XDelta19GoodModel
open MazurProof.XDelta19GoodIsogeny
open MazurProof.XDelta19GoodDescent
open MazurProof.XDelta19GoodDualDescent

noncomputable section

/-- Every rational point on the good model is a threefold multiple up to
one of the two visible rational three-torsion points. -/
theorem weak_three_descent (P : GoodPoint) :
    ∃ Q : GoodPoint,
      P = 3 • Q ∨ P = goodT + 3 • Q ∨ P = goodTNeg + 3 • Q := by
  cases P with
  | zero =>
      exact ⟨0, Or.inl (by rfl)⟩
  | some x y h =>
      have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
      by_cases hx : x = 0
      · have hySq : y ^ 2 = (76 : ℚ) ^ 2 := by
          rw [hx] at hcurve
          norm_num [OnGood] at hcurve ⊢
          exact hcurve
        rcases eq_or_eq_neg_of_sq_eq_sq y 76 hySq with hy | hy
        · refine ⟨0, Or.inr (Or.inl ?_)⟩
          change WeierstrassCurve.Affine.Point.some x y h =
            goodT + 3 • 0
          simp only [nsmul_zero, add_zero]
          rw [goodT, WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨hx, hy⟩
        · refine ⟨0, Or.inr (Or.inr ?_)⟩
          change WeierstrassCurve.Affine.Point.some x y h =
            goodTNeg + 3 • 0
          simp only [nsmul_zero, add_zero]
          rw [goodTNeg, WeierstrassCurve.Affine.Point.some.injEq]
          exact ⟨hx, hy⟩
      · have hab :
            (y - (8 * x + 76)) * (y + (8 * x + 76)) = x ^ 3 := by
          calc
            (y - (8 * x + 76)) * (y + (8 * x + 76)) =
                y ^ 2 - (8 * x + 76) ^ 2 := by ring
            _ = x ^ 3 := by rw [hcurve]; ring
        obtain ⟨r, halpha | halpha | halpha⟩ :=
          good_alpha_cubeclass hcurve
        · have hr : r ≠ 0 := by
            intro hr0
            rw [hr0] at halpha
            norm_num at halpha
            apply hx
            have hx3 : x ^ 3 = 0 := by
              rw [← hab, halpha]
              ring
            exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hx3
          obtain ⟨Qd, hQd⟩ :=
            exists_dualThreeIsogeny_preimage_of_alpha_cube
              h halpha.symm hr
          obtain ⟨Q, hQ⟩ := threeIsogenyPoint_surjective Qd
          refine ⟨Q, Or.inl ?_⟩
          calc
            WeierstrassCurve.Affine.Point.some x y h =
                dualThreeIsogenyPoint Qd := hQd.symm
            _ = dualThreeIsogenyPoint (threeIsogenyPoint Q) := by
              rw [hQ]
            _ = 3 • Q := dual_comp_threeIsogenyPoint Q
        · have hr : r ≠ 0 := by
            intro hr0
            rw [hr0] at halpha
            norm_num at halpha
            apply hx
            have hx3 : x ^ 3 = 0 := by
              rw [← hab, halpha]
              ring
            exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hx3
          let L :=
            WeierstrassCurve.Affine.slope goodCurve x 0 y 76
          let X :=
            WeierstrassCurve.Affine.addX goodCurve x 0 L
          let Y :=
            WeierstrassCurve.Affine.addY goodCurve x 0 y L
          let hns :
              WeierstrassCurve.Affine.Nonsingular goodCurve X Y :=
            WeierstrassCurve.Affine.nonsingular_add h goodT_nonsingular
              (fun hxy => hx hxy.1)
          let Pplus : GoodPoint :=
            WeierstrassCurve.Affine.Point.some X Y hns
          have hPplus :
              (WeierstrassCurve.Affine.Point.some x y h : GoodPoint) +
                  goodT = Pplus := by
            rw [goodT]
            exact WeierstrassCurve.Affine.Point.add_of_X_ne hx
          let rp : ℚ := -76 * r / x
          have hrp : rp ≠ 0 :=
            div_ne_zero (mul_ne_zero (by norm_num) hr) hx
          have halphaP : rp ^ 3 = Y - (8 * X + 76) := by
            symm
            have hid := add_goodT_alpha_identity hx hcurve
            change Y - (8 * X + 76) =
              -23104 * (y - (8 * x + 76)) / x ^ 3 at hid
            rw [hid, halpha]
            dsimp [rp]
            field_simp [hx]
            ring
          obtain ⟨Qd, hQd⟩ :=
            exists_dualThreeIsogeny_preimage_of_alpha_cube
              hns halphaP hrp
          obtain ⟨Q, hQ⟩ := threeIsogenyPoint_surjective Qd
          have hthree : Pplus = 3 • Q := by
            calc
              Pplus = dualThreeIsogenyPoint Qd := hQd.symm
              _ = dualThreeIsogenyPoint (threeIsogenyPoint Q) := by
                rw [hQ]
              _ = 3 • Q := dual_comp_threeIsogenyPoint Q
          have hsum :
              (WeierstrassCurve.Affine.Point.some x y h : GoodPoint) +
                  goodT = 3 • Q :=
            hPplus.trans hthree
          refine ⟨Q, Or.inr (Or.inr ?_)⟩
          rw [goodTNeg_eq_neg]
          calc
            WeierstrassCurve.Affine.Point.some x y h =
                -goodT +
                  ((WeierstrassCurve.Affine.Point.some x y h : GoodPoint) +
                    goodT) := by abel
            _ = -goodT + 3 • Q := by rw [hsum]
        · have hr : r ≠ 0 := by
            intro hr0
            rw [hr0] at halpha
            norm_num at halpha
            apply hx
            have hx3 : x ^ 3 = 0 := by
              rw [← hab, halpha]
              ring
            exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hx3
          let L :=
            WeierstrassCurve.Affine.slope goodCurve x 0 y (-76)
          let X :=
            WeierstrassCurve.Affine.addX goodCurve x 0 L
          let Y :=
            WeierstrassCurve.Affine.addY goodCurve x 0 y L
          let hns :
              WeierstrassCurve.Affine.Nonsingular goodCurve X Y :=
            WeierstrassCurve.Affine.nonsingular_add h goodTNeg_nonsingular
              (fun hxy => hx hxy.1)
          let Pplus : GoodPoint :=
            WeierstrassCurve.Affine.Point.some X Y hns
          have hPplus :
              (WeierstrassCurve.Affine.Point.some x y h : GoodPoint) +
                  goodTNeg = Pplus := by
            rw [goodTNeg]
            exact WeierstrassCurve.Affine.Point.add_of_X_ne hx
          let rp : ℚ := -2 * x / (19 * r ^ 2)
          have hrp : rp ≠ 0 := by
            exact div_ne_zero (mul_ne_zero (by norm_num) hx)
              (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr))
          have halphaP : rp ^ 3 = Y - (8 * X + 76) := by
            symm
            have hid := add_goodTNeg_alpha_identity hx hcurve
            change Y - (8 * X + 76) =
              -152 * (y + (8 * x + 76)) ^ 2 / x ^ 3 at hid
            rw [hid]
            have hbeta :
                y + (8 * x + 76) = x ^ 3 / (361 * r ^ 3) := by
              apply (eq_div_iff
                (mul_ne_zero (by norm_num) (pow_ne_zero 3 hr))).2
              rw [← hab, halpha]
              ring
            rw [hbeta]
            dsimp [rp]
            field_simp [hx, hr]
            ring
          obtain ⟨Qd, hQd⟩ :=
            exists_dualThreeIsogeny_preimage_of_alpha_cube
              hns halphaP hrp
          obtain ⟨Q, hQ⟩ := threeIsogenyPoint_surjective Qd
          have hthree : Pplus = 3 • Q := by
            calc
              Pplus = dualThreeIsogenyPoint Qd := hQd.symm
              _ = dualThreeIsogenyPoint (threeIsogenyPoint Q) := by
                rw [hQ]
              _ = 3 • Q := dual_comp_threeIsogenyPoint Q
          have hsum :
              (WeierstrassCurve.Affine.Point.some x y h : GoodPoint) +
                  goodTNeg = 3 • Q :=
            hPplus.trans hthree
          refine ⟨Q, Or.inr (Or.inl ?_)⟩
          rw [goodTNeg_eq_neg] at hsum
          calc
            WeierstrassCurve.Affine.Point.some x y h =
                goodT +
                  ((WeierstrassCurve.Affine.Point.some x y h : GoodPoint) -
                    goodT) := by abel
            _ = goodT + 3 • Q := by
              congr 1

end

end MazurProof.XDelta19GoodWeakDescent

end

-- Source FLT/Assumptions/MazurProof/XDelta19GoodFormalCore.lean:543-565; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodFormalCore
open MazurProof.XDelta19GoodModel MazurProof.XDelta19GoodIsogeny MazurProof.XDelta19GoodWeakDescent
noncomputable section
/-- Weak three-descent makes `3P` divisible by every power of three. -/
theorem three_nsmul_three_power_divisible
    (P : GoodPoint) (n : ℕ) :
    ∃ Q : GoodPoint,
      3 • P = (3 ^ n : ℕ) • (3 • Q) := by
  induction n with
  | zero =>
      exact ⟨P, by simp⟩
  | succ n ih =>
      obtain ⟨Q, hQ⟩ := ih
      obtain ⟨R, hR | hR | hR⟩ := weak_three_descent Q
      all_goals
        have hthreeQ : 3 • Q = 3 • (3 • R) := by
          subst Q
          simp [nsmul_add]
        refine ⟨R, ?_⟩
        calc
          3 • P = (3 ^ n : ℕ) • (3 • Q) := hQ
          _ = (3 ^ n : ℕ) • (3 • (3 • R)) := by rw [hthreeQ]
          _ = (3 ^ (n + 1) : ℕ) • (3 • R) := by
            have hp : (3 ^ (n + 1) : ℕ) = 3 ^ n * 3 := by
              simp [pow_succ, Nat.mul_comm]
            rw [hp, mul_nsmul']
end
end MazurProof.XDelta19GoodFormalCore
end

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] (hE : E = (⟨0, 64, 0, 1216, 5776⟩ : WeierstrassCurve ℚ))
    (P : WeierstrassCurve.Affine.Point E) (n : ℕ) :
    ∃ Q : WeierstrassCurve.Affine.Point E, 3 • P = (3 ^ n : ℕ) • (3 • Q) := by
  subst E
  exact MazurProof.XDelta19GoodFormalCore.three_nsmul_three_power_divisible P n
