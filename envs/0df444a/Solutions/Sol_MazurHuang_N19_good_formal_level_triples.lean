-- Prove2me | solution 1 for MazurHuang.N19.good_formal_level_triples
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:29:42.117669+00:00
-- url     : https://prove2.me/submissions/2519ed6d-de4a-435f-b49b-ad84cebab4f2

/-
Tripling raises the exact three-adic formal level
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
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

-- Source FLT/Assumptions/MazurProof/XDelta19GoodFormalCore.lean:26-459; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodFormalCore
open MazurProof.XDelta19GoodModel MazurProof.XDelta19GoodIsogeny
noncomputable section
/-- The common denominator in the affine tripling formulas. -/
def tripleDen (x : ℚ) : ℚ :=
  x * (3 * x + 76) * (x ^ 2 + 60 * x + 912)

/-- The numerator of the horizontal tripling coordinate. -/
def tripleXNum (x : ℚ) : ℚ :=
  x ^ 9 - 14592 * x ^ 7 - 1177088 * x ^ 6 -
    35487744 * x ^ 5 - 168566784 * x ^ 4 +
    15985750016 * x ^ 3 + 409954418688 * x ^ 2 +
    3894566977536 * x + 12332795428864

/-- The factored numerator of the vertical tripling coordinate. -/
def tripleYNum (x y : ℚ) : ℚ :=
  y * (x ^ 3 - 2432 * x - 46208) *
    (x ^ 3 + 76 * x ^ 2 + 2128 * x + 23104) *
    (x ^ 6 + 180 * x ^ 5 + 13376 * x ^ 4 +
      516800 * x ^ 3 + 10905088 * x ^ 2 +
      119401472 * x + 533794816)

/-- The tripling denominator does not vanish away from the visible
three-torsion kernel. -/
theorem tripleDen_ne_zero {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    tripleDen x ≠ 0 := by
  have hquad : x ^ 2 + 60 * x + 912 ≠ 0 := by
    nlinarith [sq_nonneg (x + 30)]
  have hlin : 3 * x + 76 ≠ 0 := by
    intro hlin
    have hxval : x = -76 / 3 := by
      linarith
    rw [hxval] at h
    norm_num [OnGood] at h
    nlinarith [sq_nonneg y]
  exact mul_ne_zero (mul_ne_zero hx hlin) hquad

/-- The forward horizontal isogeny coordinate is the tripling
denominator in factored form. -/
private theorem threeIsogenyX_eq_den (x : ℚ) (hx : x ≠ 0) :
    threeIsogenyX x = 3 * tripleDen x / x ^ 3 := by
  unfold threeIsogenyX tripleDen
  field_simp [hx]
  ring

/-- The forward vertical isogeny coordinate has the displayed cubic
factor. -/
private theorem threeIsogenyY_eq_factor (x y : ℚ) (hx : x ≠ 0) :
    threeIsogenyY x y =
      27 * y * (x ^ 3 - 2432 * x - 46208) / x ^ 3 := by
  unfold threeIsogenyY
  field_simp [hx]
  ring

set_option maxHeartbeats 0 in
/-- The verified dual-forward composition has the displayed horizontal
rational function. -/
theorem tripleX_formula {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    dualThreeIsogenyX (threeIsogenyX x) =
      tripleXNum x / tripleDen x ^ 2 := by
  have hd := tripleDen_ne_zero hx h
  rw [threeIsogenyX_eq_den x hx]
  unfold dualThreeIsogenyX tripleXNum
  field_simp [hx, hd]
  unfold tripleDen
  ring

set_option maxHeartbeats 0 in
/-- The verified dual-forward composition has the displayed vertical
rational function. -/
theorem tripleY_formula {x y : ℚ} (hx : x ≠ 0)
    (h : OnGood x y) :
    dualThreeIsogenyY (threeIsogenyX x) (threeIsogenyY x y) =
      tripleYNum x y / tripleDen x ^ 3 := by
  have hd := tripleDen_ne_zero hx h
  rw [threeIsogenyX_eq_den x hx, threeIsogenyY_eq_factor x y hx]
  unfold dualThreeIsogenyY tripleYNum
  field_simp [hx, hd]
  unfold tripleDen
  ring

/-! ## Valuation helpers -/

/-- The three-adic valuation of an integer is nonnegative. -/
theorem val_int_nonneg (z : ℤ) :
    0 ≤ padicValRat 3 (z : ℚ) := by
  rw [padicValRat.of_int]
  exact Int.natCast_nonneg _

/-- In a sum of unequal valuations, the term of smaller valuation
controls the sum. -/
theorem val_add_eq_left_of_lt {a b : ℚ} (ha : a ≠ 0)
    (hval : padicValRat 3 a < padicValRat 3 b) :
    padicValRat 3 (a + b) = padicValRat 3 a := by
  by_cases hb : b = 0
  · simp [hb]
  have hab : a + b ≠ 0 := by
    intro hzero
    have hba : b = -a := by
      linarith
    have : padicValRat 3 b = padicValRat 3 a := by
      rw [hba, padicValRat.neg]
    omega
  exact padicValRat.add_eq_of_lt hab ha hb hval

/-- A finite sum of terms of valuation larger than `q` is zero or still
has valuation larger than `q`. -/
theorem val_sum_gt_or_zero {q : ℚ} (l : List ℚ)
    (hgt : ∀ a ∈ l, padicValRat 3 q < padicValRat 3 a) :
    l.sum = 0 ∨ padicValRat 3 q < padicValRat 3 l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : padicValRat 3 q < padicValRat 3 a :=
        hgt a (by simp)
      have htail : ∀ b ∈ l, padicValRat 3 q < padicValRat 3 b := by
        intro b hb
        exact hgt b (by simp [hb])
      rcases ih htail with hzero | htailgt
      · right
        simpa [hzero] using ha
      · by_cases hs : a + l.sum = 0
        · exact Or.inl (by simpa using hs)
        · exact Or.inr (padicValRat.lt_add_of_lt hs ha htailgt)

/-- Adding terms of strictly larger valuation does not change the
valuation of a nonzero leading term. -/
theorem val_add_list_eq {q : ℚ} (l : List ℚ) (hq : q ≠ 0)
    (hgt : ∀ a ∈ l, padicValRat 3 q < padicValRat 3 a) :
    padicValRat 3 (q + l.sum) = padicValRat 3 q := by
  rcases val_sum_gt_or_zero l hgt with hzero | hsum
  · simp [hzero]
  · exact val_add_eq_left_of_lt hq hsum

/-- The valuation of an integral-coefficient monomial is bounded below
by the valuations of its variables. -/
theorem val_monomial_ge
    {x y : ℚ} (hx : x ≠ 0) (hy : y ≠ 0)
    (c : ℤ) (hc : c ≠ 0) (a b : ℕ) :
    (a : ℤ) * padicValRat 3 x + (b : ℤ) * padicValRat 3 y ≤
      padicValRat 3 ((c : ℚ) * x ^ a * y ^ b) := by
  rw [padicValRat.mul
      (mul_ne_zero (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx))
      (pow_ne_zero b hy),
    padicValRat.mul (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx),
    padicValRat.pow x, padicValRat.pow y]
  have hcval := val_int_nonneg c
  omega

/-- A monic polynomial at a negative-valuation argument is controlled by
its highest-degree term when every other degree is smaller. -/
theorem val_leading_poly {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hvx : padicValRat 3 x = -2 * k)
    (n : ℕ) (l : List (ℤ × ℕ))
    (hval : ∀ cb ∈ l,
      -2 * (n : ℤ) * k < -2 * (cb.2 : ℤ) * k)
    (hcoeff : ∀ cb ∈ l, cb.1 ≠ 0) :
    padicValRat 3
        (x ^ n +
          (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum) =
      -2 * (n : ℤ) * k := by
  rw [val_add_list_eq (q := x ^ n)]
  · rw [padicValRat.pow x, hvx]
    ring
  · exact pow_ne_zero n hx
  · intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨cb, hcb, rfl⟩ := hz
    have hge := val_monomial_ge hx hy cb.1
      (hcoeff cb hcb) cb.2 0
    rw [hvx] at hge
    have hlead : padicValRat 3 (x ^ n) =
        -2 * (n : ℤ) * k := by
      rw [padicValRat.pow x, hvx]
      ring
    rw [hlead]
    norm_num at hge ⊢
    have hge' : -2 * (cb.2 : ℤ) * k ≤
        padicValRat 3 ((cb.1 : ℚ) * x ^ cb.2) := by
      convert hge using 1
      ring
    rw [show -(2 * (n : ℤ) * k) = -2 * (n : ℤ) * k by ring]
    exact (hval cb hcb).trans_le hge'

/-! ## Valuations of the tripling coordinates -/

/-- The tripling denominator has valuation `1-8k` at formal level `k`. -/
private theorem tripleDen_val {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hcurve : OnGood x y)
    (hvx : padicValRat 3 x = -2 * k) :
    padicValRat 3 (tripleDen x) = 1 - 8 * k := by
  have hlin : 3 * x + 76 ≠ 0 := by
    intro hz
    apply tripleDen_ne_zero hx hcurve
    unfold tripleDen
    rw [hz]
    ring
  have hv3x : padicValRat 3 (3 * x) = 1 - 2 * k := by
    have hthree : padicValRat 3 (3 : ℚ) = 1 :=
      padicValRat.self (p := 3) (by norm_num)
    rw [padicValRat.mul (by norm_num) hx, hthree, hvx]
    ring
  have hvlin : padicValRat 3 (3 * x + 76) = 1 - 2 * k := by
    rw [val_add_eq_left_of_lt (a := 3 * x) (b := 76)
      (mul_ne_zero (by norm_num) hx) (by
        rw [hv3x]
        have h76 : 0 ≤ padicValRat 3 (76 : ℚ) := by
          simpa using val_int_nonneg 76
        omega), hv3x]
  have hquad : x ^ 2 + 60 * x + 912 ≠ 0 := by
    nlinarith [sq_nonneg (x + 30)]
  have hvquad :
      padicValRat 3 (x ^ 2 + 60 * x + 912) = -4 * k := by
    have hshape : x ^ 2 + 60 * x + 912 =
        x ^ 2 + [60 * x, (912 : ℚ)].sum := by
      simp
      ring
    rw [hshape, val_add_list_eq (q := x ^ 2)]
    · rw [padicValRat.pow x, hvx]
      ring
    · exact pow_ne_zero 2 hx
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · have hge := val_monomial_ge hx hy 60 (by norm_num) 1 0
        rw [padicValRat.pow x, hvx]
        norm_num at hge ⊢
        omega
      · have hge := val_int_nonneg 912
        rw [padicValRat.pow x, hvx]
        norm_num at hge ⊢
        omega
  unfold tripleDen
  rw [padicValRat.mul (mul_ne_zero hx hlin) hquad,
    padicValRat.mul hx hlin, hvx, hvlin, hvquad]
  ring

/-- The horizontal tripling numerator has valuation `-18k`. -/
private theorem tripleXNum_val {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 3 x = -2 * k) :
    padicValRat 3 (tripleXNum x) = -18 * k := by
  let l : List (ℤ × ℕ) :=
    [(-14592, 7), (-1177088, 6), (-35487744, 5),
      (-168566784, 4), (15985750016, 3),
      (409954418688, 2), (3894566977536, 1),
      (12332795428864, 0)]
  have h := val_leading_poly hx hy hvx 9 l
    (by
      intro cb hcb
      simp [l] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num <;> omega)
    (by
      intro cb hcb
      simp [l] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
  convert h using 1
  · simp [l, tripleXNum]
    ring
  · ring

/-- The vertical tripling numerator has valuation `-27k`. -/
private theorem tripleYNum_val {x y : ℚ} {k : ℤ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hk : 0 < k)
    (hvx : padicValRat 3 x = -2 * k)
    (hvy : padicValRat 3 y = -3 * k) :
    padicValRat 3 (tripleYNum x y) = -27 * k := by
  let l1 : List (ℤ × ℕ) := [(-2432, 1), (-46208, 0)]
  let l2 : List (ℤ × ℕ) := [(76, 2), (2128, 1), (23104, 0)]
  let l3 : List (ℤ × ℕ) :=
    [(180, 5), (13376, 4), (516800, 3), (10905088, 2),
      (119401472, 1), (533794816, 0)]
  have hv1 :
      padicValRat 3 (x ^ 3 - 2432 * x - 46208) = -6 * k := by
    have h := val_leading_poly hx hy hvx 3 l1
      (by
        intro cb hcb
        simp [l1] at hcb
        rcases hcb with rfl | rfl <;> norm_num <;> omega)
      (by
        intro cb hcb
        simp [l1] at hcb
        rcases hcb with rfl | rfl <;> norm_num)
    convert h using 1
    · simp [l1]
      ring
    · ring
  have hv2 :
      padicValRat 3
        (x ^ 3 + 76 * x ^ 2 + 2128 * x + 23104) = -6 * k := by
    have h := val_leading_poly hx hy hvx 3 l2
      (by
        intro cb hcb
        simp [l2] at hcb
        rcases hcb with rfl | rfl | rfl <;> norm_num <;> omega)
      (by
        intro cb hcb
        simp [l2] at hcb
        rcases hcb with rfl | rfl | rfl <;> norm_num)
    convert h using 1
    · simp [l2]
      ring
    · ring
  have hv3 :
      padicValRat 3
        (x ^ 6 + 180 * x ^ 5 + 13376 * x ^ 4 +
          516800 * x ^ 3 + 10905088 * x ^ 2 +
          119401472 * x + 533794816) = -12 * k := by
    have h := val_leading_poly hx hy hvx 6 l3
      (by
        intro cb hcb
        simp [l3] at hcb
        rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;>
          norm_num <;> omega)
      (by
        intro cb hcb
        simp [l3] at hcb
        rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;>
          norm_num)
    convert h using 1
    · simp [l3]
      ring
    · ring
  have hf1 : x ^ 3 - 2432 * x - 46208 ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hv1
    omega
  have hf2 : x ^ 3 + 76 * x ^ 2 + 2128 * x + 23104 ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hv2
    omega
  have hf3 :
      x ^ 6 + 180 * x ^ 5 + 13376 * x ^ 4 +
        516800 * x ^ 3 + 10905088 * x ^ 2 +
        119401472 * x + 533794816 ≠ 0 := by
    intro hz
    rw [hz, padicValRat.zero] at hv3
    omega
  unfold tripleYNum
  rw [padicValRat.mul
      (mul_ne_zero (mul_ne_zero hy hf1) hf2) hf3,
    padicValRat.mul (mul_ne_zero hy hf1) hf2,
    padicValRat.mul hy hf1, hvy, hv1, hv2, hv3]
  ring

/-! ## The formal filtration and tripling -/

/-- Membership in the formal kernel at three, expressed by affine
coordinate valuations. -/
def FormalAtThree : GoodPoint → Prop
  | .zero => True
  | .some x y _ =>
      ∃ k : ℤ, 0 < k ∧
        padicValRat 3 x = -2 * k ∧
        padicValRat 3 y = -3 * k

/-- The exact positive level of a nonzero formal point. -/
def FormalLevel : GoodPoint → ℤ → Prop
  | .zero, _ => False
  | .some x y _, k =>
      0 < k ∧ padicValRat 3 x = -2 * k ∧
        padicValRat 3 y = -3 * k

/-- Formal-kernel membership is zero or membership at a unique positive
level. -/
theorem FormalAtThree_iff (P : GoodPoint) :
    FormalAtThree P ↔ P = 0 ∨ ∃ k : ℤ, FormalLevel P k := by
  cases P with
  | zero =>
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        trivial
  | some x y h =>
      simp only [FormalAtThree, FormalLevel,
        WeierstrassCurve.Affine.Point.some_ne_zero, false_or]

/-- Tripling raises the exact formal level by one. -/
theorem FormalLevel_triple {P : GoodPoint} {k : ℤ}
    (hP : FormalLevel P k) :
    FormalLevel (3 • P) (k + 1) := by
  cases P with
  | zero => simp [FormalLevel] at hP
  | some x y h =>
      rcases hP with ⟨hk, hvx, hvy⟩
      have hcurve : OnGood x y :=
        (goodCurve_equation_iff x y).mp h.1
      have hx : x ≠ 0 := by
        intro hx0
        rw [hx0, padicValRat.zero] at hvx
        omega
      have hy : y ≠ 0 := by
        intro hy0
        rw [hy0, padicValRat.zero] at hvy
        omega
      have hdval := tripleDen_val hx hy hk hcurve hvx
      have hXval := tripleXNum_val hx hy hk hvx
      have hYval := tripleYNum_val hx hy hk hvx hvy
      have hd : tripleDen x ≠ 0 := tripleDen_ne_zero hx hcurve
      have hX : tripleXNum x ≠ 0 := by
        intro hz
        rw [hz, padicValRat.zero] at hXval
        omega
      have hY : tripleYNum x y ≠ 0 := by
        intro hz
        rw [hz, padicValRat.zero] at hYval
        omega
      have hphi := threeIsogenyX_ne_zero hx hcurve
      have hcomp := dual_comp_threeIsogenyPoint
        (WeierstrassCurve.Affine.Point.some x y h : GoodPoint)
      rw [threeIsogenyPoint_some_of_x_ne_zero h hx] at hcomp
      unfold WeierstrassCurve.Affine.Point.mk at hcomp
      rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hphi] at hcomp
      rw [← hcomp]
      change 0 < k + 1 ∧
        padicValRat 3
          (dualThreeIsogenyX (threeIsogenyX x)) = -2 * (k + 1) ∧
        padicValRat 3
          (dualThreeIsogenyY
            (threeIsogenyX x) (threeIsogenyY x y)) =
              -3 * (k + 1)
      refine ⟨by omega, ?_, ?_⟩
      · rw [tripleX_formula hx hcurve,
          padicValRat.div hX (pow_ne_zero 2 hd), hXval,
          padicValRat.pow (tripleDen x), hdval]
        ring
      · rw [tripleY_formula hx hcurve,
          padicValRat.div hY (pow_ne_zero 3 hd), hYval,
          padicValRat.pow (tripleDen x), hdval]
        ring
end
end MazurProof.XDelta19GoodFormalCore
end

namespace MazurProof.XDelta19GoodFormalCore
open MazurProof.XDelta19GoodModel
theorem public_formal_level_iff (P : GoodPoint) (k : ℤ) :
  FormalLevel P k ↔ (∃ (x y : ℚ) (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y), P = WeierstrassCurve.Affine.Point.some x y h ∧ 0 < k ∧ padicValRat 3 x = -2 * k ∧ padicValRat 3 y = -3 * k) := by
  cases P with
  | zero =>
    constructor
    · intro hp; exact hp.elim
    · rintro ⟨x, y, h, heq, _⟩; cases heq
  | some x y h =>
    constructor
    · intro hp; exact ⟨x, y, h, rfl, hp⟩
    · rintro ⟨u, v, hu, heq, hp⟩
      rw [WeierstrassCurve.Affine.Point.some.injEq] at heq
      rcases heq with ⟨rfl, rfl⟩
      exact hp
theorem public_formal_iff (P : GoodPoint) :
  FormalAtThree P ↔ (P = 0 ∨ ∃ (x y : ℚ) (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y), P = WeierstrassCurve.Affine.Point.some x y h ∧ ∃ k : ℤ, 0 < k ∧ padicValRat 3 x = -2 * k ∧ padicValRat 3 y = -3 * k) := by
  cases P with
  | zero =>
    constructor
    · intro _; exact Or.inl rfl
    · intro _; trivial
  | some x y h =>
    constructor
    · intro hp; exact Or.inr ⟨x, y, h, rfl, hp⟩
    · rintro (hz | ⟨u, v, hu, heq, hp⟩)
      · cases hz
      · rw [WeierstrassCurve.Affine.Point.some.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact hp
end MazurProof.XDelta19GoodFormalCore

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] (hE : E = (⟨0, 64, 0, 1216, 5776⟩ : WeierstrassCurve ℚ))
    (P : WeierstrassCurve.Affine.Point E) (k : ℤ)
    (hP : (∃ (x y : ℚ) (h : WeierstrassCurve.Affine.Nonsingular E x y), P = WeierstrassCurve.Affine.Point.some x y h ∧ 0 < k ∧ padicValRat 3 x = -2 * k ∧ padicValRat 3 y = -3 * k)) :
    (∃ (x y : ℚ) (h : WeierstrassCurve.Affine.Nonsingular E x y), (3 • P) = WeierstrassCurve.Affine.Point.some x y h ∧ 0 < (k + 1) ∧ padicValRat 3 x = -2 * (k + 1) ∧ padicValRat 3 y = -3 * (k + 1)) := by
  subst E
  exact (MazurProof.XDelta19GoodFormalCore.public_formal_level_iff (3 • P) (k + 1)).mp
    (MazurProof.XDelta19GoodFormalCore.FormalLevel_triple (P := P) (k := k)
      ((MazurProof.XDelta19GoodFormalCore.public_formal_level_iff P k).mpr hP))
