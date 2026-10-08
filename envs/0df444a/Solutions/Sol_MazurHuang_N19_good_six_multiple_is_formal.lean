-- Prove2me | solution 1 for MazurHuang.N19.good_six_multiple_is_formal
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:31:34.601867+00:00
-- url     : https://prove2.me/submissions/9b7f3ebd-f39f-46ec-aeab-74f6800f326f

/-
Six times every rational good-model point lies in the formal kernel
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_MazurHuang_N19_good_affine_tripling_coordinates
import Theorems.Thm_MazurHuang_N19_good_formal_level_triples


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

-- Source FLT/Assumptions/MazurProof/XDelta19GoodFormalCore.lean:26-208; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
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
end
end MazurProof.XDelta19GoodFormalCore
end

-- Source FLT/Assumptions/MazurProof/XDelta19GoodFormalCore.lean:376-405; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodFormalCore
open MazurProof.XDelta19GoodModel MazurProof.XDelta19GoodIsogeny
noncomputable section
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

namespace MazurProof.XDelta19GoodFormalCore
open MazurProof.XDelta19GoodModel
/-- The exact-level facade is the coordinate formulation of the formal filtration. -/
theorem FormalLevel_triple {P : GoodPoint} {k : ℤ} (hP : FormalLevel P k) :
    FormalLevel (3 • P) (k + 1) :=
  (public_formal_level_iff (3 • P) (k + 1)).mpr
    (MazurHuang.N19.good_formal_level_triples goodCurve rfl P k ((public_formal_level_iff P k).mp hP))
end MazurProof.XDelta19GoodFormalCore

-- Source FLT/Assumptions/MazurProof/XDelta19GoodFormalCore.lean:461-469; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodFormalCore
open MazurProof.XDelta19GoodModel MazurProof.XDelta19GoodIsogeny
noncomputable section
/-- Tripling preserves the formal kernel and raises nonzero points one
level. -/
theorem FormalAtThree_triple {P : GoodPoint}
    (hP : FormalAtThree P) :
    FormalAtThree (3 • P) := by
  rw [FormalAtThree_iff] at hP ⊢
  rcases hP with rfl | ⟨k, hk⟩
  · simp
  · exact Or.inr ⟨k + 1, FormalLevel_triple hk⟩
end
end MazurProof.XDelta19GoodFormalCore
end

-- Source FLT/Assumptions/MazurProof/XDelta19GoodFormalReduction.lean:3-1174; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section

/-!
# Reduction into the three-adic formal kernel at level nineteen

The good model has six points over `𝔽₃`.  An integral rational point
reduces to one of

`(0,±1)`, `(1,±1)`, `(2,0)`.

For the first two pairs, doubling has positive horizontal valuation and
unit vertical valuation, so a further tripling enters the formal kernel.
For `(2,0)`, doubling itself enters the formal kernel.  Points with
negative horizontal valuation are already formal.  Consequently `[6]P`
is formal for every rational point.
-/

namespace MazurProof.XDelta19GoodFormalReduction

open MazurProof.XDelta19GoodModel
open MazurProof.XDelta19GoodIsogeny
open MazurProof.XDelta19GoodFormalCore

noncomputable section

/-! ## Integral-or-formal dichotomy -/

/-- An integral coefficient does not lower the valuation of a monomial
in one rational variable. -/
private theorem val_x_monomial_ge
    {x : ℚ} (hx : x ≠ 0) (c : ℤ) (hc : c ≠ 0) (a : ℕ) :
    (a : ℤ) * padicValRat 3 x ≤
      padicValRat 3 ((c : ℚ) * x ^ a) := by
  rw [padicValRat.mul (Int.cast_ne_zero.mpr hc) (pow_ne_zero a hx),
    padicValRat.pow x]
  have hcval := val_int_nonneg c
  omega

/-- Every rational affine point is either three-adically integral or
belongs to the formal kernel. -/
theorem formal_or_integral (P : GoodPoint) :
    FormalAtThree P ∨
      match P with
      | .zero => True
      | .some x y _ =>
          0 ≤ padicValRat 3 x ∧ 0 ≤ padicValRat 3 y := by
  cases P with
  | zero =>
      exact Or.inl trivial
  | some x y h =>
      have hE : OnGood x y := (goodCurve_equation_iff x y).mp h.1
      let vx := padicValRat 3 x
      let vy := padicValRat 3 y
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
          [-(x ^ 3), -(64 * x ^ 2), -(1216 * x), (-5776 : ℚ)]
        have hshape : y ^ 2 + l.sum = 0 := by
          simp [l]
          unfold OnGood at hE
          linear_combination hE
        have hlead : padicValRat 3 (y ^ 2) = 2 * vy := by
          rw [padicValRat.pow y]
          rfl
        have hgt : ∀ a ∈ l,
            padicValRat 3 (y ^ 2) < padicValRat 3 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl
          · by_cases hx0 : x = 0
            · simp [hx0, hlead]
              omega
            · rw [padicValRat.neg, padicValRat.pow x, hlead]
              dsimp [vx, vy] at hxint hvyneg ⊢
              omega
          · by_cases hx0 : x = 0
            · simp [hx0, hlead]
              omega
            · have hge := val_x_monomial_ge hx0 64 (by norm_num) 2
              rw [padicValRat.neg, hlead]
              dsimp [vx, vy] at hxint hvyneg hge ⊢
              omega
          · by_cases hx0 : x = 0
            · simp [hx0, hlead]
              omega
            · have hge := val_x_monomial_ge hx0 1216 (by norm_num) 1
              rw [padicValRat.neg, hlead]
              dsimp [vx, vy] at hxint hvyneg hge ⊢
              norm_num at hge
              omega
          · have hge := val_int_nonneg (-5776)
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
            [y ^ 2, -(64 * x ^ 2), -(1216 * x), (-5776 : ℚ)]
          have hshape : -(x ^ 3) + l.sum = 0 := by
            simp [l]
            unfold OnGood at hE
            linear_combination hE
          have hlead : padicValRat 3 (-(x ^ 3)) = 3 * vx := by
            rw [padicValRat.neg, padicValRat.pow x]
            rfl
          have hgt : ∀ a ∈ l,
              padicValRat 3 (-(x ^ 3)) < padicValRat 3 a := by
            intro a ha
            simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with rfl | rfl | rfl | rfl
            · by_cases hy0 : y = 0
              · simp [hy0, hlead]
                omega
              · rw [padicValRat.pow y, hlead]
                dsimp [vx, vy] at hvxneg hvxley ⊢
                omega
            · have hge := val_x_monomial_ge hx 64 (by norm_num) 2
              simp only [padicValRat.neg]
              rw [padicValRat.pow x]
              dsimp [vx] at hvxneg hge ⊢
              omega
            · have hge := val_x_monomial_ge hx 1216 (by norm_num) 1
              simp only [padicValRat.neg]
              rw [padicValRat.pow x]
              dsimp [vx] at hvxneg hge ⊢
              norm_num at hge
              omega
            · have hge := val_int_nonneg (-5776)
              rw [hlead]
              norm_num at hge ⊢
              omega
          have hval := val_add_list_eq l
            (neg_ne_zero.mpr (pow_ne_zero 3 hx)) hgt
          rw [hshape, padicValRat.zero, hlead] at hval
          omega
        have hy : y ≠ 0 := by
          intro hy0
          dsimp [vx, vy] at hvylt
          rw [hy0, padicValRat.zero] at hvylt
          omega
        let l : List ℚ :=
          [64 * x ^ 2, 1216 * x, (5776 : ℚ)]
        have hshape : x ^ 3 + l.sum =
            x ^ 3 + 64 * x ^ 2 + 1216 * x + 5776 := by
          simp [l]
          ring
        have hgt : ∀ a ∈ l,
            padicValRat 3 (x ^ 3) < padicValRat 3 a := by
          intro a ha
          simp only [l, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl
          · have hge := val_x_monomial_ge hx 64 (by norm_num) 2
            rw [padicValRat.pow x]
            dsimp [vx] at hvxneg hge ⊢
            omega
          · have hge := val_x_monomial_ge hx 1216 (by norm_num) 1
            rw [padicValRat.pow x]
            dsimp [vx] at hvxneg hge ⊢
            norm_num at hge
            omega
          · have hge := val_int_nonneg 5776
            rw [padicValRat.pow x]
            dsimp [vx] at hvxneg ⊢
            norm_num at hge ⊢
            omega
        have hvright := val_add_list_eq l (pow_ne_zero 3 hx) hgt
        have hvrel : 2 * vy = 3 * vx := by
          calc
            2 * vy = padicValRat 3 (y ^ 2) := by
              rw [padicValRat.pow y]
              dsimp [vy]
            _ = padicValRat 3 (x ^ 3 + (8 * x + 76) ^ 2) := by
              rw [hE]
            _ = padicValRat 3
                (x ^ 3 + 64 * x ^ 2 + 1216 * x + 5776) := by
              congr 1
              ring
            _ = padicValRat 3 (x ^ 3 + l.sum) := by rw [hshape]
            _ = 3 * vx := by
              rw [hvright, padicValRat.pow x]
              dsimp [vx]
        left
        change ∃ k : ℤ, 0 < k ∧
          padicValRat 3 x = -2 * k ∧
          padicValRat 3 y = -3 * k
        refine ⟨vx - vy, by omega, ?_, ?_⟩
        · dsimp [vx]
          omega
        · dsimp [vy]
          omega

/-! ## Reduction of integral rational coordinates -/

/-- A rational number of nonnegative valuation viewed as a three-adic
integer. -/
private noncomputable def ratPadicInt (q : ℚ)
    (hq : 0 ≤ padicValRat 3 q) : ℤ_[3] :=
  ⟨(q : ℚ_[3]), by
    rw [Padic.norm_le_one_iff_val_nonneg, Padic.valuation_ratCast]
    exact_mod_cast hq⟩

/-- Positive rational valuation is equivalent to zero reduction for a
nonzero integral rational number. -/
private theorem ratPadicInt_red_eq_zero_of_val_pos
    {q : ℚ} (hq : q ≠ 0) (hv : 0 < padicValRat 3 q) :
    PadicInt.toZMod (ratPadicInt q (le_of_lt hv)) = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd]
  change ‖(q : ℚ_[3])‖ < 1
  have hqcast : (q : ℚ_[3]) ≠ 0 := by
    exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, ← zpow_zero (3 : ℝ)]
  exact (zpow_lt_zpow_iff_right₀ (a := (3 : ℝ))
    (by norm_num : (1 : ℝ) < 3)).2 (by omega)

/-- Zero reduction of a nonzero integral rational number forces positive
valuation. -/
private theorem val_pos_of_padicInt_red_zero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 3 q)
    (hred : PadicInt.toZMod (ratPadicInt q hqi) = 0) :
    0 < padicValRat 3 q := by
  by_contra hnot
  have hv0 : padicValRat 3 q = 0 := by
    omega
  have hm : ratPadicInt q hqi ∈ IsLocalRing.maximalIdeal ℤ_[3] := by
    rw [← PadicInt.ker_toZMod]
    exact hred
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    ← PadicInt.norm_lt_one_iff_dvd] at hm
  change ‖(q : ℚ_[3])‖ < 1 at hm
  have hqcast : (q : ℚ_[3]) ≠ 0 := by
    exact_mod_cast hq
  rw [Padic.norm_eq_zpow_neg_valuation hqcast,
    Padic.valuation_ratCast, hv0] at hm
  norm_num at hm

/-- Nonzero reduction of an integral nonzero rational number forces
valuation zero. -/
private theorem val_zero_of_padicInt_red_nonzero
    {q : ℚ} (hq : q ≠ 0) (hqi : 0 ≤ padicValRat 3 q)
    (hred : PadicInt.toZMod (ratPadicInt q hqi) ≠ 0) :
    padicValRat 3 q = 0 := by
  by_contra hne
  have hvpos : 0 < padicValRat 3 q :=
    lt_of_le_of_ne hqi (Ne.symm hne)
  have hzero := ratPadicInt_red_eq_zero_of_val_pos hq hvpos
  have heq : ratPadicInt q hqi =
      ratPadicInt q (le_of_lt hvpos) := by
    apply Subtype.ext
    rfl
  exact hred (by rw [heq, hzero])

/-- The good equation holds in the three-adic integers for integral
rational coordinates. -/
private theorem padicInt_equation {x y : ℚ}
    (hx : 0 ≤ padicValRat 3 x) (hy : 0 ≤ padicValRat 3 y)
    (hE : OnGood x y) :
    (ratPadicInt y hy) ^ 2 =
      (ratPadicInt x hx) ^ 3 + 64 * (ratPadicInt x hx) ^ 2 +
        1216 * ratPadicInt x hx + 5776 := by
  apply Subtype.ext
  change (y : ℚ_[3]) ^ 2 =
    (x : ℚ_[3]) ^ 3 + 64 * (x : ℚ_[3]) ^ 2 +
      1216 * (x : ℚ_[3]) + 5776
  unfold OnGood at hE
  exact_mod_cast
    (show y ^ 2 = x ^ 3 + 64 * x ^ 2 + 1216 * x + 5776 by
      nlinarith [hE])

set_option maxHeartbeats 0 in
/-- Exhaustive classification of affine points on the good special fibre
over `𝔽₃`. -/
private theorem mod_three_affine_points :
    ∀ X Y : ZMod 3,
      Y ^ 2 = X ^ 3 + 64 * X ^ 2 + 1216 * X + 5776 →
      (X = 0 ∧ Y ≠ 0) ∨ (X = 1 ∧ Y ≠ 0) ∨ (X = 2 ∧ Y = 0) := by
  decide

/-- Integral rational coordinates reduce to one of the three affine
residue types. -/
private theorem integral_reduction {x y : ℚ}
    (hx : 0 ≤ padicValRat 3 x) (hy : 0 ≤ padicValRat 3 y)
    (hE : OnGood x y) :
    let X := PadicInt.toZMod (ratPadicInt x hx)
    let Y := PadicInt.toZMod (ratPadicInt y hy)
    (X = 0 ∧ Y ≠ 0) ∨ (X = 1 ∧ Y ≠ 0) ∨ (X = 2 ∧ Y = 0) := by
  have hpadic := padicInt_equation hx hy hE
  have hred :
      PadicInt.toZMod (ratPadicInt y hy) ^ 2 =
        PadicInt.toZMod (ratPadicInt x hx) ^ 3 +
          64 * PadicInt.toZMod (ratPadicInt x hx) ^ 2 +
          1216 * PadicInt.toZMod (ratPadicInt x hx) + 5776 := by
    simpa only [map_pow, map_add, map_mul, map_ofNat] using
      congrArg PadicInt.toZMod hpadic
  exact mod_three_affine_points _ _ hred

/-! ## Explicit doubling coordinates -/

/-- Horizontal coordinate of twice an affine good-model point. -/
def doubleX (x y : ℚ) : ℚ :=
  x * (x ^ 3 - 2432 * x - 46208) / (4 * y ^ 2)

/-- Vertical coordinate of twice an affine good-model point. -/
def doubleY (x y : ℚ) : ℚ :=
  (x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 + 115520 * x ^ 3 -
      28094464 * x - 266897408) / (8 * y ^ 3)

/-- The library doubling formula has the displayed horizontal
coordinate. -/
private theorem addX_self_eq_doubleX {x y : ℚ}
    (hy : y ≠ 0) (h : OnGood x y) :
    let L := WeierstrassCurve.Affine.slope goodCurve x x y y
    WeierstrassCurve.Affine.addX goodCurve x x L = doubleX x y := by
  dsimp
  have hneg : y ≠ WeierstrassCurve.Affine.negY goodCurve x y := by
    rw [goodCurve_negY]
    intro heq
    apply hy
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  unfold WeierstrassCurve.Affine.negY goodCurve doubleX
  field_simp [hy]
  unfold OnGood at h
  ring_nf at h ⊢
  linear_combination
    -32 * y ^ 2 * (x + 32) * h

/-- The library doubling formula has the displayed vertical
coordinate. -/
private theorem addY_self_eq_doubleY {x y : ℚ}
    (hy : y ≠ 0) (h : OnGood x y) :
    let L := WeierstrassCurve.Affine.slope goodCurve x x y y
    WeierstrassCurve.Affine.addY goodCurve x x y L = doubleY x y := by
  dsimp
  have hneg : y ≠ WeierstrassCurve.Affine.negY goodCurve x y := by
    rw [goodCurve_negY]
    intro heq
    apply hy
    linarith
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hneg]
  unfold WeierstrassCurve.Affine.addY
  unfold WeierstrassCurve.Affine.negAddY
  unfold WeierstrassCurve.Affine.negY
  unfold WeierstrassCurve.Affine.addX
  unfold goodCurve doubleY
  field_simp [hy]
  unfold OnGood at h
  ring_nf at h ⊢
  linear_combination
    32 * y ^ 3 *
      (7 * x ^ 3 + 448 * x ^ 2 + 9408 * x -
        2 * y ^ 2 + 66272) * h

/-- The displayed doubling coordinates are nonsingular because they are the
coordinates produced by the affine group law. -/
private theorem double_nonsingular {x y : ℚ}
    (hy : y ≠ 0)
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y) :
    WeierstrassCurve.Affine.Nonsingular goodCurve
      (doubleX x y) (doubleY x y) := by
  have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
  have hneg : y ≠ WeierstrassCurve.Affine.negY goodCurve x y := by
    rw [goodCurve_negY]
    intro heq
    apply hy
    linarith
  have hxadd := addX_self_eq_doubleX hy hcurve
  have hyadd := addY_self_eq_doubleY hy hcurve
  rw [← hxadd, ← hyadd]
  exact WeierstrassCurve.Affine.nonsingular_add h h
    (fun hxy => hneg hxy.right)

/-- Doubling a good-model point agrees with the two displayed rational
coordinate functions. -/
private theorem two_nsmul_eq_double_point {x y : ℚ}
    (hy : y ≠ 0)
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y) :
    2 • (WeierstrassCurve.Affine.Point.some x y h : GoodPoint) =
      WeierstrassCurve.Affine.Point.some (doubleX x y) (doubleY x y)
        (double_nonsingular hy h) := by
  have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
  have hneg : y ≠ WeierstrassCurve.Affine.negY goodCurve x y := by
    rw [goodCurve_negY]
    intro heq
    apply hy
    linarith
  rw [two_nsmul,
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg,
    WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨addX_self_eq_doubleX hy hcurve,
    addY_self_eq_doubleY hy hcurve⟩

/-- A rational integer prime to three has valuation zero. -/
private theorem val_int_unit (z : ℤ) (hz : ¬(3 : ℤ) ∣ z) :
    padicValRat 3 (z : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hz]
  norm_num

/-- A polynomial with unit constant term and all other terms of positive
valuation is a three-adic unit. -/
private theorem val_unit_constant_poly
    {x : ℚ} (hx : x ≠ 0) (hvx : 0 < padicValRat 3 x)
    (c : ℤ) (hc : ¬(3 : ℤ) ∣ c) (l : List (ℤ × ℕ))
    (hexp : ∀ cb ∈ l, 0 < cb.2)
    (hcoeff : ∀ cb ∈ l, cb.1 ≠ 0) :
    (c : ℚ) +
        (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum ≠ 0 ∧
      padicValRat 3
        ((c : ℚ) +
          (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum) = 0 := by
  have hc0 : (c : ℚ) ≠ 0 :=
    Int.cast_ne_zero.mpr (fun hz => hc (by simp [hz]))
  have hgt : ∀ a ∈
      (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2),
      padicValRat 3 (c : ℚ) < padicValRat 3 a := by
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨cb, hcb, rfl⟩ := ha
    have hge := val_x_monomial_ge hx cb.1
      (hcoeff cb hcb) cb.2
    rw [val_int_unit c hc]
    have hp := hexp cb hcb
    have hpZ : (0 : ℤ) < (cb.2 : ℤ) := by
      exact_mod_cast hp
    exact (mul_pos hpZ hvx).trans_le hge
  have hval := val_add_list_eq
    (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2) hc0 hgt
  have hne :
      (c : ℚ) +
        (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum ≠ 0 := by
    intro hz
    have hsum :
        (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum = -(c : ℚ) := by
      linarith
    rcases val_sum_gt_or_zero
      (l.map fun cb => (cb.1 : ℚ) * x ^ cb.2) hgt with
      hzero | hsumgt
    · rw [hzero] at hsum
      exact hc0 (by linarith)
    · rw [hsum, padicValRat.neg] at hsumgt
      omega
  exact ⟨hne, by rw [hval, val_int_unit c hc]⟩

/-! ## Doubling and tripling inside the formal kernel -/

/-- Doubling preserves every positive formal level. -/
theorem FormalLevel_double {P : GoodPoint} {k : ℤ}
    (hP : FormalLevel P k) :
    FormalLevel (2 • P) k := by
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
      let l3 : List (ℤ × ℕ) := [(-2432, 1), (-46208, 0)]
      have hv3 :
          padicValRat 3 (x ^ 3 - 2432 * x - 46208) = -6 * k := by
        have hv := val_leading_poly hx hy hvx 3 l3
          (by
            intro cb hcb
            simp [l3] at hcb
            rcases hcb with rfl | rfl <;> norm_num <;> omega)
          (by
            intro cb hcb
            simp [l3] at hcb
            rcases hcb with rfl | rfl <;> norm_num)
        convert hv using 1
        · simp [l3]
          ring
        · ring
      have hf3 : x ^ 3 - 2432 * x - 46208 ≠ 0 := by
        intro hz
        rw [hz, padicValRat.zero] at hv3
        omega
      let l6 : List (ℤ × ℕ) :=
        [(128, 5), (6080, 4), (115520, 3),
          (-28094464, 1), (-266897408, 0)]
      have hv6 :
          padicValRat 3
            (x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
              115520 * x ^ 3 - 28094464 * x - 266897408) =
            -12 * k := by
        have hv := val_leading_poly hx hy hvx 6 l6
          (by
            intro cb hcb
            simp [l6] at hcb
            rcases hcb with rfl | rfl | rfl | rfl | rfl <;>
              norm_num <;> omega)
          (by
            intro cb hcb
            simp [l6] at hcb
            rcases hcb with rfl | rfl | rfl | rfl | rfl <;>
              norm_num)
        convert hv using 1
        · simp [l6]
          ring
        · ring
      have hf6 :
          x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
            115520 * x ^ 3 - 28094464 * x - 266897408 ≠ 0 := by
        intro hz
        rw [hz, padicValRat.zero] at hv6
        omega
      have hdx : doubleX x y ≠ 0 := by
        unfold doubleX
        exact div_ne_zero (mul_ne_zero hx hf3)
          (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
      have hdy : doubleY x y ≠ 0 := by
        unfold doubleY
        exact div_ne_zero hf6
          (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy))
      have hvdx : padicValRat 3 (doubleX x y) = -2 * k := by
        have hv4 : padicValRat 3 (4 : ℚ) = 0 :=
          val_int_unit 4 (by norm_num)
        unfold doubleX
        rw [padicValRat.div (mul_ne_zero hx hf3)
            (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)),
          padicValRat.mul hx hf3, hvx, hv3,
          padicValRat.mul (by norm_num) (pow_ne_zero 2 hy),
          hv4, padicValRat.pow y, hvy]
        ring
      have hvdy : padicValRat 3 (doubleY x y) = -3 * k := by
        have hv8 : padicValRat 3 (8 : ℚ) = 0 :=
          val_int_unit 8 (by norm_num)
        unfold doubleY
        rw [padicValRat.div hf6
            (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy)),
          hv6, padicValRat.mul (by norm_num) (pow_ne_zero 3 hy),
          hv8, padicValRat.pow y, hvy]
        ring
      have hneg : y ≠ WeierstrassCurve.Affine.negY goodCurve x y := by
        rw [goodCurve_negY]
        intro heq
        apply hy
        linarith
      rw [two_nsmul,
        WeierstrassCurve.Affine.Point.add_self_of_Y_ne hneg]
      change 0 < k ∧
        padicValRat 3
          (WeierstrassCurve.Affine.addX goodCurve x x
            (WeierstrassCurve.Affine.slope goodCurve x x y y)) =
              -2 * k ∧
        padicValRat 3
          (WeierstrassCurve.Affine.addY goodCurve x x y
            (WeierstrassCurve.Affine.slope goodCurve x x y y)) =
              -3 * k
      rw [addX_self_eq_doubleX hy hcurve,
        addY_self_eq_doubleY hy hcurve]
      exact ⟨hk, hvdx, hvdy⟩

/-- Doubling preserves the three-adic formal kernel. -/
theorem FormalAtThree_double {P : GoodPoint}
    (hP : FormalAtThree P) :
    FormalAtThree (2 • P) := by
  rw [FormalAtThree_iff] at hP ⊢
  rcases hP with rfl | ⟨k, hk⟩
  · simp
  · exact Or.inr ⟨k, FormalLevel_double hk⟩

/-- A point with positive horizontal valuation and unit vertical
valuation enters the formal kernel after tripling. -/
private theorem triple_formal_of_x_pos
    {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y)
    (hvx : 0 < padicValRat 3 x)
    (hvy : padicValRat 3 y = 0) :
    FormalAtThree
      (3 • (WeierstrassCurve.Affine.Point.some x y h : GoodPoint)) := by
  have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, padicValRat.zero] at hvx
    omega
  have hy : y ≠ 0 := good_y_ne_zero hcurve
  have hd := tripleDen_ne_zero hx hcurve
  have hlin : 3 * x + 76 ≠ 0 := by
    intro hz
    apply hd
    unfold tripleDen
    rw [hz]
    ring
  have hquad : x ^ 2 + 60 * x + 912 ≠ 0 := by
    nlinarith [sq_nonneg (x + 30)]
  have hv3 : padicValRat 3 (3 : ℚ) = 1 :=
    padicValRat.self (p := 3) (by norm_num)
  have hv76 : padicValRat 3 (76 : ℚ) = 0 :=
    val_int_unit 76 (by norm_num)
  have hv3x : padicValRat 3 (3 * x) =
      1 + padicValRat 3 x := by
    rw [padicValRat.mul (by norm_num) hx, hv3]
  have hvlin : padicValRat 3 (3 * x + 76) = 0 := by
    rw [add_comm, val_add_eq_left_of_lt (a := (76 : ℚ))
      (b := 3 * x) (by norm_num)
      (by rw [hv76, hv3x]; omega), hv76]
  have hv20 : padicValRat 3 (20 : ℚ) = 0 :=
    val_int_unit 20 (by norm_num)
  have hv60 : padicValRat 3 (60 : ℚ) = 1 := by
    rw [show (60 : ℚ) = 3 * 20 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num), hv3, hv20]
    norm_num
  have hv304 : padicValRat 3 (304 : ℚ) = 0 :=
    val_int_unit 304 (by norm_num)
  have hv912 : padicValRat 3 (912 : ℚ) = 1 := by
    rw [show (912 : ℚ) = 3 * 304 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num), hv3, hv304]
    norm_num
  let lq : List ℚ := [x ^ 2, 60 * x]
  have hshape : (912 : ℚ) + lq.sum =
      x ^ 2 + 60 * x + 912 := by
    simp [lq]
    ring
  have hgt : ∀ a ∈ lq,
      padicValRat 3 (912 : ℚ) < padicValRat 3 a := by
    intro a ha
    simp only [lq, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · rw [hv912, padicValRat.pow x]
      omega
    · rw [hv912, padicValRat.mul (by norm_num) hx, hv60]
      omega
  have hvquad := val_add_list_eq lq (by norm_num) hgt
  rw [hshape, hv912] at hvquad
  have hdval : padicValRat 3 (tripleDen x) =
      padicValRat 3 x + 1 := by
    unfold tripleDen
    rw [padicValRat.mul (mul_ne_zero hx hlin) hquad,
      padicValRat.mul hx hlin, hvlin, hvquad]
    ring
  let lx : List (ℤ × ℕ) :=
    [(1, 9), (-14592, 7), (-1177088, 6), (-35487744, 5),
      (-168566784, 4), (15985750016, 3), (409954418688, 2),
      (3894566977536, 1)]
  have hX := val_unit_constant_poly hx hvx 12332795428864
    (by norm_num) lx
    (by
      intro cb hcb
      simp [lx] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
    (by
      intro cb hcb
      simp [lx] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
  have hXshape : ((12332795428864 : ℤ) : ℚ) +
      (lx.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum =
        tripleXNum x := by
    simp [lx, tripleXNum]
    ring
  rw [hXshape] at hX
  obtain ⟨hXne, hXval⟩ := hX
  let l1 : List (ℤ × ℕ) := [(1, 3), (-2432, 1)]
  let l2 : List (ℤ × ℕ) := [(1, 3), (76, 2), (2128, 1)]
  let l3 : List (ℤ × ℕ) :=
    [(1, 6), (180, 5), (13376, 4), (516800, 3),
      (10905088, 2), (119401472, 1)]
  have h1 := val_unit_constant_poly hx hvx (-46208) (by norm_num) l1
    (by
      intro cb hcb
      simp [l1] at hcb
      rcases hcb with rfl | rfl <;> norm_num)
    (by
      intro cb hcb
      simp [l1] at hcb
      rcases hcb with rfl | rfl <;> norm_num)
  have h2 := val_unit_constant_poly hx hvx 23104 (by norm_num) l2
    (by
      intro cb hcb
      simp [l2] at hcb
      rcases hcb with rfl | rfl | rfl <;> norm_num)
    (by
      intro cb hcb
      simp [l2] at hcb
      rcases hcb with rfl | rfl | rfl <;> norm_num)
  have h3 := val_unit_constant_poly hx hvx 533794816
    (by norm_num) l3
    (by
      intro cb hcb
      simp [l3] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
    (by
      intro cb hcb
      simp [l3] at hcb
      rcases hcb with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num)
  have hs1 : (((-46208 : ℤ) : ℚ)) +
      (l1.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum =
        x ^ 3 - 2432 * x - 46208 := by
    simp [l1]
    ring
  have hs2 : ((23104 : ℤ) : ℚ) +
      (l2.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum =
        x ^ 3 + 76 * x ^ 2 + 2128 * x + 23104 := by
    simp [l2]
    ring
  have hs3 : ((533794816 : ℤ) : ℚ) +
      (l3.map fun cb => (cb.1 : ℚ) * x ^ cb.2).sum =
        x ^ 6 + 180 * x ^ 5 + 13376 * x ^ 4 +
          516800 * x ^ 3 + 10905088 * x ^ 2 +
          119401472 * x + 533794816 := by
    simp [l3]
    ring
  rw [hs1] at h1
  rw [hs2] at h2
  rw [hs3] at h3
  rcases h1 with ⟨hne1, hv1⟩
  rcases h2 with ⟨hne2, hv2⟩
  rcases h3 with ⟨hne3, hv3f⟩
  have hYne : tripleYNum x y ≠ 0 := by
    unfold tripleYNum
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hy hne1) hne2) hne3
  have hYval : padicValRat 3 (tripleYNum x y) = 0 := by
    unfold tripleYNum
    rw [padicValRat.mul
        (mul_ne_zero (mul_ne_zero hy hne1) hne2) hne3,
      padicValRat.mul (mul_ne_zero hy hne1) hne2,
      padicValRat.mul hy hne1, hvy, hv1, hv2, hv3f]
    ring
  have hphi := threeIsogenyX_ne_zero hx hcurve
  have hcomp := dual_comp_threeIsogenyPoint
    (WeierstrassCurve.Affine.Point.some x y h : GoodPoint)
  rw [threeIsogenyPoint_some_of_x_ne_zero h hx] at hcomp
  unfold WeierstrassCurve.Affine.Point.mk at hcomp
  rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hphi] at hcomp
  rw [← hcomp]
  change ∃ k : ℤ, 0 < k ∧
    padicValRat 3
      (dualThreeIsogenyX (threeIsogenyX x)) = -2 * k ∧
    padicValRat 3
      (dualThreeIsogenyY
        (threeIsogenyX x) (threeIsogenyY x y)) = -3 * k
  refine ⟨padicValRat 3 x + 1, by omega, ?_, ?_⟩
  · rw [tripleX_formula hx hcurve,
      padicValRat.div hXne (pow_ne_zero 2 hd), hXval,
      padicValRat.pow (tripleDen x), hdval]
    ring
  · rw [tripleY_formula hx hcurve,
      padicValRat.div hYne (pow_ne_zero 3 hd), hYval,
      padicValRat.pow (tripleDen x), hdval]
    ring

/-- An affine point with first coordinate zero is killed by three and
therefore is formally trivial after tripling. -/
private theorem triple_formal_of_x_zero
    {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y)
    (hx : x = 0) :
    FormalAtThree
      (3 • (WeierstrassCurve.Affine.Point.some x y h : GoodPoint)) := by
  rw [three_nsmul_of_x_zero h hx]
  trivial

/-! ## Reading valuations from explicit PadicInt models -/

/-- A PadicInt expression whose value is rational certifies nonnegative
rational valuation. -/
private theorem val_nonneg_of_padicInt_model
    {q : ℚ} (qi : ℤ_[3])
    (hcoe : (qi : ℚ_[3]) = (q : ℚ_[3])) :
    0 ≤ padicValRat 3 q := by
  have hp := qi.property
  rw [hcoe, Padic.norm_le_one_iff_val_nonneg,
    Padic.valuation_ratCast] at hp
  exact_mod_cast hp

/-- Nonzero reduction of a rational PadicInt model forces rational
valuation zero. -/
private theorem val_zero_of_padicInt_model
    {q : ℚ} (hq : q ≠ 0) (qi : ℤ_[3])
    (hcoe : (qi : ℚ_[3]) = (q : ℚ_[3]))
    (hred : PadicInt.toZMod qi ≠ 0) :
    padicValRat 3 q = 0 := by
  have hqint := val_nonneg_of_padicInt_model qi hcoe
  have heq : ratPadicInt q hqint = qi := by
    apply Subtype.ext
    exact hcoe.symm
  apply val_zero_of_padicInt_red_nonzero hq hqint
  rwa [heq]

/-- Zero reduction of a nonzero rational PadicInt model forces positive
rational valuation. -/
private theorem val_pos_of_padicInt_model
    {q : ℚ} (hq : q ≠ 0) (qi : ℤ_[3])
    (hcoe : (qi : ℚ_[3]) = (q : ℚ_[3]))
    (hred : PadicInt.toZMod qi = 0) :
    0 < padicValRat 3 q := by
  have hqint := val_nonneg_of_padicInt_model qi hcoe
  have heq : ratPadicInt q hqint = qi := by
    apply Subtype.ext
    exact hcoe.symm
  apply val_pos_of_padicInt_red_zero hq hqint
  rwa [heq]

/-! ## Entry after multiplication by six -/

set_option maxHeartbeats 0 in
/-- Every rational point enters the three-adic formal kernel after
multiplication by six. -/
theorem six_nsmul_formal (P : GoodPoint) :
    FormalAtThree (6 • P) := by
  rcases formal_or_integral P with hformal | hintegral
  · have hdouble := FormalAtThree_double hformal
    have htriple := FormalAtThree_triple hdouble
    simpa only [show (6 : ℕ) = 3 * 2 by norm_num, mul_nsmul'] using htriple
  · cases P with
    | zero => trivial
    | some x y h =>
        rcases hintegral with ⟨hxint, hyint⟩
        have hcurve : OnGood x y :=
          (goodCurve_equation_iff x y).mp h.1
        have hy : y ≠ 0 := good_y_ne_zero hcurve
        let xi : ℤ_[3] := ratPadicInt x hxint
        let yi : ℤ_[3] := ratPadicInt y hyint
        obtain hred | hred | hred :=
          integral_reduction hxint hyint hcurve
        · rcases hred with ⟨hxred, hyred⟩
          have hvy : padicValRat 3 y = 0 :=
            val_zero_of_padicInt_red_nonzero hy hyint hyred
          let nxi : ℤ_[3] :=
            xi * (xi ^ 3 - 2432 * xi - 46208)
          let nyi : ℤ_[3] :=
            xi ^ 6 + 128 * xi ^ 5 + 6080 * xi ^ 4 +
              115520 * xi ^ 3 - 28094464 * xi - 266897408
          have hnxcoe :
              (nxi : ℚ_[3]) =
                (x * (x ^ 3 - 2432 * x - 46208) : ℚ) := by
            change
              (x : ℚ_[3]) *
                  ((x : ℚ_[3]) ^ 3 - 2432 * (x : ℚ_[3]) - 46208) =
                ((x * (x ^ 3 - 2432 * x - 46208) : ℚ) : ℚ_[3])
            norm_num
          have hnycoe :
              (nyi : ℚ_[3]) =
                (x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) := by
            change
              (x : ℚ_[3]) ^ 6 + 128 * (x : ℚ_[3]) ^ 5 +
                    6080 * (x : ℚ_[3]) ^ 4 +
                    115520 * (x : ℚ_[3]) ^ 3 -
                    28094464 * (x : ℚ_[3]) - 266897408 =
                ((x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) : ℚ_[3])
            norm_num
          have hnxred : PadicInt.toZMod nxi = 0 := by
            simp [nxi, xi, hxred]
          have hnyred : PadicInt.toZMod nyi ≠ 0 := by
            simp [nyi, xi, hxred]
            norm_num only [map_ofNat]
            decide
          let nx : ℚ := x * (x ^ 3 - 2432 * x - 46208)
          let ny : ℚ :=
            x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
              115520 * x ^ 3 - 28094464 * x - 266897408
          have hny : ny ≠ 0 := by
            intro hzero
            apply hnyred
            have : nyi = 0 := by
              apply Subtype.ext
              rw [hnycoe]
              change ((ny : ℚ) : ℚ_[3]) = 0
              rw [hzero]
              norm_num
            rw [this, map_zero]
          have hvny : padicValRat 3 ny = 0 :=
            val_zero_of_padicInt_model hny nyi hnycoe hnyred
          by_cases hnx : nx = 0
          · have hdx : doubleX x y = 0 := by
              unfold doubleX
              change nx / (4 * y ^ 2) = 0
              rw [hnx]
              simp
            let hd := double_nonsingular hy h
            have hdouble := two_nsmul_eq_double_point hy h
            rw [show (6 : ℕ) = 3 * 2 by norm_num, mul_nsmul', hdouble]
            exact triple_formal_of_x_zero hd hdx
          · have hvnx : 0 < padicValRat 3 nx :=
              val_pos_of_padicInt_model hnx nxi hnxcoe hnxred
            have hdx : doubleX x y ≠ 0 := by
              unfold doubleX
              change nx / (4 * y ^ 2) ≠ 0
              exact div_ne_zero hnx
                (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
            have hdy : doubleY x y ≠ 0 := by
              unfold doubleY
              change ny / (8 * y ^ 3) ≠ 0
              exact div_ne_zero hny
                (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy))
            have hvdx : 0 < padicValRat 3 (doubleX x y) := by
              have hv4 : padicValRat 3 (4 : ℚ) = 0 :=
                val_int_unit 4 (by norm_num)
              unfold doubleX
              change 0 < padicValRat 3 (nx / (4 * y ^ 2))
              rw [padicValRat.div hnx
                  (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)),
                padicValRat.mul (by norm_num) (pow_ne_zero 2 hy),
                hv4, padicValRat.pow y, hvy]
              omega
            have hvdy : padicValRat 3 (doubleY x y) = 0 := by
              have hv8 : padicValRat 3 (8 : ℚ) = 0 :=
                val_int_unit 8 (by norm_num)
              unfold doubleY
              change padicValRat 3 (ny / (8 * y ^ 3)) = 0
              rw [padicValRat.div hny
                  (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy)),
                hvny, padicValRat.mul (by norm_num) (pow_ne_zero 3 hy),
                hv8, padicValRat.pow y, hvy]
              ring
            let hd := double_nonsingular hy h
            have hdouble := two_nsmul_eq_double_point hy h
            rw [show (6 : ℕ) = 3 * 2 by norm_num, mul_nsmul', hdouble]
            exact triple_formal_of_x_pos hd hvdx hvdy
        · rcases hred with ⟨hxred, hyred⟩
          have hvy : padicValRat 3 y = 0 :=
            val_zero_of_padicInt_red_nonzero hy hyint hyred
          let nxi : ℤ_[3] :=
            xi * (xi ^ 3 - 2432 * xi - 46208)
          let nyi : ℤ_[3] :=
            xi ^ 6 + 128 * xi ^ 5 + 6080 * xi ^ 4 +
              115520 * xi ^ 3 - 28094464 * xi - 266897408
          have hnxcoe :
              (nxi : ℚ_[3]) =
                (x * (x ^ 3 - 2432 * x - 46208) : ℚ) := by
            change
              (x : ℚ_[3]) *
                  ((x : ℚ_[3]) ^ 3 - 2432 * (x : ℚ_[3]) - 46208) =
                ((x * (x ^ 3 - 2432 * x - 46208) : ℚ) : ℚ_[3])
            norm_num
          have hnycoe :
              (nyi : ℚ_[3]) =
                (x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) := by
            change
              (x : ℚ_[3]) ^ 6 + 128 * (x : ℚ_[3]) ^ 5 +
                    6080 * (x : ℚ_[3]) ^ 4 +
                    115520 * (x : ℚ_[3]) ^ 3 -
                    28094464 * (x : ℚ_[3]) - 266897408 =
                ((x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) : ℚ_[3])
            norm_num
          have hnxred : PadicInt.toZMod nxi = 0 := by
            simp [nxi, xi, hxred]
            norm_num only [map_ofNat]
            decide
          have hnyred : PadicInt.toZMod nyi ≠ 0 := by
            simp [nyi, xi, hxred]
            norm_num only [map_ofNat]
            decide
          let nx : ℚ := x * (x ^ 3 - 2432 * x - 46208)
          let ny : ℚ :=
            x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
              115520 * x ^ 3 - 28094464 * x - 266897408
          have hny : ny ≠ 0 := by
            intro hzero
            apply hnyred
            have : nyi = 0 := by
              apply Subtype.ext
              rw [hnycoe]
              change ((ny : ℚ) : ℚ_[3]) = 0
              rw [hzero]
              norm_num
            rw [this, map_zero]
          have hvny : padicValRat 3 ny = 0 :=
            val_zero_of_padicInt_model hny nyi hnycoe hnyred
          by_cases hnx : nx = 0
          · have hdx : doubleX x y = 0 := by
              unfold doubleX
              change nx / (4 * y ^ 2) = 0
              rw [hnx]
              simp
            let hd := double_nonsingular hy h
            have hdouble := two_nsmul_eq_double_point hy h
            rw [show (6 : ℕ) = 3 * 2 by norm_num, mul_nsmul', hdouble]
            exact triple_formal_of_x_zero hd hdx
          · have hvnx : 0 < padicValRat 3 nx :=
              val_pos_of_padicInt_model hnx nxi hnxcoe hnxred
            have hdx : doubleX x y ≠ 0 := by
              unfold doubleX
              change nx / (4 * y ^ 2) ≠ 0
              exact div_ne_zero hnx
                (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
            have hdy : doubleY x y ≠ 0 := by
              unfold doubleY
              change ny / (8 * y ^ 3) ≠ 0
              exact div_ne_zero hny
                (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy))
            have hvdx : 0 < padicValRat 3 (doubleX x y) := by
              have hv4 : padicValRat 3 (4 : ℚ) = 0 :=
                val_int_unit 4 (by norm_num)
              unfold doubleX
              change 0 < padicValRat 3 (nx / (4 * y ^ 2))
              rw [padicValRat.div hnx
                  (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)),
                padicValRat.mul (by norm_num) (pow_ne_zero 2 hy),
                hv4, padicValRat.pow y, hvy]
              omega
            have hvdy : padicValRat 3 (doubleY x y) = 0 := by
              have hv8 : padicValRat 3 (8 : ℚ) = 0 :=
                val_int_unit 8 (by norm_num)
              unfold doubleY
              change padicValRat 3 (ny / (8 * y ^ 3)) = 0
              rw [padicValRat.div hny
                  (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy)),
                hvny, padicValRat.mul (by norm_num) (pow_ne_zero 3 hy),
                hv8, padicValRat.pow y, hvy]
              ring
            let hd := double_nonsingular hy h
            have hdouble := two_nsmul_eq_double_point hy h
            rw [show (6 : ℕ) = 3 * 2 by norm_num, mul_nsmul', hdouble]
            exact triple_formal_of_x_pos hd hvdx hvdy
        · rcases hred with ⟨hxred, hyred⟩
          have hx : x ≠ 0 := by
            intro hx0
            subst x
            simp [ratPadicInt] at hxred
            exact (by decide : (0 : ZMod 3) ≠ 2) hxred
          have hvx : padicValRat 3 x = 0 :=
            val_zero_of_padicInt_red_nonzero hx hxint (by
              rw [hxred]
              decide)
          have hvypos : 0 < padicValRat 3 y :=
            val_pos_of_padicInt_red_zero hy hyint hyred
          let nxi : ℤ_[3] :=
            xi * (xi ^ 3 - 2432 * xi - 46208)
          let nyi : ℤ_[3] :=
            xi ^ 6 + 128 * xi ^ 5 + 6080 * xi ^ 4 +
              115520 * xi ^ 3 - 28094464 * xi - 266897408
          have hnxcoe :
              (nxi : ℚ_[3]) =
                (x * (x ^ 3 - 2432 * x - 46208) : ℚ) := by
            change
              (x : ℚ_[3]) *
                  ((x : ℚ_[3]) ^ 3 - 2432 * (x : ℚ_[3]) - 46208) =
                ((x * (x ^ 3 - 2432 * x - 46208) : ℚ) : ℚ_[3])
            norm_num
          have hnycoe :
              (nyi : ℚ_[3]) =
                (x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) := by
            change
              (x : ℚ_[3]) ^ 6 + 128 * (x : ℚ_[3]) ^ 5 +
                    6080 * (x : ℚ_[3]) ^ 4 +
                    115520 * (x : ℚ_[3]) ^ 3 -
                    28094464 * (x : ℚ_[3]) - 266897408 =
                ((x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
                  115520 * x ^ 3 - 28094464 * x -
                  266897408 : ℚ) : ℚ_[3])
            norm_num
          have hnxred : PadicInt.toZMod nxi ≠ 0 := by
            simp [nxi, xi, hxred]
            norm_num only [map_ofNat]
            decide
          have hnyred : PadicInt.toZMod nyi ≠ 0 := by
            simp [nyi, xi, hxred]
            norm_num only [map_ofNat]
            decide
          let nx : ℚ := x * (x ^ 3 - 2432 * x - 46208)
          let ny : ℚ :=
            x ^ 6 + 128 * x ^ 5 + 6080 * x ^ 4 +
              115520 * x ^ 3 - 28094464 * x - 266897408
          have hnx : nx ≠ 0 := by
            intro hzero
            apply hnxred
            have : nxi = 0 := by
              apply Subtype.ext
              rw [hnxcoe]
              change ((nx : ℚ) : ℚ_[3]) = 0
              rw [hzero]
              norm_num
            rw [this, map_zero]
          have hny : ny ≠ 0 := by
            intro hzero
            apply hnyred
            have : nyi = 0 := by
              apply Subtype.ext
              rw [hnycoe]
              change ((ny : ℚ) : ℚ_[3]) = 0
              rw [hzero]
              norm_num
            rw [this, map_zero]
          have hvnx : padicValRat 3 nx = 0 :=
            val_zero_of_padicInt_model hnx nxi hnxcoe hnxred
          have hvny : padicValRat 3 ny = 0 :=
            val_zero_of_padicInt_model hny nyi hnycoe hnyred
          have hdx : doubleX x y ≠ 0 := by
            unfold doubleX
            change nx / (4 * y ^ 2) ≠ 0
            exact div_ne_zero hnx
              (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy))
          have hdy : doubleY x y ≠ 0 := by
            unfold doubleY
            change ny / (8 * y ^ 3) ≠ 0
            exact div_ne_zero hny
              (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy))
          have hvdx :
              padicValRat 3 (doubleX x y) =
                -2 * padicValRat 3 y := by
            have hv4 : padicValRat 3 (4 : ℚ) = 0 :=
              val_int_unit 4 (by norm_num)
            unfold doubleX
            change padicValRat 3 (nx / (4 * y ^ 2)) =
              -2 * padicValRat 3 y
            rw [padicValRat.div hnx
                (mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)),
              hvnx, padicValRat.mul (by norm_num) (pow_ne_zero 2 hy),
              hv4, padicValRat.pow y]
            ring
          have hvdy :
              padicValRat 3 (doubleY x y) =
                -3 * padicValRat 3 y := by
            have hv8 : padicValRat 3 (8 : ℚ) = 0 :=
              val_int_unit 8 (by norm_num)
            unfold doubleY
            change padicValRat 3 (ny / (8 * y ^ 3)) =
              -3 * padicValRat 3 y
            rw [padicValRat.div hny
                (mul_ne_zero (by norm_num) (pow_ne_zero 3 hy)),
              hvny, padicValRat.mul (by norm_num) (pow_ne_zero 3 hy),
              hv8, padicValRat.pow y]
            ring
          let hd := double_nonsingular hy h
          have hdouble := two_nsmul_eq_double_point hy h
          have hlevel :
              FormalLevel
                (WeierstrassCurve.Affine.Point.some
                  (doubleX x y) (doubleY x y) hd)
                (padicValRat 3 y) :=
            ⟨hvypos, hvdx, hvdy⟩
          have hformal2 : FormalAtThree
              (2 • (WeierstrassCurve.Affine.Point.some x y h :
                GoodPoint)) := by
            rw [hdouble, FormalAtThree_iff]
            exact Or.inr ⟨padicValRat 3 y, hlevel⟩
          have hformal6 := FormalAtThree_triple hformal2
          simpa only [show (6 : ℕ) = 3 * 2 by norm_num,
            mul_nsmul'] using hformal6

end

end MazurProof.XDelta19GoodFormalReduction

end

theorem solution (E : WeierstrassCurve ℚ) [E.IsElliptic] (hE : E = (⟨0, 64, 0, 1216, 5776⟩ : WeierstrassCurve ℚ))
    (P : WeierstrassCurve.Affine.Point E) :
    ((6 • P) = 0 ∨ ∃ (x y : ℚ) (h : WeierstrassCurve.Affine.Nonsingular E x y), (6 • P) = WeierstrassCurve.Affine.Point.some x y h ∧ ∃ k : ℤ, 0 < k ∧ padicValRat 3 x = -2 * k ∧ padicValRat 3 y = -3 * k) := by
  subst E
  exact (MazurProof.XDelta19GoodFormalCore.public_formal_iff (6 • P)).mp
    (MazurProof.XDelta19GoodFormalReduction.six_nsmul_formal P)
