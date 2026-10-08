-- Prove2me | solution 1 for MazurHuang.N19.good_affine_x_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-07T18:34:24.125564+00:00
-- url     : https://prove2.me/submissions/ea20b368-19dc-4a75-a853-7fda36f49622

/-
Rational points on the good conductor-nineteen model
Author: Xiang Huang. License: Apache-2.0.
Source: https://github.com/xiangyazi24/FLT/tree/51bbb4f191ad0d3753b87123635c100a638ae580
Port: Lean v4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Mathlib
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_MazurHuang_N19_good_affine_tripling_coordinates
import Theorems.Thm_MazurHuang_N19_good_three_multiple_infinitely_three_divisible
import Theorems.Thm_MazurHuang_N19_good_formal_level_triples
import Theorems.Thm_MazurHuang_N19_good_six_multiple_is_formal


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

-- Source FLT/Assumptions/MazurProof/XDelta19GoodFormalCore.lean:473-541; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodFormalCore
open MazurProof.XDelta19GoodModel MazurProof.XDelta19GoodIsogeny
noncomputable section
/-- A nonzero point has at most one exact formal level. -/
private theorem FormalLevel_unique {P : GoodPoint} {k l : ℤ}
    (hk : FormalLevel P k) (hl : FormalLevel P l) :
    k = l := by
  cases P with
  | zero => simp [FormalLevel] at hk
  | some x y h =>
      rcases hk with ⟨_, hxk, _⟩
      rcases hl with ⟨_, hxl, _⟩
      omega

/-- Multiplication by `3^n` raises a formal level by exactly `n`. -/
theorem FormalLevel_three_power {P : GoodPoint} {k : ℤ}
    (hP : FormalLevel P k) (n : ℕ) :
    ∃ k' : ℤ, k' = k + (n : ℤ) ∧
      FormalLevel ((3 ^ n : ℕ) • P) k' := by
  induction n with
  | zero =>
      exact ⟨k, by simp, by simpa using hP⟩
  | succ n ih =>
      obtain ⟨l, hl, hlevel⟩ := ih
      have hpow : (3 ^ (n + 1) : ℕ) • P =
          3 • ((3 ^ n : ℕ) • P) := by
        rw [pow_succ, mul_nsmul]
      refine ⟨l + 1, by norm_num at hl ⊢; omega, ?_⟩
      rw [hpow]
      exact FormalLevel_triple hlevel

/-- A formal point divisible through formal points by every power of
three is zero. -/
theorem formal_separated (P : GoodPoint)
    (hP : FormalAtThree P)
    (hdiv : ∀ n : ℕ, ∃ Q : GoodPoint,
      FormalAtThree Q ∧ P = (3 ^ n : ℕ) • Q) :
    P = 0 := by
  by_contra hP0
  have hlevelP : ∃ k : ℤ, FormalLevel P k := by
    rw [FormalAtThree_iff] at hP
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
    rw [FormalAtThree_iff] at hQformal
    exact hQformal.resolve_left hQ0
  obtain ⟨l, hl⟩ := hlevelQ
  obtain ⟨l', hl', hlevel⟩ := FormalLevel_three_power hl n
  have hlevelP' : FormalLevel P l' := by
    rw [hPQ]
    exact hlevel
  have heq : l' = k := FormalLevel_unique hlevelP' hk
  have hkNat : (k.toNat : ℤ) = k :=
    Int.toNat_of_nonneg (le_of_lt hkpos)
  have hncast : (n : ℤ) = k + 1 := by
    dsimp [n]
    rw [hkNat]
  have hlpos : 0 < l := by
    cases Q with
    | zero => simp [FormalLevel] at hl
    | some x y h => exact hl.1
  omega
end
end MazurProof.XDelta19GoodFormalCore
end

namespace MazurProof.XDelta19GoodFormalCore
open MazurProof.XDelta19GoodModel
/-- The weak-descent facade supplies arbitrary powers of three. -/
theorem three_nsmul_three_power_divisible (P : GoodPoint) (n : ℕ) :
    ∃ Q : GoodPoint, 3 • P = (3 ^ n : ℕ) • (3 • Q) :=
  MazurHuang.N19.good_three_multiple_infinitely_three_divisible goodCurve rfl P n
end MazurProof.XDelta19GoodFormalCore

-- Source FLT/Assumptions/MazurProof/XDelta19GoodFormalCore.lean:567-588; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section
namespace MazurProof.XDelta19GoodFormalCore
open MazurProof.XDelta19GoodModel MazurProof.XDelta19GoodIsogeny
noncomputable section
/-- Weak descent and formal entry of every `6P` imply that every rational
point is killed by six. -/
theorem six_nsmul_eq_zero
    (hentry : ∀ Q : GoodPoint, FormalAtThree (6 • Q))
    (P : GoodPoint) :
    6 • P = 0 := by
  apply formal_separated (6 • P) (hentry P)
  intro n
  obtain ⟨Q, hQ⟩ := three_nsmul_three_power_divisible P n
  refine ⟨6 • Q, hentry Q, ?_⟩
  calc
    6 • P = (2 * 3) • P := by norm_num
    _ = 2 • (3 • P) := mul_nsmul' P 2 3
    _ = 2 • ((3 ^ n : ℕ) • (3 • Q)) := by rw [hQ]
    _ = (2 * 3 ^ n) • (3 • Q) :=
      (mul_nsmul' (3 • Q) 2 (3 ^ n)).symm
    _ = (3 ^ n * 2) • (3 • Q) := by rw [Nat.mul_comm 2]
    _ = (3 ^ n : ℕ) • (2 • (3 • Q)) :=
      mul_nsmul' (3 • Q) (3 ^ n) 2
    _ = (3 ^ n : ℕ) • (6 • Q) := by
      rw [show 6 • Q = 2 • (3 • Q) by
        exact mul_nsmul' Q 2 3]
end
end MazurProof.XDelta19GoodFormalCore
end

namespace MazurProof.XDelta19GoodFormalReduction
open MazurProof.XDelta19GoodModel MazurProof.XDelta19GoodFormalCore
/-- Formal entry is supplied by the coordinate-level published statement. -/
theorem six_nsmul_formal (P : GoodPoint) : FormalAtThree (6 • P) :=
  (public_formal_iff (6 • P)).mpr (MazurHuang.N19.good_six_multiple_is_formal goodCurve rfl P)
end MazurProof.XDelta19GoodFormalReduction

-- Source FLT/Assumptions/MazurProof/XDelta19GoodRationalPoints.lean:3-99; fork 51bbb4f191ad0d3753b87123635c100a638ae580.
section

/-!
# Rational points on the good conductor-nineteen model

The two explicit three-isogeny descents give a three-coset cover of the
rational points on

`y² = x³ + (8x+76)²`.

The three-adic formal filtration then kills six times every rational point.
This curve has no rational two-torsion, so every rational point is already
killed by three.  Finally, the verified dual-forward isogeny composition
shows that an affine three-torsion point must lie in the visible kernel
`x=0`.
-/

namespace MazurProof.XDelta19GoodRationalPoints

open WeierstrassCurve.Affine
open MazurProof.XDelta19GoodModel
open MazurProof.XDelta19GoodIsogeny
open MazurProof.XDelta19GoodFormalCore
open MazurProof.XDelta19GoodFormalReduction

noncomputable section

/-! ## Elimination of rational two-torsion -/

/-- The good model has no nonzero rational point killed by two.  An affine
two-torsion point would equal its inverse, forcing its vertical coordinate
to vanish, while the good cubic has no rational root. -/
theorem eq_zero_of_two_nsmul_eq_zero
    (P : GoodPoint) (hP : 2 • P = 0) :
    P = 0 := by
  cases P with
  | zero => rfl
  | some x y h =>
      exfalso
      rw [two_nsmul] at hP
      have hself :
          (Point.some x y h : GoodPoint) = -Point.some x y h :=
        eq_neg_of_add_eq_zero_left hP
      rw [Point.neg_some, Point.some.injEq] at hself
      have hy : y = 0 := by
        have := hself.2
        simp only [WeierstrassCurve.Affine.negY, goodCurve] at this
        linarith
      have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
      exact good_y_ne_zero hcurve hy

/-! ## Exponent three and the visible kernel -/

/-- Weak three-descent, formal entry after multiplication by six, and the
absence of rational two-torsion force every rational point to be killed by
three. -/
theorem three_nsmul_eq_zero (P : GoodPoint) :
    3 • P = 0 := by
  apply eq_zero_of_two_nsmul_eq_zero (3 • P)
  calc
    2 • (3 • P) = 6 • P := by
      exact (mul_nsmul' P 2 3).symm
    _ = 0 := six_nsmul_eq_zero six_nsmul_formal P

/-- An affine rational point killed by three belongs to the visible kernel
of the forward three-isogeny, hence has first coordinate zero.  Otherwise
both isogeny maps are affine at the point, contradicting that their
composition is the point at infinity. -/
theorem x_eq_zero_of_three_nsmul
    {x y : ℚ}
    (h : WeierstrassCurve.Affine.Nonsingular goodCurve x y)
    (hthree : 3 • (Point.some x y h : GoodPoint) = 0) :
    x = 0 := by
  by_contra hx
  have hcurve : OnGood x y := (goodCurve_equation_iff x y).mp h.1
  have hforward := threeIsogenyPoint_some_of_x_ne_zero h hx
  have hforwardX := threeIsogenyX_ne_zero hx hcurve
  have hcomp := dual_comp_threeIsogenyPoint
    (Point.some x y h : GoodPoint)
  rw [hthree] at hcomp
  rw [hforward] at hcomp
  change dualThreeIsogenyPoint
      (Point.some (threeIsogenyX x) (threeIsogenyY x y) _) = 0 at hcomp
  rw [dualThreeIsogenyPoint_some_of_x_ne_zero _ hforwardX] at hcomp
  exact (Point.some_ne_zero _) hcomp

/-- Every affine rational point on the good integral model has first
coordinate zero. -/
theorem affine_x_eq_zero {x y : ℚ} (h : OnGood x y) :
    x = 0 := by
  have hns : WeierstrassCurve.Affine.Nonsingular goodCurve x y :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      ((goodCurve_equation_iff x y).mpr h)
  exact x_eq_zero_of_three_nsmul hns
    (three_nsmul_eq_zero (Point.some x y hns : GoodPoint))

end

end MazurProof.XDelta19GoodRationalPoints

end

theorem solution {x y : ℚ} (h : y ^ 2 = x ^ 3 + (8 * x + 76) ^ 2) : x = 0 := by
  exact MazurProof.XDelta19GoodRationalPoints.affine_x_eq_zero h
