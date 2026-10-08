-- Prove2me | solution 1 for MazurTransfer.x0_49_rational_points_finite
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T14:45:03.079103+00:00
-- url     : https://prove2.me/submissions/384649c4-796a-4f2d-86df-3ae36b70d416

import Mathlib
import Definitions.Def_MazurTransfer_XZeroFortyNineCurveData


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

lemma den_duplication_ne_zero_or_num_duplication_ne_zero
    {x y : F} (h : W.toAffine.Nonsingular x y) :
    4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ≠ 0 ∨
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ ≠ 0 := by
  have ⟨h₁, h₂⟩ := (W.toAffine.nonsingular_iff x y).mp h
  rw [W.toAffine.equation_iff x y] at h₁
  by_cases hzero : 2 * y + W.a₁ * x + W.a₃ = 0
  · right
    replace h₂ : W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
      grind
    contrapose! h₂
    rw [b₄, b₆, b₈] at h₂
    grobner
  · left
    clear h₂
    contrapose! hzero
    rw [b₂, b₄, b₆] at hzero
    grobner

section Decidable

variable [DecidableEq F]

lemma addX_self_of_Y_ne {x y : F} (h : W.toAffine.Equation x y)
    (hn : y ≠ W.toAffine.negY x y) :
    W.toAffine.addX x x (W.toAffine.slope x x y y) =
      (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  have aux {a b c : F} (ha : a ≠ 0) :
      a ^ 2 * (b * (c / a)) = a * b * c := by
    field
  have hn' := (den_duplication_eq_zero_iff h).not.mpr hn
  refine mul_left_cancel₀ hn' ?_
  have hn'' : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [den_duplication_eq h] at hn'
    grind
  rw [mul_div_cancel₀ _ hn', WeierstrassCurve.Affine.addX,
    sub_sub, sub_sub, mul_sub, mul_add]
  simp only [WeierstrassCurve.Affine.slope, ↓reduceIte, hn]
  rw [WeierstrassCurve.Affine.negY,
    show y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ by ring,
    div_pow]
  nth_rewrite 1 2 [den_duplication_eq h]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hn'', aux hn'', b₂, b₄, b₆, b₈]
  linear_combination -W.a₁ ^ 2 * (W.toAffine.equation_iff x y).mp h

lemma addX_of_X_ne {xP yP xQ yQ : F} (hn : xP ≠ xQ) :
    W.toAffine.addX xP xQ (W.toAffine.slope xP xQ yP yQ) =
      ((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) -
          (W.a₂ + xP + xQ) * (xP - xQ) ^ 2) /
        (xP - xQ) ^ 2 := by
  have hxPQ : xP - xQ ≠ 0 := by
    grind only
  simp [WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.slope, hn, div_pow]
  field

lemma Point.xRep_add_self_of_Y_ne {x y : F}
    (h : W.toAffine.Nonsingular x y)
    (hn : y ≠ W.toAffine.negY x y) :
    (some x y h + some x y h).xRep =
      ![(x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
          (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆), 1] := by
  simp only [add_self_of_Y_ne hn, ← addX_self_of_Y_ne h.1 hn, xRep_some]



lemma Point.xRep_add_of_X_ne {xP yP xQ yQ : F}
    (hP : W.toAffine.Nonsingular xP yP)
    (hQ : W.toAffine.Nonsingular xQ yQ)
    (hn : xP ≠ xQ) :
    (some xP yP hP + some xQ yQ hQ).xRep =
      ![((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) -
            (W.a₂ + xP + xQ) * (xP - xQ) ^ 2) /
          (xP - xQ) ^ 2, 1] := by
  simp only [add_of_X_ne (h₁ := hP) (h₂ := hQ) hn, xRep_some,
    addX_of_X_ne hn]

lemma Point.xRep_sub_of_X_ne {xP yP xQ yQ : F}
    (hP : W.toAffine.Nonsingular xP yP)
    (hQ : W.toAffine.Nonsingular xQ yQ)
    (hn : xP ≠ xQ) :
    (some xP yP hP - some xQ yQ hQ).xRep =
      ![((yP + yQ + W.a₁ * xQ + W.a₃) ^ 2 +
            W.a₁ * (yP + yQ + W.a₁ * xQ + W.a₃) * (xP - xQ) -
            (W.a₂ + xP + xQ) * (xP - xQ) ^ 2) /
          (xP - xQ) ^ 2, 1] := by
  simp only [sub_eq_add_neg (some ..), neg_some hQ,
    add_of_X_ne (h₁ := hP) (h₂ := (nonsingular_neg ..).mpr hQ) hn,
    xRep_some, addX_of_X_ne hn]
  grind only [negY]

end Decidable

lemma finite_preimage_xRep (x : F) :
    {P : W.toAffine.Point | P.xRep = ![x, 1]}.Finite := by
  rcases Set.eq_empty_or_nonempty
      {P : W.toAffine.Point | P.xRep = ![x, 1]} with h | h
  · exact h ▸ Set.finite_empty
  choose Q hQ using h
  simp only [Set.mem_setOf_eq] at hQ
  rw [show {P | P.xRep = ![x, 1]} = {Q, -Q} by
    ext
    simp [← hQ, Point.xRep_eq_xRep_iff]]
  simp

lemma finite_preimage_xRep0 (x : F) :
    {P : W.toAffine.Point | P.xRep 0 = x}.Finite := by
  have hsubset :
      {P : W.toAffine.Point | P.xRep 0 = x} ⊆
        {P | P.xRep = ![x, 1]} ∪ {0} := by
    intro P hP
    match P with
    | 0 => simp
    | .some x' y h => simp_all [Point.xRep_some]
  exact (finite_preimage_xRep x).union (Set.finite_singleton 0) |>.subset hsubset

lemma Point.sym2x_eq (P Q : W.toAffine.Point) :
    P.sym2x Q =
      ![P.xRep 0 * Q.xRep 0,
        P.xRep 0 * Q.xRep 1 + P.xRep 1 * Q.xRep 0,
        P.xRep 1 * Q.xRep 1] :=
  rfl

private lemma Point.sym2x_P_P_eq_addSubMap (P : W.toAffine.Point) :
    Point.sym2x P P =
      fun i ↦ (addSubMap W i).eval <| P.sym2x 0 := by
  match P with
  | 0 =>
    simp only [Point.sym2x_zero_zero, succ_eq_add_one, reduceAdd,
      addSubMap, Fin.isValue]
    ext i
    fin_cases i <;> simp
  | some .. =>
    simp only [Point.sym2x_some_some, succ_eq_add_one, reduceAdd,
      Point.sym2x_some_zero, addSubMap, Fin.isValue]
    ext i
    fin_cases i <;> simp [pow_two, two_mul]

section Decidable

variable [DecidableEq F]

private lemma Point.sym2x_P_add_P_zero (P : W.toAffine.Point) :
    ∃ t : F, t ≠ 0 ∧
      t • Point.sym2x (P + P) 0 =
        fun i ↦ (addSubMap W i).eval <| P.sym2x P := by
  match P with
  | 0 =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [add_zero, Point.sym2x_zero_zero, one_smul, addSubMap]
    ext i
    fin_cases i <;> simp
  | some x y h =>
    have heq := (W.toAffine.equation_iff x y).mp h.1
    have hrs :
        (fun i ↦ (addSubMap W i).eval <|
          (some x y h).sym2x (some x y h)) =
          ![x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈,
            4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆, 0] := by
      ext i
      fin_cases i <;> simp [addSubMap] <;> ring
    rw [hrs]
    by_cases hvertical : y = W.toAffine.negY x y
    · have hden := (den_duplication_eq_zero_iff h.1).mpr hvertical
      rw [hden, add_self_of_Y_eq hvertical, Point.sym2x_zero_zero]
      refine ⟨_,
        den_duplication_ne_zero_or_num_duplication_ne_zero h
          |>.neg_resolve_left hden, ?_⟩
      simp
    · have hden := (den_duplication_eq_zero_iff h.1).not.mpr hvertical
      refine ⟨_, hden, ?_⟩
      simp [Point.sym2x_eq, Point.xRep_add_self_of_Y_ne h hvertical,
        mul_div_cancel₀ _ hden]

theorem Point.sym2x_add_sub_eq_addSubMap_sym2x
    (P Q : W.toAffine.Point) :
    ∃ t : F, t ≠ 0 ∧
      t • Point.sym2x (P + Q) (P - Q) =
        fun i ↦ (addSubMap W i).eval <| Point.sym2x P Q := by
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using P.sym2x_P_add_P_zero
  rcases eq_or_ne Q (-P) with rfl | hPQ'
  · simpa [Point.sym2x_neg_right, Point.sym2x_comm 0] using
      P.sym2x_P_add_P_zero
  match P, Q with
  | P, 0 =>
    exact ⟨1, one_ne_zero, by simpa using P.sym2x_P_P_eq_addSubMap⟩
  | 0, Q =>
    refine ⟨1, one_ne_zero, ?_⟩
    simpa [Point.sym2x_neg_right, Point.sym2x_comm _ Q] using
      Q.sym2x_P_P_eq_addSubMap
  | some xP yP hP, some xQ yQ hQ =>
    have hxPQ : xP ≠ xQ := fun heq ↦ by
      grind only [X_eq_iff.mp heq]
    have hrs :
        (fun i ↦ (addSubMap W i).eval <|
          (some xP yP hP).sym2x (some xQ yQ hQ)) =
          ![(xP * xQ) ^ 2 - W.b₄ * (xP * xQ) -
              W.b₆ * (xP + xQ) - W.b₈,
            2 * (xP + xQ) * (xP * xQ) +
              W.b₂ * (xP * xQ) + W.b₄ * (xP + xQ) + W.b₆,
            (xP - xQ) ^ 2] := by
      ext i
      fin_cases i <;> simp [addSubMap]
      ring
    have hsub : xP - xQ ≠ 0 := sub_ne_zero_of_ne hxPQ
    refine ⟨(xP - xQ) ^ 2, pow_ne_zero 2 hsub, ?_⟩
    have heqP := (W.toAffine.equation_iff xP yP).mp hP.1
    have heqQ := (W.toAffine.equation_iff xQ yQ).mp hQ.1
    rw [hrs, Point.sym2x_eq, Point.xRep_add_of_X_ne hP hQ hxPQ,
      Point.xRep_sub_of_X_ne hP hQ hxPQ, b₂, b₄, b₆, b₈]
    ext i
    fin_cases i <;> simp [field] <;> grobner

end Decidable

section Height

open Height

variable [AdmissibleAbsValues F]

/-- The logarithmic projective height of an affine point's `x`-coordinates. -/
noncomputable def Point.naiveHeight (P : W.toAffine.Point) : ℝ :=
  logHeight P.xRep

lemma Point.naiveHeight_eq_logHeight (P : W.toAffine.Point) :
    P.naiveHeight = logHeight P.xRep :=
  rfl

lemma Point.naiveHeight_eq_logHeight₁ {P : W.toAffine.Point} :
    P.naiveHeight = logHeight₁ (P.xRep 0) := by
  match P with
  | 0 => simp [naiveHeight, xRep]
  | some .. =>
    simpa [naiveHeight] using (logHeight₁_eq_logHeight _).symm

variable (W)

lemma abs_logHeight_sym2x_sub_le :
    ∃ C, ∀ P Q : W.toAffine.Point,
      |logHeight (P.sym2x Q) - (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight_sym2_sub_le F
  refine ⟨C, fun P Q ↦ ?_⟩
  rw [P.naiveHeight_eq_logHeight, Q.naiveHeight_eq_logHeight,
    Point.sym2x_eq]
  have hmul := logHeight_fun_mul_eq P.xRep_ne_zero Q.xRep_ne_zero
  have hvec (v : Fin 2 → F) : ![v 0, v 1] = v := by
    ext i
    fin_cases i <;> simp
  have hzero (P : W.toAffine.Point) : ![P.xRep 0, P.xRep 1] ≠ 0 :=
    hvec P.xRep ▸ P.xRep_ne_zero
  specialize hC (hzero P) (hzero Q)
  rw [hvec P.xRep, hvec Q.xRep] at *
  grind only [= abs.eq_1, = max_def]

variable [W.toAffine.IsElliptic]

theorem approx_parallelogram_law [DecidableEq F] :
    ∃ C, ∀ P Q : W.toAffine.Point,
      |(P + Q).naiveHeight + (P - Q).naiveHeight -
          2 * (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := abs_logHeight_sym2x_sub_le W
  obtain ⟨C₂, hC₂⟩ :=
    WeierstrassCurve.abs_logHeight_addSubMap_sub_two_mul_logHeight_le W
  refine ⟨3 * C₁ + C₂, fun P Q ↦ ?_⟩
  obtain ⟨t, ht₀, ht⟩ :=
    Point.sym2x_add_sub_eq_addSubMap_sym2x P Q
  replace ht := congrArg logHeight ht
  rw [Height.logHeight_smul_eq_logHeight _ ht₀] at ht
  have hPQ := hC₁ P Q
  have haddsub := hC₁ (P + Q) (P - Q)
  have hC := ht ▸ hC₂ (P.sym2x Q)
  generalize (P + Q).naiveHeight + (P - Q).naiveHeight = A at haddsub ⊢
  generalize logHeight ((P + Q).sym2x (P - Q)) = B at hC haddsub
  generalize logHeight (P.sym2x Q) = B' at hPQ hC
  generalize P.naiveHeight + Q.naiveHeight = A' at hPQ ⊢
  grind only [= abs.eq_1, = max_def]

instance [Northcott (logHeight₁ (K := F))] :
    Northcott (Point.naiveHeight (F := F) (W := W)) := by
  eta_expand
  simp only [Point.naiveHeight_eq_logHeight₁]
  rw [← Function.comp_def]
  letI : Filter.TendstoCofinite (fun P : W.toAffine.Point ↦ P.xRep 0) :=
    (Filter.tendstoCofinite_iff_finite_preimage_singleton _).2 fun x ↦ by
      simpa only [Set.preimage, Set.mem_singleton_iff] using
        (finite_preimage_xRep0 (W := W) x)
  exact Northcott.comp_of_finite_fibers
    (h := fun P : W.toAffine.Point ↦ P.xRep 0)
    (h' := logHeight₁)

variable [Northcott (logHeight₁ (K := F))]
variable [DecidableEq F]

theorem fg_point_of_finiteIndex_two
    (hindex :
      (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range.FiniteIndex) :
    AddGroup.FG W.toAffine.Point := by
  have hnonneg (P : W.toAffine.Point) : 0 ≤ P.naiveHeight := by
    rw [Point.naiveHeight_eq_logHeight P]
    positivity
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.fg_of_descent' hindex hnonneg hC



end Height

end WeierstrassCurve.Affine

end


/- Source module: MazurTorsion.Foundations.TwoTorsion. Original headers retained. -/
section
/-
Copyright (c) 2026 Victor Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Aguiar
-/



/-!
# Rational two-torsion bounds

This file bounds the two-torsion of a Weierstrass curve in characteristic
different from two and excludes an elementary abelian subgroup of order eight.
These are elementary structural inputs to the torsion classification in
Mazur's theorem.
-/

namespace MazurTorsion

open scoped WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F) [NeZero (2 : F)]

noncomputable section

private noncomputable def twoTorsionRootMap :
    {P : (E⁄F).Point // (2 : ℕ) • P = 0} →
      Option (E.twoTorsionPolynomial.toPoly.rootSet F)
  | ⟨0, _⟩ => none
  | ⟨WeierstrassCurve.Affine.Point.some x y h, htwo⟩ => some ⟨x, by
      rw [Polynomial.mem_rootSet_of_ne]
      · simp only [Polynomial.aeval_def]
        rw [Algebra.algebraMap_self, Polynomial.eval₂_id]
        have hneg : WeierstrassCurve.Affine.Point.some x y h =
            -WeierstrassCurve.Affine.Point.some x y h := by
          rw [← add_eq_zero_iff_eq_neg]
          simpa [two_nsmul] using htwo
        have hy : y = (E⁄F).negY x y := by
          simpa only [WeierstrassCurve.Affine.Point.neg_some,
            WeierstrassCurve.Affine.Point.some.injEq, true_and] using hneg
        have heq := h.1
        rw [WeierstrassCurve.Affine.equation_iff] at heq
        simp only [WeierstrassCurve.Affine.negY] at hy
        change y = -y - E.a₁ * x - E.a₃ at hy
        change y ^ 2 + E.a₁ * x * y + E.a₃ * y =
          x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ at heq
        have hlin : 2 * y + E.a₁ * x + E.a₃ = 0 := by
          linear_combination hy
        simp only [Cubic.toPoly, WeierstrassCurve.twoTorsionPolynomial,
          Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X]
        simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄,
          WeierstrassCurve.b₆]
        linear_combination -4 * heq +
          (2 * y + E.a₁ * x + E.a₃) * hlin
      · intro hp
        have hdeg :
            E.twoTorsionPolynomial.toPoly.natDegree = 3 :=
          Cubic.natDegree_of_a_ne_zero' (by
            rw [show (4 : F) = 2 ^ 2 by norm_num]
            exact pow_ne_zero 2 (NeZero.ne (2 : F)))
        rw [hp, Polynomial.natDegree_zero] at hdeg
        omega⟩

private theorem twoTorsionRootMap_injective :
    Function.Injective (twoTorsionRootMap E) := by
  rintro ⟨P, hP⟩ ⟨Q, hQ⟩ h
  apply Subtype.ext
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | some x y hxy => simp [twoTorsionRootMap] at h
  | some x y hxy =>
      cases Q with
      | zero => simp [twoTorsionRootMap] at h
      | some x' y' hxy' =>
          simp only [twoTorsionRootMap, Option.some.injEq,
            Subtype.mk.injEq] at h
          have hxrep :
              (WeierstrassCurve.Affine.Point.some x y hxy).xRep =
                (WeierstrassCurve.Affine.Point.some x' y' hxy').xRep := by
            simp [h]
          rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxrep
            with heq | heq
          · exact heq
          · have hself :
                WeierstrassCurve.Affine.Point.some x' y' hxy' =
                  -WeierstrassCurve.Affine.Point.some x' y' hxy' := by
              rw [← add_eq_zero_iff_eq_neg]
              simpa [two_nsmul] using hQ
            rw [hself.symm] at heq
            exact heq

/-- The points killed by `2` form a finite type in characteristic different
from two. -/
theorem finite_two_torsion :
    Finite {P : (E⁄F).Point // (2 : ℕ) • P = 0} :=
  Finite.of_injective (twoTorsionRootMap E)
    (twoTorsionRootMap_injective E)



















end

end MazurTorsion

end


/- Source module: MazurTorsion.GroupTheory.IndexNSmulFG. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/



/-!
# The index of multiplication on a finitely generated abelian group

This file is a narrow port of the finitely-generated-abelian-group part of
Michael Stoll's `EllipticCurves/Mathlib/SelmerGroup.lean`, commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.

It extends `AddSubgroup.index_range_nsmul`, which treats a finite free
`ℤ`-module, to a finitely generated commutative group with torsion.  The
result will let a curve-specific two-descent turn a bound on
`E(ℚ) / 2 E(ℚ)` into a bound on the Mordell--Weil rank.
-/

/-- First-isomorphism counting: the cardinality of an additive group is the
cardinality of the kernel times the cardinality of the range of a homomorphism. -/
theorem AddMonoidHom.card_ker_mul_card_range {G H : Type*}
    [AddGroup G] [AddGroup H] (φ : G →+ H) :
    Nat.card φ.ker * Nat.card φ.range = Nat.card G := by
  rw [Nat.card_congr
      (QuotientAddGroup.quotientKerEquivRange φ).toEquiv.symm,
    mul_comm]
  exact
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker).symm

/-- On a finite additive group, the index of the range of an endomorphism
equals the cardinality of its kernel. -/
theorem AddMonoidHom.index_range_eq_card_ker {G : Type*}
    [AddGroup G] [Finite G] (φ : G →+ G) :
    φ.range.index = Nat.card φ.ker := by
  have h1 : φ.range.index * Nat.card φ.range = Nat.card G :=
    φ.range.index_mul_card
  exact
    Nat.eq_of_mul_eq_mul_right Nat.card_pos
      (h1.trans φ.card_ker_mul_card_range.symm)

/-- An additive equivalence maps the kernel of multiplication by `n` onto
the corresponding kernel. -/
lemma AddEquiv.map_ker_nsmulAddMonoidHom {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) (n : ℕ) :
    ((nsmulAddMonoidHom (α := M) n).ker).map e.toAddMonoidHom =
      (nsmulAddMonoidHom (α := N) n).ker := by
  ext x
  rw [AddSubgroup.mem_map_equiv]
  simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
  rw [← map_nsmul, EmbeddingLike.map_eq_zero_iff]

/-- Multiplication by `n` on a product has the product of the two ranges as
its range. -/
lemma nsmulAddMonoidHom_range_prod (A B : Type*)
    [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    (nsmulAddMonoidHom (α := A × B) n).range =
      ((nsmulAddMonoidHom (α := A) n).range).prod
        (nsmulAddMonoidHom (α := B) n).range := by
  ext x
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply,
    AddSubgroup.mem_prod]
  exact
    ⟨fun ⟨y, hy⟩ ↦
        ⟨⟨y.1, congrArg Prod.fst hy⟩, ⟨y.2, congrArg Prod.snd hy⟩⟩,
      fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ ⟨(a, b), Prod.ext ha hb⟩⟩

/-- Multiplication by `n` on a product has the product of the two kernels as
its kernel. -/
lemma nsmulAddMonoidHom_ker_prod (A B : Type*)
    [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    (nsmulAddMonoidHom (α := A × B) n).ker =
      ((nsmulAddMonoidHom (α := A) n).ker).prod
        (nsmulAddMonoidHom (α := B) n).ker := by
  ext x
  simp [AddMonoidHom.mem_ker, AddSubgroup.mem_prod, Prod.ext_iff]

/-- A finite module over a characteristic-zero ring has rank zero. -/
lemma Module.rank_eq_zero_of_finite (R M : Type*) [Ring R] [CharZero R]
    [AddCommGroup M] [Module R M] [Finite M] :
    Module.rank R M = 0 :=
  rank_eq_zero_iff.mpr fun x ↦
    ⟨addOrderOf x, Nat.cast_ne_zero.mpr (addOrderOf_pos x).ne',
      by
        rw [Nat.cast_smul_eq_nsmul]
        exact addOrderOf_nsmul_eq_zero x⟩

open scoped DirectSum in
open Module in
/-- The index of `nG` in a finitely generated commutative group `G` is
`n ^ rank(G)` times the cardinality of its `n`-torsion subgroup. -/
theorem AddSubgroup.index_range_nsmul_of_fg
    (G : Type*) [AddCommGroup G] [AddGroup.FG G]
    {n : ℕ} (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := G) n).range.index =
      n ^ finrank ℤ G *
        Nat.card (nsmulAddMonoidHom (α := G) n).ker := by
  obtain ⟨r, ι, fι, p, hp, e, ⟨eqv⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod G
  have hne (i : ι) : NeZero (p i ^ e i) :=
    ⟨pow_ne_zero _ (hp i).pos.ne'⟩
  have hTfin : Finite (⨁ i, ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have hidx :
      (nsmulAddMonoidHom (α := G) n).range.index =
        (nsmulAddMonoidHom
          (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).range.index := by
    simpa [AddEquiv.map_range_nsmulAddMonoidHom]
      using
        (AddSubgroup.index_map_equiv
          (nsmulAddMonoidHom (α := G) n).range eqv).symm
  have hker :
      Nat.card (nsmulAddMonoidHom (α := G) n).ker =
        Nat.card
          (nsmulAddMonoidHom
            (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).ker := by
    rw [← eqv.map_ker_nsmulAddMonoidHom n]
    exact
      Nat.card_congr
        (AddSubgroup.equivMapOfInjective _
          eqv.toAddMonoidHom eqv.injective).toEquiv
  have hrk : finrank ℤ G = r := by
    have h1 :
        Module.rank ℤ ((Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) = r := by
      set π :=
        LinearMap.fst ℤ (Fin r →₀ ℤ) (⨁ i, ZMod (p i ^ e i))
        with hπ
      have h0 : Module.rank ℤ (LinearMap.ker π) = 0 := by
        have e2 :
            LinearMap.ker π ≃ₗ[ℤ] ⨁ i, ZMod (p i ^ e i) :=
          { toFun := fun x ↦ x.1.2
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl
            invFun := fun t ↦ ⟨(0, t), rfl⟩
            left_inv := fun x ↦
              Subtype.ext (Prod.ext (x.2 : x.1.1 = 0).symm rfl)
            right_inv := fun _ ↦ rfl }
        rw [e2.rank_eq]
        exact Module.rank_eq_zero_of_finite ℤ _
      rw [← π.rank_range_add_rank_ker,
        LinearMap.range_eq_top.mpr Prod.fst_surjective, rank_top,
        rank_finsupp_self', Cardinal.mk_fin, h0, add_zero]
    have h2 :
        finrank ℤ ((Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) = r := by
      simp [Module.finrank, h1]
    rw [eqv.toIntLinearEquiv.finrank_eq]
    convert h2 using 2
  have hkerF : (nsmulAddMonoidHom (α := Fin r →₀ ℤ) n).ker = ⊥ :=
    (AddMonoidHom.ker_eq_bot_iff _).mpr
      (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hn)
  rw [hidx, hker, hrk, nsmulAddMonoidHom_range_prod,
    AddSubgroup.index_prod, AddSubgroup.index_range_nsmul,
    AddMonoidHom.index_range_eq_card_ker,
    nsmulAddMonoidHom_ker_prod,
    Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv,
    Nat.card_prod, hkerF]
  simp

end


/- Source module: MazurTorsion.NumberTheory.RatNorthcott. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Northcott's property for the rational logarithmic height

The logarithmic height of a rational number is the logarithm of the maximum of the absolute
value of its normalized numerator and its positive denominator. Consequently, a height bound
places the numerator and denominator in finite integer intervals. This file records that elementary
rational specialization of Northcott's theorem.
-/

section

namespace MazurTorsion

open Height

/-- The rational numbers of logarithmic height at most `B` form a finite set. -/
theorem finite_rat_logHeight₁_le (B : ℝ) :
    {q : ℚ | logHeight₁ q ≤ B}.Finite := by
  let N := Nat.ceil (Real.exp B)
  let encode : ℚ → ℤ × ℕ := fun q => (q.num, q.den)
  let box : Set (ℤ × ℕ) :=
    Set.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Set.Icc 0 N
  have hbox : box.Finite := by
    exact (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).prod (Set.finite_Icc 0 N)
  have himage : encode '' {q : ℚ | logHeight₁ q ≤ B} ⊆ box := by
    rintro p ⟨q, hq, rfl⟩
    have hmax_real : (max q.num.natAbs q.den : ℝ) ≤ Real.exp B := by
      apply Real.le_exp_of_log_le
      simpa only [Set.mem_setOf_eq, Rat.logHeight₁_eq_log_max, Nat.cast_max] using hq
    have hmax_cast : (max q.num.natAbs q.den : ℝ) ≤ (N : ℝ) :=
      hmax_real.trans (Nat.le_ceil (Real.exp B))
    have hmax : max q.num.natAbs q.den ≤ N := by
      exact_mod_cast hmax_cast
    have hnum : q.num.natAbs ≤ N := le_trans (le_max_left _ _) hmax
    have hden : q.den ≤ N := le_trans (le_max_right _ _) hmax
    have hnum_upper : q.num ≤ (N : ℤ) := by
      exact Int.le_natAbs.trans (Int.ofNat_le.mpr hnum)
    have hnum_lower : -(N : ℤ) ≤ q.num := by
      have hneg : -q.num ≤ (N : ℤ) :=
        Int.le_natAbs.trans (by simpa only [Int.natAbs_neg] using Int.ofNat_le.mpr hnum)
      omega
    exact ⟨⟨hnum_lower, hnum_upper⟩, ⟨Nat.zero_le _, hden⟩⟩
  refine Set.Finite.of_finite_image (hbox.subset himage) ?_
  intro q _ r _ h
  exact Rat.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- The usual logarithmic height on `ℚ` has Northcott's property. -/
instance rationalLogHeightNorthcott : Northcott (logHeight₁ (K := ℚ)) where
  finite_le := finite_rat_logHeight₁_le

end MazurTorsion

end
end


/- Source module: MazurTorsion.NumberTheory.XZeroFortyNineDescent. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The two-isogeny descent for the `X₀(49)` model

The modular curve `X₀(49)` is the conductor-`49` elliptic curve
`y² + xy = x³ - x² - 2x - 1`; completing the square and shifting gives the
model

`y² = x(x² + 21x + 112)`

used here.  The two-isogenous curve is `Y² = X(X² - 42X - 7)`.  The
original descent images are `{1, 7}`: negative classes die by positivity,
and the classes `2` and `14` die modulo eight.  The dual images are
`{1, -7}`: the classes `-1` and `7` die by a two-step seven-adic descent.
Consequently every rational point lies in one of the two cosets of
doubling represented by `0` and `(0,0)`, the group is finitely generated
of rank zero, and, since the curve has no rational point of order four and
reduction modulo three bounds the cardinality by four, the rational point
group is exactly `{0, (0,0)}`.
-/

namespace MazurTorsion.XZeroFortyNine





private lemma curve_equation_of_nonsingular
    {U V : ℚ} (hP : curve.toAffine.Nonsingular U V) :
    V ^ 2 = U * (U ^ 2 + 21 * U + 112) := by
  have heq := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  norm_num [curve] at heq
  nlinarith [heq]

/-! ## The dual squareclasses `-1` and `7` are impossible -/

private lemma seven_dvd_of_seven_dvd_sq {c : ℤ}
    (h : (7 : ℤ) ∣ c ^ 2) : (7 : ℤ) ∣ c :=
  Int.Prime.dvd_pow' (by decide) h

private lemma seven_zmod_eq_zero : ((7 : ZMod 7)) = 0 := by decide

private lemma neg_one_leaf_mod_seven :
    ∀ m c : ZMod 7, m ≠ 0 → c ^ 2 ≠ -m ^ 4 := by
  decide

/-- The primitive integral quartic for the dual squareclass `-1` has no
solution: `c² = -m⁴ - 42m²n² + 7n⁴` is impossible for coprime `m, n`. -/
private lemma no_dual_neg_one_class_int
    {m n c : ℤ} (hmn : IsCoprime m n) :
    c ^ 2 ≠ -m ^ 4 - 42 * m ^ 2 * n ^ 2 + 7 * n ^ 4 := by
  intro hc
  have hm7 : (7 : ℤ) ∣ m := by
    by_contra hm
    apply neg_one_leaf_mod_seven (m : ZMod 7) (c : ZMod 7)
      (fun hz ↦ hm ((ZMod.intCast_zmod_eq_zero_iff_dvd m 7).mp hz))
    have := congrArg (fun z : ℤ ↦ (z : ZMod 7)) hc
    push_cast at this
    linear_combination this +
      (-6 * (m : ZMod 7) ^ 2 * (n : ZMod 7) ^ 2 + (n : ZMod 7) ^ 4) *
        seven_zmod_eq_zero
  obtain ⟨μ, rfl⟩ := hm7
  have hc7 : (7 : ℤ) ∣ c := by
    apply seven_dvd_of_seven_dvd_sq
    refine ⟨-343 * μ ^ 4 - 42 * 7 * μ ^ 2 * n ^ 2 + n ^ 4, ?_⟩
    linear_combination hc
  obtain ⟨γ, rfl⟩ := hc7
  have hstep : 7 * γ ^ 2 = -343 * μ ^ 4 - 294 * μ ^ 2 * n ^ 2 + n ^ 4 := by
    have h7 : (7 : ℤ) *
        (7 * γ ^ 2 - (-343 * μ ^ 4 - 294 * μ ^ 2 * n ^ 2 + n ^ 4)) = 0 := by
      linear_combination hc
    rcases mul_eq_zero.mp h7 with h | h
    · norm_num at h
    · linarith
  have hn7 : (7 : ℤ) ∣ n := by
    have h4 : (7 : ℤ) ∣ n ^ 4 := by
      refine ⟨γ ^ 2 + 49 * μ ^ 4 + 42 * μ ^ 2 * n ^ 2, ?_⟩
      linear_combination -hstep
    exact seven_dvd_of_seven_dvd_sq
      (seven_dvd_of_seven_dvd_sq (by simpa [pow_succ, pow_two] using
        (by rwa [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul] at h4 :
          (7 : ℤ) ∣ (n ^ 2) ^ 2)))
  have : IsUnit (7 : ℤ) := hmn.isUnit_of_dvd' ⟨μ, rfl⟩ hn7
  norm_num [Int.isUnit_iff] at this

/-- The primitive integral quartic for the dual squareclass `7` has no
solution: `c² = 7m⁴ - 42m²n² - n⁴` is impossible for coprime `m, n`. -/
private lemma no_dual_seven_class_int
    {m n c : ℤ} (hmn : IsCoprime m n) :
    c ^ 2 ≠ 7 * m ^ 4 - 42 * m ^ 2 * n ^ 2 - n ^ 4 := by
  intro hc
  have hn7 : (7 : ℤ) ∣ n := by
    by_contra hn
    apply neg_one_leaf_mod_seven (n : ZMod 7) (c : ZMod 7)
      (fun hz ↦ hn ((ZMod.intCast_zmod_eq_zero_iff_dvd n 7).mp hz))
    have := congrArg (fun z : ℤ ↦ (z : ZMod 7)) hc
    push_cast at this
    linear_combination this +
      ((m : ZMod 7) ^ 4 - 6 * (m : ZMod 7) ^ 2 * (n : ZMod 7) ^ 2) *
        seven_zmod_eq_zero
  obtain ⟨ν, rfl⟩ := hn7
  have hc7 : (7 : ℤ) ∣ c := by
    apply seven_dvd_of_seven_dvd_sq
    refine ⟨m ^ 4 - 42 * 7 * m ^ 2 * ν ^ 2 - 343 * ν ^ 4, ?_⟩
    linear_combination hc
  obtain ⟨γ, rfl⟩ := hc7
  have hstep : 7 * γ ^ 2 = m ^ 4 - 294 * m ^ 2 * ν ^ 2 - 343 * ν ^ 4 := by
    have h7 : (7 : ℤ) *
        (7 * γ ^ 2 - (m ^ 4 - 294 * m ^ 2 * ν ^ 2 - 343 * ν ^ 4)) = 0 := by
      linear_combination hc
    rcases mul_eq_zero.mp h7 with h | h
    · norm_num at h
    · linarith
  have hm7 : (7 : ℤ) ∣ m := by
    have h4 : (7 : ℤ) ∣ m ^ 4 := by
      refine ⟨γ ^ 2 + 42 * m ^ 2 * ν ^ 2 + 49 * ν ^ 4, ?_⟩
      linear_combination -hstep
    exact seven_dvd_of_seven_dvd_sq
      (seven_dvd_of_seven_dvd_sq (by simpa [pow_succ, pow_two] using
        (by rwa [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul] at h4 :
          (7 : ℤ) ∣ (m ^ 2) ^ 2)))
  have : IsUnit (7 : ℤ) := hmn.isUnit_of_dvd' hm7 ⟨ν, rfl⟩
  norm_num [Int.isUnit_iff] at this

/-- Rational form of the dual `-1` obstruction. -/
private lemma no_dual_neg_one_class_rat (z q : ℚ) :
    q ^ 2 ≠ -z ^ 4 - 42 * z ^ 2 + 7 := by
  intro hq
  let m : ℤ := z.num
  let n : ℤ := z.den
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast z.den_ne_zero
  have hz : z = (m : ℚ) / (n : ℚ) := z.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den z
  have hscaled :
      (q * (n : ℚ) ^ 2) ^ 2 =
        ((-m ^ 4 - 42 * m ^ 2 * n ^ 2 + 7 * n ^ 4 : ℤ) : ℚ) := by
    rw [hz] at hq
    push_cast
    field_simp at hq
    linear_combination hq
  have hsq :
      IsSquare ((-m ^ 4 - 42 * m ^ 2 * n ^ 2 + 7 * n ^ 4 : ℤ) : ℚ) :=
    ⟨q * (n : ℚ) ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨c, hcint⟩ := Rat.isSquare_intCast_iff.mp hsq
  exact no_dual_neg_one_class_int hmn
    (by simpa [pow_two] using hcint.symm)

/-- Rational form of the dual `7` obstruction. -/
private lemma no_dual_seven_class_rat (z q : ℚ) :
    q ^ 2 ≠ 7 * z ^ 4 - 42 * z ^ 2 - 1 := by
  intro hq
  let m : ℤ := z.num
  let n : ℤ := z.den
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast z.den_ne_zero
  have hz : z = (m : ℚ) / (n : ℚ) := z.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den z
  have hscaled :
      (q * (n : ℚ) ^ 2) ^ 2 =
        ((7 * m ^ 4 - 42 * m ^ 2 * n ^ 2 - n ^ 4 : ℤ) : ℚ) := by
    rw [hz] at hq
    push_cast
    field_simp at hq
    linear_combination hq
  have hsq :
      IsSquare ((7 * m ^ 4 - 42 * m ^ 2 * n ^ 2 - n ^ 4 : ℤ) : ℚ) :=
    ⟨q * (n : ℚ) ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨c, hcint⟩ := Rat.isSquare_intCast_iff.mp hsq
  exact no_dual_seven_class_int hmn
    (by simpa [pow_two] using hcint.symm)

/-! ## Dual abscissas have squareclass `1` or `-7` -/

private lemma common_divisor_dual_dvd_seven
    {m n d : ℤ} (hmn : IsCoprime m n)
    (hA : d ∣ m * n)
    (hB : d ∣ m ^ 2 - 42 * m * n - 7 * n ^ 2) :
    d ∣ 7 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hm3 : d ∣ m ^ 3 := by
    refine ⟨m * b + (42 * m + 7 * n) * a, ?_⟩
    linear_combination m * hb + (42 * m + 7 * n) * ha
  have h7n3 : d ∣ 7 * n ^ 3 := by
    refine ⟨-(n * b) + (m - 42 * n) * a, ?_⟩
    linear_combination -(n * hb) + (m - 42 * n) * ha
  have hd_coprime_n3 : IsCoprime d (n ^ 3) :=
    hmn.pow.of_isCoprime_of_dvd_left hm3
  exact hd_coprime_n3.dvd_of_dvd_mul_right
    (by simpa [mul_comm] using h7n3)

private lemma squareclass_of_gcd_dvd_seven
    {A B C : ℤ} (hA : A ≠ 0) (hAB : A * B = C ^ 2)
    (hgcd : GCDMonoid.gcd A B ∣ (7 : ℤ)) :
    ∃ z : ℤ,
      A = z ^ 2 ∨ A = -z ^ 2 ∨ A = 7 * z ^ 2 ∨ A = -(7 * z ^ 2) := by
  let g : ℤ := GCDMonoid.gcd A B
  have hgA : g ∣ A := GCDMonoid.gcd_dvd_left A B
  have hgB : g ∣ B := GCDMonoid.gcd_dvd_right A B
  have hg0 : g ≠ 0 := by
    intro hz
    rw [hz] at hgA
    exact hA (zero_dvd_iff.mp hgA)
  have hgpos : 0 < g :=
    lt_of_le_of_ne (Int.gcd_nonneg A B) (Ne.symm hg0)
  have hgC : g ∣ C := by
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd
      (R := ℤ) (n := 2) (by norm_num)).mp
    simpa [pow_two, hAB] using mul_dvd_mul hgA hgB
  let a : ℤ := A / g
  let b : ℤ := B / g
  let c : ℤ := C / g
  have hga : g * a = A :=
    EuclideanDomain.mul_div_cancel' hg0 hgA
  have hgb : g * b = B :=
    EuclideanDomain.mul_div_cancel' hg0 hgB
  have hgc : g * c = C :=
    EuclideanDomain.mul_div_cancel' hg0 hgC
  have hab : a * b = c ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
    calc
      g ^ 2 * (a * b) = A * B := by rw [← hga, ← hgb]; ring
      _ = C ^ 2 := hAB
      _ = g ^ 2 * c ^ 2 := by rw [← hgc]; ring
  have habcop : IsCoprime a b :=
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0
  have hdivNat : g.natAbs ∣ 7 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hgcd
  have hgleNat : g.natAbs ≤ 7 := Nat.le_of_dvd (by norm_num) hdivNat
  have hgle : g ≤ 7 := by
    have : (g.natAbs : ℤ) ≤ 7 := by exact_mod_cast hgleNat
    simpa [Int.natCast_natAbs, abs_of_pos hgpos] using this
  have hgval : g = 1 ∨ g = 7 := by
    interval_cases g <;> norm_num at hdivNat
    all_goals simp
  obtain ⟨z, hz | hz⟩ := Int.sq_of_isCoprime habcop hab
  · have hAz : A = g * z ^ 2 := by rw [← hga, hz]
    rcases hgval with hg | hg
    · exact ⟨z, Or.inl (by rw [hAz, hg]; ring)⟩
    · exact ⟨z, Or.inr (Or.inr (Or.inl (by rw [hAz, hg])))⟩
  · have hAz : A = -(g * z ^ 2) := by rw [← hga, hz]; ring
    rcases hgval with hg | hg
    · exact ⟨z, Or.inr (Or.inl (by rw [hAz, hg]; ring))⟩
    · exact ⟨z, Or.inr (Or.inr (Or.inr (by rw [hAz, hg])))⟩

/-- On the dual curve `Y² = X(X² - 42X - 7)`, every nonzero rational
abscissa is a square or `-7` times a square. -/
theorem dual_abscissa_isSquare_or_negSeven
    {X Y : ℚ} (hX0 : X ≠ 0)
    (hdual : Y ^ 2 = X * (X ^ 2 - 42 * X - 7)) :
    IsSquare X ∨ ∃ z : ℚ, X = -(7 * z ^ 2) := by
  let m : ℤ := X.num
  let n : ℤ := X.den
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast X.den_ne_zero
  have hX : X = (m : ℚ) / (n : ℚ) := X.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den X
  have hm0 : m ≠ 0 := by
    dsimp [m]
    exact Rat.num_ne_zero.mpr hX0
  have hscaled :
      (Y * (n : ℚ) ^ 2) ^ 2 =
        (((m * n) * (m ^ 2 - 42 * m * n - 7 * n ^ 2) : ℤ) : ℚ) := by
    rw [hX] at hdual
    push_cast
    field_simp at hdual
    linear_combination (n : ℚ) * hdual
  have hsq :
      IsSquare
        (((m * n) * (m ^ 2 - 42 * m * n - 7 * n ^ 2) : ℤ) : ℚ) :=
    ⟨Y * (n : ℚ) ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨C, hC⟩ := Rat.isSquare_intCast_iff.mp hsq
  have hAB : (m * n) * (m ^ 2 - 42 * m * n - 7 * n ^ 2) = C ^ 2 := by
    simpa [pow_two] using hC
  have hA0 : m * n ≠ 0 := by
    apply mul_ne_zero hm0
    dsimp [n]
    exact_mod_cast X.den_ne_zero
  have hgcd :
      GCDMonoid.gcd (m * n) (m ^ 2 - 42 * m * n - 7 * n ^ 2) ∣
        (7 : ℤ) :=
    common_divisor_dual_dvd_seven hmn
      (GCDMonoid.gcd_dvd_left _ _)
      (GCDMonoid.gcd_dvd_right _ _)
  have lift :
      ∀ {dd z : ℤ}, m * n = dd * z ^ 2 →
        X = (dd : ℚ) * ((z : ℚ) / n) ^ 2 := by
    intro dd z hd
    rw [hX]
    field_simp
    exact_mod_cast hd
  obtain ⟨z, hz | hz | hz | hz⟩ :=
    squareclass_of_gcd_dvd_seven hA0 hAB hgcd
  · -- squareclass 1
    left
    refine ⟨(z : ℚ) / n, ?_⟩
    have := lift (dd := 1) (by simpa using hz)
    rw [this]
    ring
  · -- squareclass -1 dies by the seven-adic quartic
    exfalso
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
      exact hA0 (mul_eq_zero.mpr hz)
    have hXval : X = -((z : ℚ) / n) ^ 2 :=
      by simpa using lift (dd := -1) (by linarith [hz])
    have hr0 : ((z : ℚ) / n) ≠ 0 :=
      div_ne_zero (by exact_mod_cast hz0) hn0
    set r : ℚ := (z : ℚ) / n with hrdef
    have hq : (Y / r) ^ 2 = -r ^ 4 - 42 * r ^ 2 + 7 := by
      rw [div_pow]
      rw [hXval] at hdual
      field_simp [hr0]
      linear_combination hdual
    exact no_dual_neg_one_class_rat r (Y / r) hq
  · -- squareclass 7 dies by the seven-adic quartic
    exfalso
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
      exact hA0 (mul_eq_zero.mpr hz)
    have hXval : X = 7 * ((z : ℚ) / n) ^ 2 := lift hz
    have hr0 : ((z : ℚ) / n) ≠ 0 :=
      div_ne_zero (by exact_mod_cast hz0) hn0
    set r : ℚ := (z : ℚ) / n with hrdef
    have hq : (Y / (7 * r)) ^ 2 = 7 * r ^ 4 - 42 * r ^ 2 - 1 := by
      rw [div_pow]
      rw [hXval] at hdual
      field_simp [hr0]
      linear_combination hdual
    exact no_dual_seven_class_rat r (Y / (7 * r)) hq
  · -- squareclass -7
    right
    refine ⟨(z : ℚ) / n, ?_⟩
    have := lift (dd := -7) (by linarith [hz])
    rw [this]
    ring

/-! ## Curve abscissas have squareclass `1`, `2`, `7`, or `14` -/

private abbrev reduceTwoOfEight : ZMod 8 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)

private lemma intCast_reduceTwoOfEight_ne_zero
    {m : ℤ} (hm : ¬ (2 : ℤ) ∣ m) :
    reduceTwoOfEight (m : ZMod 8) ≠ 0 := by
  intro h
  apply hm
  have : ((m : ZMod 2) : ZMod 2) = 0 := by
    simpa [reduceTwoOfEight] using h
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at this

private lemma two_dvd_of_two_dvd_sq {c : ℤ} (h : (2 : ℤ) ∣ c ^ 2) :
    (2 : ℤ) ∣ c :=
  Int.Prime.dvd_pow' (by decide) h

private lemma two_class_leaf_one :
    ∀ m n c : ZMod 8, reduceTwoOfEight m ≠ 0 →
      c ^ 2 ≠ 2 * m ^ 4 + 21 * m ^ 2 * n ^ 2 + 56 * n ^ 4 := by
  decide

private lemma two_class_leaf_two :
    ∀ μ n c : ZMod 8, reduceTwoOfEight n ≠ 0 →
      c ^ 2 ≠ 8 * μ ^ 4 + 21 * μ ^ 2 * n ^ 2 + 14 * n ^ 4 := by
  decide

/-- The primitive integral quartic for the curve squareclass `2` has no
solution. -/
private lemma no_curve_two_class_int
    {m n c : ℤ} (hmn : IsCoprime m n) :
    c ^ 2 ≠ 2 * m ^ 4 + 21 * m ^ 2 * n ^ 2 + 56 * n ^ 4 := by
  intro hc
  have hm2 : (2 : ℤ) ∣ m := by
    by_contra hm
    apply two_class_leaf_one (m : ZMod 8) (n : ZMod 8) (c : ZMod 8)
      (intCast_reduceTwoOfEight_ne_zero hm)
    have := congrArg (fun z : ℤ ↦ (z : ZMod 8)) hc
    push_cast at this
    linear_combination this
  obtain ⟨μ, rfl⟩ := hm2
  have hn2 : ¬ (2 : ℤ) ∣ n := by
    intro hn
    have : IsUnit (2 : ℤ) := hmn.isUnit_of_dvd' ⟨μ, rfl⟩ hn
    norm_num [Int.isUnit_iff] at this
  have hc2 : (2 : ℤ) ∣ c := by
    apply two_dvd_of_two_dvd_sq
    refine ⟨16 * μ ^ 4 + 42 * μ ^ 2 * n ^ 2 + 28 * n ^ 4, ?_⟩
    linear_combination hc
  obtain ⟨γ, rfl⟩ := hc2
  have hstep : γ ^ 2 = 8 * μ ^ 4 + 21 * μ ^ 2 * n ^ 2 + 14 * n ^ 4 := by
    have h4 : (4 : ℤ) *
        (γ ^ 2 - (8 * μ ^ 4 + 21 * μ ^ 2 * n ^ 2 + 14 * n ^ 4)) = 0 := by
      linear_combination hc
    rcases mul_eq_zero.mp h4 with h | h
    · norm_num at h
    · linarith
  apply two_class_leaf_two (μ : ZMod 8) (n : ZMod 8) (γ : ZMod 8)
    (intCast_reduceTwoOfEight_ne_zero hn2)
  have := congrArg (fun z : ℤ ↦ (z : ZMod 8)) hstep
  push_cast at this
  linear_combination this

private lemma fourteen_class_leaf_one :
    ∀ m n c : ZMod 8, reduceTwoOfEight m ≠ 0 →
      c ^ 2 ≠ 14 * m ^ 4 + 21 * m ^ 2 * n ^ 2 + 8 * n ^ 4 := by
  decide

private lemma fourteen_class_leaf_two :
    ∀ μ n c : ZMod 8, reduceTwoOfEight n ≠ 0 →
      c ^ 2 ≠ 56 * μ ^ 4 + 21 * μ ^ 2 * n ^ 2 + 2 * n ^ 4 := by
  decide

/-- The primitive integral quartic for the curve squareclass `14` has no
solution. -/
private lemma no_curve_fourteen_class_int
    {m n c : ℤ} (hmn : IsCoprime m n) :
    c ^ 2 ≠ 14 * m ^ 4 + 21 * m ^ 2 * n ^ 2 + 8 * n ^ 4 := by
  intro hc
  have hm2 : (2 : ℤ) ∣ m := by
    by_contra hm
    apply fourteen_class_leaf_one (m : ZMod 8) (n : ZMod 8) (c : ZMod 8)
      (intCast_reduceTwoOfEight_ne_zero hm)
    have := congrArg (fun z : ℤ ↦ (z : ZMod 8)) hc
    push_cast at this
    linear_combination this
  obtain ⟨μ, rfl⟩ := hm2
  have hn2 : ¬ (2 : ℤ) ∣ n := by
    intro hn
    have : IsUnit (2 : ℤ) := hmn.isUnit_of_dvd' ⟨μ, rfl⟩ hn
    norm_num [Int.isUnit_iff] at this
  have hc2 : (2 : ℤ) ∣ c := by
    apply two_dvd_of_two_dvd_sq
    refine ⟨112 * μ ^ 4 + 42 * μ ^ 2 * n ^ 2 + 4 * n ^ 4, ?_⟩
    linear_combination hc
  obtain ⟨γ, rfl⟩ := hc2
  have hstep : γ ^ 2 = 56 * μ ^ 4 + 21 * μ ^ 2 * n ^ 2 + 2 * n ^ 4 := by
    have h4 : (4 : ℤ) *
        (γ ^ 2 - (56 * μ ^ 4 + 21 * μ ^ 2 * n ^ 2 + 2 * n ^ 4)) = 0 := by
      linear_combination hc
    rcases mul_eq_zero.mp h4 with h | h
    · norm_num at h
    · linarith
  apply fourteen_class_leaf_two (μ : ZMod 8) (n : ZMod 8) (γ : ZMod 8)
    (intCast_reduceTwoOfEight_ne_zero hn2)
  have := congrArg (fun z : ℤ ↦ (z : ZMod 8)) hstep
  push_cast at this
  linear_combination this

/-- Rational form of the curve `2` obstruction. -/
private lemma no_curve_two_class_rat (z q : ℚ) :
    q ^ 2 ≠ 2 * z ^ 4 + 21 * z ^ 2 + 56 := by
  intro hq
  let m : ℤ := z.num
  let n : ℤ := z.den
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast z.den_ne_zero
  have hz : z = (m : ℚ) / (n : ℚ) := z.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den z
  have hscaled :
      (q * (n : ℚ) ^ 2) ^ 2 =
        ((2 * m ^ 4 + 21 * m ^ 2 * n ^ 2 + 56 * n ^ 4 : ℤ) : ℚ) := by
    rw [hz] at hq
    push_cast
    field_simp at hq
    linear_combination hq
  have hsq :
      IsSquare ((2 * m ^ 4 + 21 * m ^ 2 * n ^ 2 + 56 * n ^ 4 : ℤ) : ℚ) :=
    ⟨q * (n : ℚ) ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨c, hcint⟩ := Rat.isSquare_intCast_iff.mp hsq
  exact no_curve_two_class_int hmn
    (by simpa [pow_two] using hcint.symm)

/-- Rational form of the curve `14` obstruction. -/
private lemma no_curve_fourteen_class_rat (z q : ℚ) :
    q ^ 2 ≠ 14 * z ^ 4 + 21 * z ^ 2 + 8 := by
  intro hq
  let m : ℤ := z.num
  let n : ℤ := z.den
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast z.den_ne_zero
  have hz : z = (m : ℚ) / (n : ℚ) := z.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den z
  have hscaled :
      (q * (n : ℚ) ^ 2) ^ 2 =
        ((14 * m ^ 4 + 21 * m ^ 2 * n ^ 2 + 8 * n ^ 4 : ℤ) : ℚ) := by
    rw [hz] at hq
    push_cast
    field_simp at hq
    linear_combination hq
  have hsq :
      IsSquare ((14 * m ^ 4 + 21 * m ^ 2 * n ^ 2 + 8 * n ^ 4 : ℤ) : ℚ) :=
    ⟨q * (n : ℚ) ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨c, hcint⟩ := Rat.isSquare_intCast_iff.mp hsq
  exact no_curve_fourteen_class_int hmn
    (by simpa [pow_two] using hcint.symm)

private lemma common_divisor_curve_dvd_112
    {m n d : ℤ} (hmn : IsCoprime m n)
    (hA : d ∣ m * n)
    (hB : d ∣ m ^ 2 + 21 * m * n + 112 * n ^ 2) :
    d ∣ 112 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hm3 : d ∣ m ^ 3 := by
    refine ⟨m * b - (21 * m + 112 * n) * a, ?_⟩
    linear_combination m * hb - (21 * m + 112 * n) * ha
  have h112n3 : d ∣ 112 * n ^ 3 := by
    refine ⟨n * b - (m + 21 * n) * a, ?_⟩
    linear_combination n * hb - (m + 21 * n) * ha
  have hd_coprime_n3 : IsCoprime d (n ^ 3) :=
    hmn.pow.of_isCoprime_of_dvd_left hm3
  exact hd_coprime_n3.dvd_of_dvd_mul_right
    (by simpa [mul_comm] using h112n3)

private lemma positive_squareclass_of_gcd_dvd_112
    {A B C : ℤ} (hApos : 0 < A) (hprod : A * B = C ^ 2)
    (hgcd : GCDMonoid.gcd A B ∣ (112 : ℤ)) :
    ∃ z : ℤ,
      A = z ^ 2 ∨ A = 2 * z ^ 2 ∨ A = 7 * z ^ 2 ∨ A = 14 * z ^ 2 := by
  let g : ℤ := GCDMonoid.gcd A B
  have hgA : g ∣ A := GCDMonoid.gcd_dvd_left A B
  have hgB : g ∣ B := GCDMonoid.gcd_dvd_right A B
  have hg0 : g ≠ 0 := by
    intro hg
    rw [hg] at hgA
    exact hApos.ne' (zero_dvd_iff.mp hgA)
  have hgpos : 0 < g :=
    lt_of_le_of_ne (Int.gcd_nonneg A B) (Ne.symm hg0)
  have hgC : g ∣ C := by
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd
      (R := ℤ) (n := 2) (by norm_num)).mp
    simpa [pow_two, hprod] using mul_dvd_mul hgA hgB
  let a : ℤ := A / g
  let b : ℤ := B / g
  let c : ℤ := C / g
  have hga : g * a = A :=
    EuclideanDomain.mul_div_cancel' hg0 hgA
  have hgb : g * b = B :=
    EuclideanDomain.mul_div_cancel' hg0 hgB
  have hgc : g * c = C :=
    EuclideanDomain.mul_div_cancel' hg0 hgC
  have hab : a * b = c ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
    calc
      g ^ 2 * (a * b) = A * B := by rw [← hga, ← hgb]; ring
      _ = C ^ 2 := hprod
      _ = g ^ 2 * c ^ 2 := by rw [← hgc]; ring
  have habcop : IsCoprime a b :=
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0
  have hgabs : g.natAbs ∣ 112 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hgcd
  have hgleNat : g.natAbs ≤ 112 := Nat.le_of_dvd (by norm_num) hgabs
  have hgle : g ≤ 112 := by
    have : (g.natAbs : ℤ) ≤ 112 := by exact_mod_cast hgleNat
    simpa [Int.natCast_natAbs, abs_of_pos hgpos] using this
  obtain ⟨z, hz | hz⟩ := Int.sq_of_isCoprime habcop hab
  · have hAz : A = g * z ^ 2 := by rw [← hga, hz]
    have hgvals :
        g = 1 ∨ g = 2 ∨ g = 4 ∨ g = 7 ∨ g = 8 ∨ g = 14 ∨
          g = 16 ∨ g = 28 ∨ g = 56 ∨ g = 112 := by
      interval_cases g <;> norm_num at hgabs
      all_goals simp
    rcases hgvals with hg | hg | hg | hg | hg | hg | hg | hg | hg | hg
    · exact ⟨z, Or.inl (by rw [hAz, hg]; ring)⟩
    · exact ⟨z, Or.inr (Or.inl (by rw [hAz, hg]))⟩
    · exact ⟨2 * z, Or.inl (by rw [hAz, hg]; ring)⟩
    · exact ⟨z, Or.inr (Or.inr (Or.inl (by rw [hAz, hg])))⟩
    · exact ⟨2 * z, Or.inr (Or.inl (by rw [hAz, hg]; ring))⟩
    · exact ⟨z, Or.inr (Or.inr (Or.inr (by rw [hAz, hg])))⟩
    · exact ⟨4 * z, Or.inl (by rw [hAz, hg]; ring)⟩
    · exact ⟨2 * z, Or.inr (Or.inr (Or.inl (by rw [hAz, hg]; ring)))⟩
    · exact ⟨2 * z, Or.inr (Or.inr (Or.inr (by rw [hAz, hg]; ring)))⟩
    · exact ⟨4 * z, Or.inr (Or.inr (Or.inl (by rw [hAz, hg]; ring)))⟩
  · exfalso
    have haNonpos : a ≤ 0 := by nlinarith [sq_nonneg z]
    have hAnonpos : A ≤ 0 := by
      rw [← hga]
      exact mul_nonpos_of_nonneg_of_nonpos hgpos.le haNonpos
    exact absurd hApos (not_lt_of_ge hAnonpos)

/-- Every nonzero abscissa on the `X₀(49)` model is a square or seven
times a square. -/
theorem curve_abscissa_isSquare_or_seven
    {U V : ℚ} (hU0 : U ≠ 0)
    (hcurve : V ^ 2 = U * (U ^ 2 + 21 * U + 112)) :
    IsSquare U ∨ ∃ z : ℚ, U = 7 * z ^ 2 := by
  have hquadratic : 0 < U ^ 2 + 21 * U + 112 := by
    nlinarith [sq_nonneg (2 * U + 21)]
  have hUpos : 0 < U := by
    rcases lt_or_gt_of_ne hU0 with hneg | hpos
    · exfalso
      nlinarith [sq_nonneg V]
    · exact hpos
  let m : ℤ := U.num
  let n : ℤ := U.den
  let A : ℤ := m * n
  let B : ℤ := m ^ 2 + 21 * m * n + 112 * n ^ 2
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast U.den_pos
  have hn0 : (n : ℚ) ≠ 0 := by positivity
  have hU : U = (m : ℚ) / n := U.num_div_den.symm
  have hscaled :
      (V * n ^ 2) ^ 2 = (((A * B : ℤ) : ℚ)) := by
    rw [hU] at hcurve
    field_simp [hn0] at hcurve
    calc
      (V * n ^ 2) ^ 2 = V ^ 2 * n ^ 4 := by ring
      _ = (m : ℚ) * n *
          ((m : ℚ) ^ 2 + 21 * m * n + 112 * n ^ 2) := by
        linear_combination n * hcurve
      _ = (((A * B : ℤ) : ℚ)) := by
        dsimp [A, B]
        push_cast
        ring
  have hsqAB : IsSquare (((A * B : ℤ) : ℚ)) :=
    ⟨V * n ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨C, hC⟩ := Rat.isSquare_intCast_iff.mp hsqAB
  have hprod : A * B = C ^ 2 := by
    simpa [pow_two] using hC
  have hApos : 0 < A := by
    have hmpos : 0 < m := by
      dsimp [m]
      exact Rat.num_pos.mpr hUpos
    exact mul_pos hmpos hnpos
  have hmnCoprime : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den U
  have hgcd : GCDMonoid.gcd A B ∣ (112 : ℤ) :=
    common_divisor_curve_dvd_112 hmnCoprime
      (GCDMonoid.gcd_dvd_left A B) (GCDMonoid.gcd_dvd_right A B)
  obtain ⟨z, hA | hA | hA | hA⟩ :=
    positive_squareclass_of_gcd_dvd_112 hApos hprod hgcd
  · left
    refine ⟨(z : ℚ) / n, ?_⟩
    rw [hU]
    simp only [A] at hA
    field_simp [hn0]
    exact_mod_cast hA
  · -- squareclass 2 dies
    exfalso
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hA
      norm_num at hA
      exact absurd hA (by
        simp only [A]
        exact mul_ne_zero (by dsimp [m]; exact Rat.num_ne_zero.mpr hU0)
          (by omega))
    have hUval : U = 2 * ((z : ℚ) / n) ^ 2 := by
      rw [hU]
      simp only [A] at hA
      field_simp [hn0]
      exact_mod_cast hA
    have hr0 : ((z : ℚ) / n) ≠ 0 :=
      div_ne_zero (by exact_mod_cast hz0) hn0
    set r : ℚ := (z : ℚ) / n with hrdef
    have hq : (V / (2 * r)) ^ 2 = 2 * r ^ 4 + 21 * r ^ 2 + 56 := by
      rw [div_pow]
      rw [hUval] at hcurve
      field_simp [hr0]
      linear_combination hcurve
    exact no_curve_two_class_rat r (V / (2 * r)) hq
  · right
    refine ⟨(z : ℚ) / n, ?_⟩
    rw [hU]
    simp only [A] at hA
    field_simp [hn0]
    exact_mod_cast hA
  · -- squareclass 14 dies
    exfalso
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hA
      norm_num at hA
      exact absurd hA (by
        simp only [A]
        exact mul_ne_zero (by dsimp [m]; exact Rat.num_ne_zero.mpr hU0)
          (by omega))
    have hUval : U = 14 * ((z : ℚ) / n) ^ 2 := by
      rw [hU]
      simp only [A] at hA
      field_simp [hn0]
      exact_mod_cast hA
    have hr0 : ((z : ℚ) / n) ≠ 0 :=
      div_ne_zero (by exact_mod_cast hz0) hn0
    set r : ℚ := (z : ℚ) / n with hrdef
    have hq : (V / (14 * r)) ^ 2 = 14 * r ^ 4 + 21 * r ^ 2 + 8 := by
      rw [div_pow]
      rw [hUval] at hcurve
      field_simp [hr0]
      linear_combination hcurve
    exact no_curve_fourteen_class_rat r (V / (14 * r)) hq

/-! ## Reverse doubling from a square abscissa -/

private lemma y_linear_of_reverse_definition
    {X Y q v : ℚ} (hq0 : q ≠ 0)
    (hv : v = -21 / 2 + X / 2 - Y / (2 * q)) :
    Y = q * (X - 21 - 2 * v) := by
  field_simp [hq0] at hv
  linear_combination hv

private lemma y_formula_of_reverse_linear
    {X Y q v : ℚ} (hv0 : v ≠ 0)
    (hlinear : Y = q * (X - 21 - 2 * v))
    (hXv : X * v = v ^ 2 + 21 * v + 112) :
    Y = -q * (v ^ 2 - 112) / v := by
  rw [hlinear]
  field_simp [hv0]
  linear_combination q * hXv

private lemma y_formula_squared
    {Y q v : ℚ} (hv0 : v ≠ 0)
    (hY : Y = -q * (v ^ 2 - 112) / v) :
    Y ^ 2 * v ^ 2 = q ^ 2 * (v ^ 2 - 112) ^ 2 := by
  rw [hY]
  field_simp [hv0]

/-- A nonzero rational point whose abscissa is a square is divisible by
two.  If the first auxiliary dual abscissa has squareclass `-7`, its
conjugate (their product is `-7`) is a square and gives the same doubling
abscissa. -/
theorem double_of_square_abscissa
    {U V : ℚ} (hU0 : U ≠ 0)
    (hP : curve.toAffine.Nonsingular U V)
    (hUSquare : IsSquare U) :
    ∃ Q : curve.toAffine.Point,
      (2 : ℕ) • Q =
        WeierstrassCurve.Affine.Point.some U V hP := by
  obtain ⟨s, hs⟩ := hUSquare
  have hU : U = s ^ 2 := by
    simpa [pow_two] using hs
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz] at hU
    norm_num at hU
    exact hU0 hU
  have hcurve : V ^ 2 = U * (U ^ 2 + 21 * U + 112) :=
    curve_equation_of_nonsingular hP
  let t : ℚ := V / s
  have ht : t ^ 2 = U ^ 2 + 21 * U + 112 := by
    dsimp [t]
    rw [div_pow]
    field_simp [hs0]
    nlinarith [hcurve, hU]
  let X₀ : ℚ := 2 * U + 21 - 2 * t
  let X₁ : ℚ := 2 * U + 21 + 2 * t
  have hXprod : X₀ * X₁ = -7 := by
    dsimp [X₀, X₁]
    nlinarith [ht]
  have hX₀0 : X₀ ≠ 0 := by
    intro h
    rw [h] at hXprod
    norm_num at hXprod
  let Y₀ : ℚ := 2 * s * X₀
  have hdualFactor :
      X₀ ^ 2 - 42 * X₀ - 7 = 4 * U * X₀ := by
    dsimp [X₀]
    nlinarith [ht]
  have hdual :
      Y₀ ^ 2 = X₀ * (X₀ ^ 2 - 42 * X₀ - 7) := by
    rw [hdualFactor]
    dsimp [Y₀]
    rw [hU]
    ring
  obtain ⟨τ, X, q, hτ, hXdef, hX0, hXq⟩ :
      ∃ τ X q : ℚ,
        τ ^ 2 = U ^ 2 + 21 * U + 112 ∧
        X = 2 * U + 21 - 2 * τ ∧
        X ≠ 0 ∧ X = q ^ 2 := by
    rcases dual_abscissa_isSquare_or_negSeven hX₀0 hdual with
        hXsquare | ⟨z, hz⟩
    · obtain ⟨q, hq⟩ := hXsquare
      exact
        ⟨t, X₀, q, ht, rfl, hX₀0,
          by simpa [pow_two] using hq⟩
    · have hz0 : z ≠ 0 := by
        intro hz0
        rw [hz0] at hz
        norm_num at hz
        exact hX₀0 hz
      have hX₁square : X₁ = (1 / z) ^ 2 := by
        rw [hz] at hXprod
        dsimp [X₁]
        field_simp [hz0]
        nlinarith [hXprod]
      have hX₁0 : X₁ ≠ 0 := by
        rw [hX₁square]
        exact pow_ne_zero 2 (div_ne_zero (by norm_num) hz0)
      refine ⟨-t, X₁, 1 / z, ?_, ?_, hX₁0, hX₁square⟩
      · nlinarith [ht]
      · dsimp [X₁]
        ring
  let Y : ℚ := 2 * s * X
  have hfactor :
      X ^ 2 - 42 * X - 7 = 4 * U * X := by
    rw [hXdef]
    nlinarith [hτ]
  have hdualChosen :
      Y ^ 2 = X * (X ^ 2 - 42 * X - 7) := by
    rw [hfactor]
    dsimp [Y]
    rw [hU]
    ring
  have hq0 : q ≠ 0 := by
    intro hq
    rw [hq] at hXq
    norm_num at hXq
    exact hX0 hXq
  have hYq :
      (Y / q) ^ 2 = X ^ 2 - 42 * X - 7 := by
    rw [div_pow]
    field_simp [hq0]
    nlinarith [hdualChosen, hXq]
  let v : ℚ := -21 / 2 + X / 2 - Y / (2 * q)
  let w : ℚ := q * v
  have hvdef : v = -21 / 2 + X / 2 - Y / (2 * q) := rfl
  have hwdef : w = q * v := rfl
  have hXv : X * v = v ^ 2 + 21 * v + 112 := by
    dsimp [v]
    field_simp [hq0] at hYq ⊢
    nlinarith [hYq, hXq]
  have hv0 : v ≠ 0 := by
    intro hv
    rw [hv] at hXv
    norm_num at hXv
  have hw0 : w ≠ 0 :=
    mul_ne_zero hq0 hv0
  have hcurveQ : w ^ 2 = v * (v ^ 2 + 21 * v + 112) := by
    rw [hwdef, ← hXv, hXq]
    ring
  have hQ : curve.toAffine.Nonsingular v w := by
    apply curve.toAffine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [curve]
    linear_combination hcurveQ
  have hwneneg : w ≠ -w := by
    intro h
    apply hw0
    linarith
  have hneg : w ≠ curve.toAffine.negY v w := by
    simp only [WeierstrassCurve.Affine.negY]
    norm_num [curve]
    exact hwneneg
  let Q : curve.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some v w hQ
  have hdouble :=
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne
      (h₁ := hQ) hneg
  have hslope :
      curve.toAffine.slope v v w w =
        (3 * v ^ 2 + 42 * v + 112) / (2 * w) := by
    simp [WeierstrassCurve.Affine.slope,
      WeierstrassCurve.Affine.negY, curve, hwneneg]
    ring
  have haddX :
      curve.toAffine.addX v v
          (curve.toAffine.slope v v w w) =
        (v ^ 2 - 112) ^ 2 / (4 * w ^ 2) := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [curve]
    field_simp [hw0]
    rw [hcurveQ]
    ring
  have hYformula :
      Y = -q * (v ^ 2 - 112) / v :=
    y_formula_of_reverse_linear hv0
      (y_linear_of_reverse_definition hq0 hvdef) hXv
  have haddXeq :
      curve.toAffine.addX v v
          (curve.toAffine.slope v v w w) = U := by
    rw [haddX]
    have hYsq : Y ^ 2 = 4 * U * X ^ 2 := by
      dsimp [Y]
      rw [hU]
      ring
    have hYformulaCleared :
        Y ^ 2 * v ^ 2 =
          q ^ 2 * (v ^ 2 - 112) ^ 2 :=
      y_formula_squared hv0 hYformula
    have hcancel :
        q ^ 2 * (v ^ 2 - 112) ^ 2 =
          q ^ 2 * (4 * U * q ^ 2 * v ^ 2) := by
      calc
        q ^ 2 * (v ^ 2 - 112) ^ 2 =
            Y ^ 2 * v ^ 2 := hYformulaCleared.symm
        _ = q ^ 2 * (4 * U * q ^ 2 * v ^ 2) := by
          rw [hYsq, hXq]
          ring
    have htarget :
        (v ^ 2 - 112) ^ 2 = 4 * w ^ 2 * U := by
      have hcancelled :=
        mul_left_cancel₀ (pow_ne_zero 2 hq0) hcancel
      calc
        (v ^ 2 - 112) ^ 2 =
            4 * U * q ^ 2 * v ^ 2 := hcancelled
        _ = 4 * w ^ 2 * U := by rw [hwdef]; ring
    rw [htarget]
    field_simp [hw0]
  have hXcoord :
      Q + Q =
          WeierstrassCurve.Affine.Point.some U V hP ∨
        Q + Q =
          -WeierstrassCurve.Affine.Point.some U V hP := by
    rw [hdouble]
    apply WeierstrassCurve.Affine.Point.X_eq_iff.mp
    exact haddXeq
  rcases hXcoord with hQQ | hQQ
  · exact ⟨Q, by simpa [two_nsmul] using hQQ⟩
  · refine ⟨-Q, ?_⟩
    simp only [two_nsmul]
    calc
      -Q + -Q = -(Q + Q) := by rw [neg_add]
      _ = -(-WeierstrassCurve.Affine.Point.some U V hP) := by
        rw [hQQ]
      _ = WeierstrassCurve.Affine.Point.some U V hP := neg_neg _

/-! ## The two doubling cosets and rank zero -/





private lemma decompose_of_sub_eq_some
    {P R : curve.toAffine.Point} {x y : ℚ}
    {hxy : curve.toAffine.Nonsingular x y}
    (hsub : P - R = .some x y hxy)
    (hx0 : x ≠ 0) (hxSquare : IsSquare x) :
    ∃ Q : curve.toAffine.Point, P = R + (2 : ℕ) • Q := by
  obtain ⟨Q, hQ⟩ :=
    double_of_square_abscissa hx0 hxy hxSquare
  refine ⟨Q, ?_⟩
  calc
    P = R + (P - R) := by abel
    _ = R + (2 : ℕ) • Q := by rw [hsub, hQ]

private lemma decompose_seven_class
    {U V z : ℚ} (hU0 : U ≠ 0)
    (hP : curve.toAffine.Nonsingular U V)
    (hU : U = 7 * z ^ 2) :
    ∃ Q : curve.toAffine.Point,
      .some U V hP = T + (2 : ℕ) • Q := by
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz] at hU
    norm_num at hU
    exact hU0 hU
  have hcurve := curve_equation_of_nonsingular hP
  have hslope :
      curve.toAffine.slope U 0 V 0 = V / U := by
    simp [WeierstrassCurve.Affine.slope, hU0]
  have haddX :
      curve.toAffine.addX U 0
          (curve.toAffine.slope U 0 V 0) = 112 / U := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [curve]
    field_simp [hU0]
    nlinarith [hcurve]
  let hsum : curve.toAffine.Nonsingular
      (curve.toAffine.addX U 0
        (curve.toAffine.slope U 0 V 0))
      (curve.toAffine.addY U 0 V
        (curve.toAffine.slope U 0 V 0)) :=
    WeierstrassCurve.Affine.nonsingular_add
      hP nonsingular_zero_zero (fun h ↦ hU0 h.1)
  have hnegT : -T = T := by
    rw [T, WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    norm_num [WeierstrassCurve.Affine.negY, curve]
  have hsub :
      (.some U V hP : curve.toAffine.Point) - T =
        .some
          (curve.toAffine.addX U 0
            (curve.toAffine.slope U 0 V 0))
          (curve.toAffine.addY U 0 V
            (curve.toAffine.slope U 0 V 0)) hsum := by
    rw [sub_eq_add_neg, hnegT]
    change (.some U V hP : curve.toAffine.Point) +
        .some 0 0 nonsingular_zero_zero = _
    exact WeierstrassCurve.Affine.Point.add_of_X_ne hU0
  apply decompose_of_sub_eq_some hsub
  · rw [haddX, hU]
    apply div_ne_zero (by norm_num)
    intro h
    rw [h] at hU
    exact hU0 hU
  · refine ⟨4 / z, ?_⟩
    rw [haddX, hU]
    field_simp [hz0]
    ring

/-- Every rational point lies in one of two explicit cosets of twice the
rational point group. -/
theorem two_doubling_cosets (P : curve.toAffine.Point) :
    (∃ Q : curve.toAffine.Point, P = (2 : ℕ) • Q) ∨
      (∃ Q : curve.toAffine.Point, P = T + (2 : ℕ) • Q) := by
  cases P with
  | zero =>
      left
      exact ⟨0, rfl⟩
  | some U V hP =>
      have hcurve := curve_equation_of_nonsingular hP
      rcases eq_or_ne U 0 with rfl | hU0
      · have hV : V = 0 := by
          norm_num at hcurve
          nlinarith [sq_nonneg V]
        subst V
        right
        refine ⟨0, ?_⟩
        simp [T]
      · rcases curve_abscissa_isSquare_or_seven hU0 hcurve with
          hUsquare | ⟨z, hU⟩
        · left
          obtain ⟨Q, hQ⟩ :=
            double_of_square_abscissa hU0 hP hUsquare
          exact ⟨Q, hQ.symm⟩
        · right
          exact decompose_seven_class hU0 hP hU

/-- The image of multiplication by two on the rational point group. -/
abbrev doublingRange : AddSubgroup curve.toAffine.Point :=
  (nsmulAddMonoidHom (α := curve.toAffine.Point) 2).range

private def doublingRepresentative : Fin 2 → curve.toAffine.Point
  | 0 => 0
  | 1 => T

private lemma doubling_quotient_surjective :
    Function.Surjective
      (fun i : Fin 2 ↦
        QuotientAddGroup.mk' doublingRange
          (doublingRepresentative i)) := by
  intro c
  obtain ⟨P, rfl⟩ :=
    QuotientAddGroup.mk'_surjective doublingRange c
  rcases two_doubling_cosets P with ⟨Q, hQ⟩ | ⟨Q, hQ⟩
  · refine
      ⟨0, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm
  · refine
      ⟨1, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm

/-- The image of multiplication by two has finite index. -/
theorem doubling_finiteIndex : doublingRange.FiniteIndex := by
  letI : Finite (curve.toAffine.Point ⧸ doublingRange) :=
    Finite.of_surjective _ doubling_quotient_surjective
  exact AddSubgroup.finiteIndex_of_finite_quotient

/-- The rational point group is finitely generated. -/
theorem point_fg : AddGroup.FG curve.toAffine.Point :=
  WeierstrassCurve.Affine.fg_point_of_finiteIndex_two curve
    doubling_finiteIndex

/-- The multiplication-by-two index is at most two. -/
theorem doubling_index_le_two : doublingRange.index ≤ 2 := by
  rw [AddSubgroup.index_eq_card]
  exact
    (Nat.card_le_card_of_surjective _
      doubling_quotient_surjective).trans_eq (by simp)

private lemma double_T : (2 : ℕ) • T = 0 := by
  simp only [two_nsmul]
  rw [T]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY, curve]

private def twoToTwoTorsion :
    Fin 2 → {P : curve.toAffine.Point // (2 : ℕ) • P = 0}
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨T, double_T⟩

private lemma twoToTwoTorsion_injective :
    Function.Injective twoToTwoTorsion := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [twoToTwoTorsion, T] at hij ⊢

private lemma twoToTwoTorsion_surjective :
    Function.Surjective twoToTwoTorsion := by
  rintro ⟨P, htwo⟩
  cases P with
  | zero =>
      exact ⟨0, rfl⟩
  | some U V hP =>
      have hself :
          WeierstrassCurve.Affine.Point.some U V hP =
            -WeierstrassCurve.Affine.Point.some U V hP := by
        rw [← add_eq_zero_iff_eq_neg]
        simpa [two_nsmul] using htwo
      have hV : V = 0 := by
        rw [WeierstrassCurve.Affine.Point.neg_some] at hself
        simp only [WeierstrassCurve.Affine.Point.some.injEq,
          true_and] at hself
        norm_num [WeierstrassCurve.Affine.negY, curve] at hself
        linarith
      have hcurve := curve_equation_of_nonsingular hP
      have hquadratic : 0 < U ^ 2 + 21 * U + 112 := by
        nlinarith [sq_nonneg (2 * U + 21)]
      have hU : U = 0 := by
        rw [hV] at hcurve
        norm_num at hcurve
        rcases hcurve with hU | hquad
        · exact hU
        · exact (ne_of_gt hquadratic hquad).elim
      subst U
      subst V
      refine ⟨1, ?_⟩
      apply Subtype.ext
      rfl



/-- The `X₀(49)` model has exactly two rational points killed by two. -/
theorem two_torsion_card_eq_two :
    Nat.card
      {P : curve.toAffine.Point // (2 : ℕ) • P = 0} = 2 := by
  letI : Finite
      {P : curve.toAffine.Point // (2 : ℕ) • P = 0} :=
    MazurTorsion.finite_two_torsion curve
  simpa using
    (Nat.card_congr
      (Equiv.ofBijective twoToTwoTorsion
        ⟨twoToTwoTorsion_injective,
          twoToTwoTorsion_surjective⟩)).symm

/-- The rational point group has Mordell--Weil rank zero. -/
theorem point_rank_zero :
    Module.finrank ℤ curve.toAffine.Point = 0 := by
  letI : AddGroup.FG curve.toAffine.Point := point_fg
  have hker :
      Nat.card
          (nsmulAddMonoidHom
            (α := curve.toAffine.Point) 2).ker = 2 := by
    change Nat.card
      {P : curve.toAffine.Point // (2 : ℕ) • P = 0} = 2
    exact two_torsion_card_eq_two
  have hformula :=
    AddSubgroup.index_range_nsmul_of_fg curve.toAffine.Point
      (by norm_num : (2 : ℕ) ≠ 0)
  rw [hker] at hformula
  have hpow :
      2 ^ Module.finrank ℤ curve.toAffine.Point ≤ 1 := by
    have hindex := doubling_index_le_two
    change
      (nsmulAddMonoidHom
        (α := curve.toAffine.Point) 2).range.index ≤ 2
      at hindex
    omega
  have hpowequal :
      2 ^ Module.finrank ℤ curve.toAffine.Point = 1 :=
    le_antisymm hpow
      (Nat.one_le_pow _ _ (by norm_num))
  simpa using hpowequal

/-- All rational points are torsion; the rational point group is
finite. -/
theorem point_finite : Finite curve.toAffine.Point := by
  letI : AddGroup.FG curve.toAffine.Point := point_fg
  letI : Module.Finite ℤ curve.toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr point_fg
  have hmoduleTorsion :
      Module.IsTorsion ℤ curve.toAffine.Point :=
    (Module.finrank_eq_zero_iff_isTorsion (R := ℤ)).mp
      point_rank_zero
  exact AddCommGroup.finite_of_fg_torsion curve.toAffine.Point
    (AddMonoid.isTorsion_iff_isTorsion_int.mpr hmoduleTorsion)

/-! ## No rational point of order four -/





end MazurTorsion.XZeroFortyNine

end

theorem solution :
  Finite MazurTorsion.XZeroFortyNine.curve.toAffine.Point := by
  exact MazurTorsion.XZeroFortyNine.point_finite

#print axioms solution
