-- Prove2me | solution 1 for MazurCampaign.exceptional_cubic_finite
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T08:48:20.11209+00:00
-- url     : https://prove2.me/submissions/0ae219ea-c388-45e3-b8d8-061742aea0f9

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints


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













/-- Over a field of characteristic different from two, an elliptic curve has
at most four points killed by `2`. -/
theorem ncard_two_torsion_le_four :
    Set.ncard {P : (E⁄F).Point | (2 : ℕ) • P = 0} ≤ 4 := by
  rw [← Nat.card_coe_set_eq]
  calc
    Nat.card {P : (E⁄F).Point // (2 : ℕ) • P = 0}
        ≤ Nat.card (Option
          (E.twoTorsionPolynomial.toPoly.rootSet F)) :=
      Nat.card_le_card_of_injective (twoTorsionRootMap E)
        (twoTorsionRootMap_injective E)
    _ = Nat.card (E.twoTorsionPolynomial.toPoly.rootSet F) + 1 := by
      rw [Finite.card_option]
    _ ≤ 3 + 1 := by
      gcongr
      rw [Nat.card_coe_set_eq]
      exact (E.twoTorsionPolynomial.toPoly.ncard_rootSet_le F).trans_eq
        (Cubic.natDegree_of_a_ne_zero' (by
          rw [show (4 : F) = 2 ^ 2 by norm_num]
          exact pow_ne_zero 2 (NeZero.ne (2 : F))))
    _ = 4 := by norm_num





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


/- Source module: MazurTorsion.NumberTheory.ExceptionalCubicDescent. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Explicit two-isogeny descent on the exceptional cubic

This file studies the rational elliptic curve

`y² = u(u² + 2u - 3) = u(u - 1)(u + 3)`,

which is obtained from
`Y² = (X - 10)(X - 6)(X + 6)` by `X = 4u + 6` and `Y = 8y`.

An explicit two-isogeny descent proves that `E(ℚ) / 2E(ℚ)` has at most
four elements.  Naïve-height descent then gives finite generation, and
the exact four rational two-torsion points force Mordell--Weil rank zero.
Consequently the rational point group is finite.

The last theorem deliberately records the remaining sharp boundary:
an independent bound `#E(ℚ) ≤ 8` would classify all points and prove
`ExceptionalCubicIsTrivial`.  Rank zero alone does not supply that bound,
because odd torsion or higher two-primary torsion must still be excluded.
-/

namespace MazurTorsion.ExceptionalCubic

open scoped WeierstrassCurve.Affine

/-- The translated `X₀(24)` model `y² = u(u² + 2u - 3)`. -/
def curve : WeierstrassCurve ℚ :=
  ⟨0, 2, 0, -3, 0⟩

/-- The curve two-isogenous to `curve`. -/
def dualCurve : WeierstrassCurve ℚ :=
  ⟨0, -4, 0, 16, 0⟩

private instance curve_isElliptic : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private instance dualCurve_isElliptic : dualCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [dualCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

private lemma nonsingular_zero_zero :
    curve.toAffine.Nonsingular 0 0 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_neg_one_two :
    curve.toAffine.Nonsingular (-1) 2 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_neg_one_neg_two :
    curve.toAffine.Nonsingular (-1) (-2) := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_three_six :
    curve.toAffine.Nonsingular 3 6 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_three_neg_six :
    curve.toAffine.Nonsingular 3 (-6) := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_one_zero :
    curve.toAffine.Nonsingular 1 0 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

private lemma nonsingular_neg_three_zero :
    curve.toAffine.Nonsingular (-3) 0 := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

/-- The rational two-torsion point `(0, 0)`. -/
def T : curve.toAffine.Point :=
  .some 0 0 nonsingular_zero_zero

/-- The rational point `(-1, 2)`. -/
def D : curve.toAffine.Point :=
  .some (-1) 2 nonsingular_neg_one_two



/-- The rational point `(3, 6)`. -/
def F : curve.toAffine.Point :=
  .some 3 6 nonsingular_three_six



private def A : curve.toAffine.Point :=
  .some 1 0 nonsingular_one_zero

private def B : curve.toAffine.Point :=
  .some (-3) 0 nonsingular_neg_three_zero

private abbrev redTwo : ZMod 16 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 16) (ZMod 2)

private lemma zmod_sixteen_obstruction :
    ∀ u w v : ZMod 16,
      (redTwo u ≠ 0 ∨ redTwo w ≠ 0) →
        v ^ 2 ≠ 2 * (u ^ 4 - 2 * u ^ 2 * w ^ 2 + 4 * w ^ 4) := by
  decide

lemma no_dual_two_class
    (U W V : ℤ) (hcoprime : IsCoprime U W) :
    V ^ 2 ≠ 2 * (U ^ 4 - 2 * U ^ 2 * W ^ 2 + 4 * W ^ 4) := by
  intro h
  have hparity :
      redTwo (U : ZMod 16) ≠ 0 ∨ redTwo (W : ZMod 16) ≠ 0 := by
    by_contra hboth
    simp only [not_or, not_not] at hboth
    have hUeven : Even U := by
      rw [← ZMod.intCast_eq_zero_iff_even]
      simpa [redTwo] using hboth.1
    have hWeven : Even W := by
      rw [← ZMod.intCast_eq_zero_iff_even]
      simpa [redTwo] using hboth.2
    have hunit : IsUnit (2 : ℤ) :=
      hcoprime.isUnit_of_dvd' (even_iff_two_dvd.mp hUeven) (even_iff_two_dvd.mp hWeven)
    exact (by norm_num [Int.isUnit_iff] at hunit)
  apply zmod_sixteen_obstruction (U : ZMod 16) (W : ZMod 16) (V : ZMod 16) hparity
  simpa using congrArg (fun z : ℤ ↦ (z : ZMod 16)) h

lemma no_dual_two_class_rat (z q : ℚ) :
    q ^ 2 ≠ 2 * (z ^ 4 - 2 * z ^ 2 + 4) := by
  intro h
  let U : ℤ := z.num
  let W : ℤ := z.den
  have hW : (W : ℚ) ≠ 0 := by
    dsimp [W]
    exact_mod_cast z.den_ne_zero
  have hz : z = (U : ℚ) / W := by
    exact z.num_div_den.symm
  have hscaled :
      (q * W ^ 2) ^ 2 =
        ((2 * (U ^ 4 - 2 * U ^ 2 * W ^ 2 + 4 * W ^ 4) : ℤ) : ℚ) := by
    rw [hz] at h
    field_simp [hW] at h
    calc
      (q * W ^ 2) ^ 2 = q ^ 2 * W ^ 4 := by ring
      _ = 2 * ((U : ℚ) ^ 2 * ((U : ℚ) ^ 2 - 2 * (W : ℚ) ^ 2) +
          (W : ℚ) ^ 4 * 4) := h
      _ = ((2 * (U ^ 4 - 2 * U ^ 2 * W ^ 2 + 4 * W ^ 4) : ℤ) : ℚ) := by
        push_cast
        ring
  have hsquareRat :
      IsSquare (((2 * (U ^ 4 - 2 * U ^ 2 * W ^ 2 + 4 * W ^ 4) : ℤ) : ℚ)) :=
    ⟨q * W ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨V, hV⟩ := Rat.isSquare_intCast_iff.mp hsquareRat
  apply no_dual_two_class U W V
  · simpa [U, W] using Rat.isCoprime_num_den z
  · simpa [pow_two] using hV.symm

private lemma common_divisor_dual_dvd_sixteen
    {m n d : ℤ} (hcoprime : IsCoprime m n)
    (hA : d ∣ m * n)
    (hB : d ∣ m ^ 2 - 4 * m * n + 16 * n ^ 2) :
    d ∣ 16 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hm3 : d ∣ m ^ 3 := by
    refine ⟨m * b + (4 * m - 16 * n) * a, ?_⟩
    linear_combination m * hb + (4 * m - 16 * n) * ha
  have h16n3 : d ∣ 16 * n ^ 3 := by
    refine ⟨n * b - (m - 4 * n) * a, ?_⟩
    linear_combination n * hb - (m - 4 * n) * ha
  have hcoprimePowers : IsCoprime (m ^ 3) (n ^ 3) :=
    hcoprime.pow
  have hcoprimeDN : IsCoprime d (n ^ 3) :=
    hcoprimePowers.of_isCoprime_of_dvd_left hm3
  exact hcoprimeDN.dvd_of_dvd_mul_right (by simpa [mul_comm] using h16n3)

private lemma positive_squareclass_of_gcd_dvd_sixteen
    {A B C : ℤ} (hApos : 0 < A) (hprod : A * B = C ^ 2)
    (hgcd : GCDMonoid.gcd A B ∣ (16 : ℤ)) :
    ∃ z : ℤ, A = z ^ 2 ∨ A = 2 * z ^ 2 := by
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
  have habcoprime : IsCoprime a b := by
    exact isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0
  obtain ⟨z, hz | hz⟩ := Int.sq_of_isCoprime habcoprime hab
  · have hAz : A = g * z ^ 2 := by rw [← hga, hz]
    have hgabs : g.natAbs ∣ 16 := by
      simpa using Int.natAbs_dvd_natAbs.mpr hgcd
    have hgleNat : g.natAbs ≤ 16 :=
      Nat.le_of_dvd (by norm_num) hgabs
    have hgle : g ≤ 16 := by
      have hgleCast : (g.natAbs : ℤ) ≤ 16 := by
        exact_mod_cast hgleNat
      simpa [Int.natCast_natAbs, abs_of_pos hgpos] using hgleCast
    have hgvals : g = 1 ∨ g = 2 ∨ g = 4 ∨ g = 8 ∨ g = 16 := by
      interval_cases g <;> norm_num at hgabs
      all_goals simp
    rcases hgvals with hg | hg | hg | hg | hg
    · rw [hg] at hAz
      exact ⟨z, Or.inl (by simpa using hAz)⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (by simpa using hAz)⟩
    · rw [hg] at hAz
      exact ⟨2 * z, Or.inl (by nlinarith [hAz])⟩
    · rw [hg] at hAz
      exact ⟨2 * z, Or.inr (by nlinarith [hAz])⟩
    · rw [hg] at hAz
      exact ⟨4 * z, Or.inl (by nlinarith [hAz])⟩
  · have haNeg : a ≤ 0 := by nlinarith [sq_nonneg z]
    have : A ≤ 0 := by rw [← hga]; exact mul_nonpos_of_nonneg_of_nonpos hgpos.le haNeg
    exact (not_lt_of_ge this hApos).elim

theorem dual_abscissa_isSquare
    {X Y : ℚ} (hcurve : Y ^ 2 = X * (X ^ 2 - 4 * X + 16)) :
    IsSquare X := by
  rcases eq_or_ne X 0 with rfl | hX0
  · exact IsSquare.zero
  have hquadratic : 0 < X ^ 2 - 4 * X + 16 := by
    nlinarith [sq_nonneg (X - 2)]
  have hXpos : 0 < X := by
    by_contra! hXnonpos
    have hXneg : X < 0 := lt_of_le_of_ne hXnonpos hX0
    have hnegative : X * (X ^ 2 - 4 * X + 16) < 0 :=
      mul_neg_of_neg_of_pos hXneg hquadratic
    rw [← hcurve] at hnegative
    exact (not_lt_of_ge (sq_nonneg Y)) hnegative
  let m : ℤ := X.num
  let n : ℤ := X.den
  let A : ℤ := m * n
  let B : ℤ := m ^ 2 - 4 * m * n + 16 * n ^ 2
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast X.den_pos
  have hn0q : (n : ℚ) ≠ 0 := by positivity
  have hX : X = (m : ℚ) / n := X.num_div_den.symm
  have hscaled :
      (Y * n ^ 2) ^ 2 = (((A * B : ℤ) : ℚ)) := by
    rw [hX] at hcurve
    field_simp [hn0q] at hcurve
    calc
      (Y * n ^ 2) ^ 2 = Y ^ 2 * n ^ 4 := by ring
      _ = (m : ℚ) * n *
          ((m : ℚ) ^ 2 - 4 * m * n + 16 * n ^ 2) := by
        linear_combination n * hcurve
      _ = (((A * B : ℤ) : ℚ)) := by
        dsimp [A, B]
        push_cast
        ring
  have hsquareRat : IsSquare (((A * B : ℤ) : ℚ)) :=
    ⟨Y * n ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨C, hC⟩ := Rat.isSquare_intCast_iff.mp hsquareRat
  have hprod : A * B = C ^ 2 := by
    simpa [pow_two] using hC
  have hApos : 0 < A := by
    have hmpos : 0 < m := by
      dsimp [m]
      exact Rat.num_pos.mpr hXpos
    exact mul_pos hmpos hnpos
  have hmnCoprime : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den X
  have hgcd : GCDMonoid.gcd A B ∣ (16 : ℤ) :=
    common_divisor_dual_dvd_sixteen hmnCoprime
      (GCDMonoid.gcd_dvd_left A B) (GCDMonoid.gcd_dvd_right A B)
  obtain ⟨z, hA | hA⟩ :=
    positive_squareclass_of_gcd_dvd_sixteen hApos hprod hgcd
  · refine ⟨(z : ℚ) / n, ?_⟩
    rw [hX]
    simp only [A] at hA
    field_simp [hn0q]
    exact_mod_cast hA
  · exfalso
    let r : ℚ := (z : ℚ) / n
    have hr : X = 2 * r ^ 2 := by
      rw [hX]
      simp only [A] at hA
      dsimp [r]
      field_simp [hn0q]
      exact_mod_cast hA
    have hr0 : r ≠ 0 := by
      intro hrzero
      rw [hrzero] at hr
      norm_num at hr
      exact hX0 hr
    apply no_dual_two_class_rat r (Y / (2 * r))
    rw [div_pow]
    field_simp [hr0]
    rw [hr] at hcurve
    nlinarith [hcurve]

private lemma common_divisor_curve_dvd_three
    {m n d : ℤ} (hcoprime : IsCoprime m n)
    (hA : d ∣ m * n)
    (hB : d ∣ m ^ 2 + 2 * m * n - 3 * n ^ 2) :
    d ∣ 3 := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hm3 : d ∣ m ^ 3 := by
    refine ⟨m * b - (2 * m - 3 * n) * a, ?_⟩
    linear_combination m * hb - (2 * m - 3 * n) * ha
  have h3n3 : d ∣ 3 * n ^ 3 := by
    refine ⟨(m + 2 * n) * a - n * b, ?_⟩
    linear_combination (m + 2 * n) * ha - n * hb
  have hcoprimePowers : IsCoprime (m ^ 3) (n ^ 3) :=
    hcoprime.pow
  have hcoprimeDN : IsCoprime d (n ^ 3) :=
    hcoprimePowers.of_isCoprime_of_dvd_left hm3
  exact hcoprimeDN.dvd_of_dvd_mul_right (by simpa [mul_comm] using h3n3)

private lemma squareclass_of_gcd_dvd_three
    {A B C : ℤ} (hA0 : A ≠ 0) (hprod : A * B = C ^ 2)
    (hgcd : GCDMonoid.gcd A B ∣ (3 : ℤ)) :
    ∃ z : ℤ, A = z ^ 2 ∨ A = -z ^ 2 ∨ A = 3 * z ^ 2 ∨ A = -3 * z ^ 2 := by
  let g : ℤ := GCDMonoid.gcd A B
  have hgA : g ∣ A := GCDMonoid.gcd_dvd_left A B
  have hgB : g ∣ B := GCDMonoid.gcd_dvd_right A B
  have hg0 : g ≠ 0 := by
    intro hg
    rw [hg] at hgA
    exact hA0 (zero_dvd_iff.mp hgA)
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
  have habcoprime : IsCoprime a b :=
    isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0
  obtain ⟨z, hz | hz⟩ := Int.sq_of_isCoprime habcoprime hab
  · have hAz : A = g * z ^ 2 := by rw [← hga, hz]
    have hgabs : g.natAbs ∣ 3 := by
      simpa using Int.natAbs_dvd_natAbs.mpr hgcd
    have hgleNat : g.natAbs ≤ 3 :=
      Nat.le_of_dvd (by norm_num) hgabs
    have hgle : g ≤ 3 := by
      have hgleCast : (g.natAbs : ℤ) ≤ 3 := by exact_mod_cast hgleNat
      simpa [Int.natCast_natAbs, abs_of_pos hgpos] using hgleCast
    have hgvals : g = 1 ∨ g = 3 := by
      interval_cases g <;> norm_num at hgabs
      all_goals simp
    rcases hgvals with hg | hg
    · rw [hg] at hAz
      exact ⟨z, Or.inl (by simpa using hAz)⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inl (by simpa using hAz)))⟩
  · have hAz : A = -(g * z ^ 2) := by rw [← hga, hz]; ring
    have hgabs : g.natAbs ∣ 3 := by
      simpa using Int.natAbs_dvd_natAbs.mpr hgcd
    have hgleNat : g.natAbs ≤ 3 :=
      Nat.le_of_dvd (by norm_num) hgabs
    have hgle : g ≤ 3 := by
      have hgleCast : (g.natAbs : ℤ) ≤ 3 := by exact_mod_cast hgleNat
      simpa [Int.natCast_natAbs, abs_of_pos hgpos] using hgleCast
    have hgvals : g = 1 ∨ g = 3 := by
      interval_cases g <;> norm_num at hgabs
      all_goals simp
    rcases hgvals with hg | hg
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inl (by simpa using hAz))⟩
    · rw [hg] at hAz
      exact ⟨z, Or.inr (Or.inr (Or.inr (by nlinarith [hAz])))⟩

theorem curve_abscissa_squareclass
    {u y : ℚ} (hu : u ≠ 0)
    (hcurve : y ^ 2 = u * (u ^ 2 + 2 * u - 3)) :
    (∃ z : ℚ, u = z ^ 2) ∨
      (∃ z : ℚ, u = -z ^ 2) ∨
      (∃ z : ℚ, u = 3 * z ^ 2) ∨
      (∃ z : ℚ, u = -3 * z ^ 2) := by
  let m : ℤ := u.num
  let n : ℤ := u.den
  let A : ℤ := m * n
  let B : ℤ := m ^ 2 + 2 * m * n - 3 * n ^ 2
  have hn0q : (n : ℚ) ≠ 0 := by
    dsimp [n]
    positivity
  have hU : u = (m : ℚ) / n := u.num_div_den.symm
  have hscaled :
      (y * n ^ 2) ^ 2 = (((A * B : ℤ) : ℚ)) := by
    rw [hU] at hcurve
    field_simp [hn0q] at hcurve
    calc
      (y * n ^ 2) ^ 2 = y ^ 2 * n ^ 4 := by ring
      _ = (m : ℚ) * n *
          ((m : ℚ) ^ 2 + 2 * m * n - 3 * n ^ 2) := by
        linear_combination n * hcurve
      _ = (((A * B : ℤ) : ℚ)) := by
        dsimp [A, B]
        push_cast
        ring
  have hsquareRat : IsSquare (((A * B : ℤ) : ℚ)) :=
    ⟨y * n ^ 2, by simpa [pow_two] using hscaled.symm⟩
  obtain ⟨C, hC⟩ := Rat.isSquare_intCast_iff.mp hsquareRat
  have hprod : A * B = C ^ 2 := by
    simpa [pow_two] using hC
  have hA0 : A ≠ 0 := by
    apply mul_ne_zero
    · dsimp [m]
      exact Rat.num_ne_zero.mpr hu
    · dsimp [n]
      exact_mod_cast u.den_ne_zero
  have hmnCoprime : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den u
  have hgcd : GCDMonoid.gcd A B ∣ (3 : ℤ) :=
    common_divisor_curve_dvd_three hmnCoprime
      (GCDMonoid.gcd_dvd_left A B) (GCDMonoid.gcd_dvd_right A B)
  obtain ⟨z, hA | hA | hA | hA⟩ :=
    squareclass_of_gcd_dvd_three hA0 hprod hgcd
  · left
    refine ⟨(z : ℚ) / n, ?_⟩
    rw [hU]
    simp only [A] at hA
    field_simp [hn0q]
    exact_mod_cast hA
  · right; left
    refine ⟨(z : ℚ) / n, ?_⟩
    rw [hU]
    simp only [A] at hA
    field_simp [hn0q]
    exact_mod_cast hA
  · right; right; left
    refine ⟨(z : ℚ) / n, ?_⟩
    rw [hU]
    simp only [A] at hA
    field_simp [hn0q]
    exact_mod_cast hA
  · right; right; right
    have hA' : A = -(3 * z ^ 2) := by nlinarith [hA]
    refine ⟨(z : ℚ) / n, ?_⟩
    rw [hU]
    simp only [A] at hA'
    field_simp [hn0q]
    exact_mod_cast hA'

private lemma y_linear_of_v_definition
    {X Y q v : ℚ} (hq0 : q ≠ 0)
    (hv : v = -1 + X / 2 - Y / (2 * q)) :
    Y = q * (X - 2 - 2 * v) := by
  field_simp [hq0] at hv
  linear_combination hv

private lemma y_formula_of_linear
    {X Y q v : ℚ} (hv0 : v ≠ 0)
    (hlinear : Y = q * (X - 2 - 2 * v))
    (hXv : X * v = v ^ 2 + 2 * v - 3) :
    Y = -q * (v ^ 2 + 3) / v := by
  rw [hlinear]
  field_simp [hv0]
  linear_combination q * hXv

private lemma y_formula_squared
    {Y q v : ℚ} (hv0 : v ≠ 0)
    (hY : Y = -q * (v ^ 2 + 3) / v) :
    Y ^ 2 * v ^ 2 = q ^ 2 * (v ^ 2 + 3) ^ 2 := by
  rw [hY]
  field_simp [hv0]

theorem double_of_square_abscissa
    {u y : ℚ} (hu0 : u ≠ 0) (hP : curve.toAffine.Nonsingular u y)
    (huSquare : IsSquare u) :
    ∃ Q : curve.toAffine.Point,
      (2 : ℕ) • Q = WeierstrassCurve.Affine.Point.some u y hP := by
  obtain ⟨s, hs⟩ := huSquare
  have hu : u = s ^ 2 := by simpa [pow_two] using hs
  have hs0 : s ≠ 0 := by
    intro hszero
    rw [hszero] at hu
    norm_num at hu
    exact hu0 hu
  have hcurve : y ^ 2 = u * (u ^ 2 + 2 * u - 3) := by
    have heq := hP.1
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    norm_num [curve] at heq
    nlinarith
  let t : ℚ := y / s
  have ht : t ^ 2 = u ^ 2 + 2 * u - 3 := by
    dsimp [t]
    rw [div_pow]
    field_simp [hs0]
    nlinarith [hcurve, hu]
  let X : ℚ := 2 + 2 * u - 2 * t
  let Y : ℚ := 2 * s * X
  have hXprod : X * (2 + 2 * u + 2 * t) = 16 := by
    dsimp [X]
    nlinarith [ht]
  have hX0 : X ≠ 0 := by
    intro hX
    rw [hX] at hXprod
    norm_num at hXprod
  have hdualFactor : X ^ 2 - 4 * X + 16 = 4 * u * X := by
    dsimp [X]
    nlinarith [ht]
  have hdual : Y ^ 2 = X * (X ^ 2 - 4 * X + 16) := by
    rw [hdualFactor]
    dsimp [Y]
    rw [hu]
    ring
  obtain ⟨q, hq⟩ := dual_abscissa_isSquare hdual
  have hXq : X = q ^ 2 := by simpa [pow_two] using hq
  have hq0 : q ≠ 0 := by
    intro hqzero
    rw [hqzero] at hXq
    norm_num at hXq
    exact hX0 hXq
  have hYq :
      (Y / q) ^ 2 = X ^ 2 - 4 * X + 16 := by
    rw [div_pow]
    field_simp [hq0]
    nlinarith [hdual, hXq]
  let v : ℚ := -1 + X / 2 - Y / (2 * q)
  let w : ℚ := q * v
  have hvdef : v = -1 + X / 2 - Y / (2 * q) := rfl
  have hwdef : w = q * v := rfl
  have hXv : X * v = v ^ 2 + 2 * v - 3 := by
    dsimp [v]
    field_simp [hq0] at hYq ⊢
    nlinarith [hYq, hXq]
  have hv0 : v ≠ 0 := by
    intro hvzero
    rw [hvzero] at hXv
    norm_num at hXv
  have hw0 : w ≠ 0 :=
    mul_ne_zero hq0 hv0
  have hcurveQ : w ^ 2 = v * (v ^ 2 + 2 * v - 3) := by
    rw [hwdef]
    rw [← hXv, hXq]
    ring
  have hQ : curve.toAffine.Nonsingular v w := by
    apply curve.toAffine.equation_iff_nonsingular.mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [curve]
    nlinarith [hcurveQ]
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
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hQ) hneg
  have hslope :
      curve.toAffine.slope v v w w =
        (3 * v ^ 2 + 4 * v - 3) / (2 * w) := by
    simp [WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.negY,
      curve, hwneneg]
    ring
  have haddX :
      curve.toAffine.addX v v (curve.toAffine.slope v v w w) =
        (v ^ 2 + 3) ^ 2 / (4 * w ^ 2) := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [curve]
    field_simp [hw0]
    rw [hcurveQ]
    ring
  have hYformula : Y = -q * (v ^ 2 + 3) / v := by
    exact y_formula_of_linear hv0
      (y_linear_of_v_definition hq0 hvdef) hXv
  have haddXeq :
      curve.toAffine.addX v v (curve.toAffine.slope v v w w) = u := by
    rw [haddX]
    have hYsq : Y ^ 2 = 4 * u * X ^ 2 := by
      dsimp [Y]
      rw [hu]
      ring
    have hYformulaCleared :
        Y ^ 2 * v ^ 2 = q ^ 2 * (v ^ 2 + 3) ^ 2 :=
      y_formula_squared hv0 hYformula
    have hcancel :
        q ^ 2 * (v ^ 2 + 3) ^ 2 =
          q ^ 2 * (4 * u * q ^ 2 * v ^ 2) := by
      calc
        q ^ 2 * (v ^ 2 + 3) ^ 2 = Y ^ 2 * v ^ 2 := hYformulaCleared.symm
        _ = q ^ 2 * (4 * u * q ^ 2 * v ^ 2) := by rw [hYsq, hXq]; ring
    have htarget : (v ^ 2 + 3) ^ 2 = 4 * w ^ 2 * u := by
      have hcancelled :=
        mul_left_cancel₀ (pow_ne_zero 2 hq0) hcancel
      calc
        (v ^ 2 + 3) ^ 2 = 4 * u * q ^ 2 * v ^ 2 := hcancelled
        _ = 4 * w ^ 2 * u := by rw [hwdef]; ring
    rw [htarget]
    field_simp [hw0]
  have hXcoord :
      (Q + Q) =
          WeierstrassCurve.Affine.Point.some u y hP ∨
        (Q + Q) =
          -WeierstrassCurve.Affine.Point.some u y hP := by
    rw [hdouble]
    apply WeierstrassCurve.Affine.Point.X_eq_iff.mp
    exact haddXeq
  rcases hXcoord with hQQ | hQQ
  · exact ⟨Q, by simpa [two_nsmul] using hQQ⟩
  · refine ⟨-Q, ?_⟩
    simp only [two_nsmul]
    calc
      -Q + -Q = -(Q + Q) := by rw [neg_add]
      _ = -(-WeierstrassCurve.Affine.Point.some u y hP) := by rw [hQQ]
      _ = WeierstrassCurve.Affine.Point.some u y hP := neg_neg _

private lemma curve_equation_of_nonsingular
    {u y : ℚ} (hP : curve.toAffine.Nonsingular u y) :
    y ^ 2 = u * (u ^ 2 + 2 * u - 3) := by
  have heq := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  norm_num [curve] at heq
  nlinarith

private lemma decompose_of_sub_eq_some
    {P R : curve.toAffine.Point} {x y : ℚ}
    {hxy : curve.toAffine.Nonsingular x y}
    (hsub : P - R = .some x y hxy)
    (hx0 : x ≠ 0) (hxSquare : IsSquare x) :
    ∃ Q : curve.toAffine.Point, P = R + (2 : ℕ) • Q := by
  obtain ⟨Q, hQ⟩ := double_of_square_abscissa hx0 hxy hxSquare
  refine ⟨Q, ?_⟩
  calc
    P = R + (P - R) := by abel
    _ = R + (2 : ℕ) • Q := by rw [hsub, hQ]

private lemma decompose_neg_three_class
    {u y z : ℚ} (hu0 : u ≠ 0)
    (hP : curve.toAffine.Nonsingular u y)
    (hu : u = -3 * z ^ 2) :
    ∃ Q : curve.toAffine.Point,
      .some u y hP = T + (2 : ℕ) • Q := by
  have hz0 : z ≠ 0 := by
    intro hz
    rw [hz] at hu
    norm_num at hu
    exact hu0 hu
  have hcurve := curve_equation_of_nonsingular hP
  have hslope :
      curve.toAffine.slope u 0 y 0 = y / u := by
    simp [WeierstrassCurve.Affine.slope, hu0]
  have haddX :
      curve.toAffine.addX u 0 (curve.toAffine.slope u 0 y 0) = -3 / u := by
    rw [hslope]
    simp only [WeierstrassCurve.Affine.addX]
    norm_num [curve]
    field_simp [hu0]
    nlinarith [hcurve]
  let hsum : curve.toAffine.Nonsingular
      (curve.toAffine.addX u 0 (curve.toAffine.slope u 0 y 0))
      (curve.toAffine.addY u 0 y (curve.toAffine.slope u 0 y 0)) :=
    WeierstrassCurve.Affine.nonsingular_add hP nonsingular_zero_zero
      (fun h ↦ hu0 h.1)
  have hsub :
      (.some u y hP : curve.toAffine.Point) - T =
        .some
          (curve.toAffine.addX u 0 (curve.toAffine.slope u 0 y 0))
          (curve.toAffine.addY u 0 y (curve.toAffine.slope u 0 y 0)) hsum := by
    have hnegT : -T = T := by
      rw [T, WeierstrassCurve.Affine.Point.neg_some]
      simp only [WeierstrassCurve.Affine.Point.some.injEq]
      norm_num [WeierstrassCurve.Affine.negY, curve]
    rw [sub_eq_add_neg, hnegT]
    change (.some u y hP : curve.toAffine.Point) +
        .some 0 0 nonsingular_zero_zero = _
    exact WeierstrassCurve.Affine.Point.add_of_X_ne hu0
  apply decompose_of_sub_eq_some hsub
  · rw [haddX, hu]
    exact div_ne_zero (by norm_num)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz0))
  · refine ⟨1 / z, ?_⟩
    rw [haddX, hu]
    field_simp [hz0]

private lemma decompose_neg_one_class
    {u y z : ℚ} (hu0 : u ≠ 0)
    (hP : curve.toAffine.Nonsingular u y)
    (hu : u = -z ^ 2) :
    ∃ Q : curve.toAffine.Point,
      .some u y hP = D + (2 : ℕ) • Q := by
  have hcurve := curve_equation_of_nonsingular hP
  rcases eq_or_ne u (-1) with huD | huD
  · clear hu
    subst u
    have hySq : y ^ 2 = (2 : ℚ) ^ 2 := by
      norm_num at hcurve ⊢
      exact hcurve
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hySq with hy | hy
    · subst y
      refine ⟨0, ?_⟩
      simp [D]
    · have hy' : y = -2 := by simpa using hy
      subst y
      have hpoint :
          (.some (-1) (-2) hP : curve.toAffine.Point) = -D := by
        rw [D, WeierstrassCurve.Affine.Point.neg_some]
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        norm_num [WeierstrassCurve.Affine.negY, curve]
      refine ⟨-D, ?_⟩
      rw [hpoint]
      simp only [two_nsmul]
      abel
  · have hz0 : z ≠ 0 := by
      intro hz
      rw [hz] at hu
      norm_num at hu
      exact hu0 hu
    have huplus : u + 1 ≠ 0 := by
      intro h
      apply huD
      linarith
    have hslope :
        curve.toAffine.slope u (-1) y (-2) = (y + 2) / (u + 1) := by
      simp [WeierstrassCurve.Affine.slope, huD]
    have haddX :
        curve.toAffine.addX u (-1)
            (curve.toAffine.slope u (-1) y (-2)) =
          ((y + 2) / (u + 1)) ^ 2 - u - 1 := by
      rw [hslope]
      simp only [WeierstrassCurve.Affine.addX]
      norm_num [curve]
      ring
    have hnumerator : y - 2 * u ≠ 0 := by
      intro hzero
      have hy : y = 2 * u := by linarith
      have hfactor : u * ((u + 1) * (u - 3)) = 0 := by
        rw [hy] at hcurve
        nlinarith [hcurve]
      rcases mul_eq_zero.mp hfactor with hu' | hfactor
      · exact hu0 hu'
      rcases mul_eq_zero.mp hfactor with hleft | hright
      · apply huD
        linarith
      · have hu3 : u = 3 := by linarith
        rw [hu3] at hu
        nlinarith [sq_nonneg z]
    let w : ℚ := (y - 2 * u) / ((u + 1) * z)
    have haddXsq :
        curve.toAffine.addX u (-1)
            (curve.toAffine.slope u (-1) y (-2)) = w ^ 2 := by
      rw [haddX]
      dsimp [w]
      field_simp [huplus, hz0]
      nlinarith [hcurve, hu]
    let hsum : curve.toAffine.Nonsingular
        (curve.toAffine.addX u (-1)
          (curve.toAffine.slope u (-1) y (-2)))
        (curve.toAffine.addY u (-1) y
          (curve.toAffine.slope u (-1) y (-2))) :=
      WeierstrassCurve.Affine.nonsingular_add hP nonsingular_neg_one_neg_two
        (fun h ↦ huD h.1)
    have hnegD :
        -D = .some (-1) (-2) nonsingular_neg_one_neg_two := by
      rw [D, WeierstrassCurve.Affine.Point.neg_some]
      simp only [WeierstrassCurve.Affine.Point.some.injEq]
      norm_num [WeierstrassCurve.Affine.negY, curve]
    have hsub :
        (.some u y hP : curve.toAffine.Point) - D =
          .some
            (curve.toAffine.addX u (-1)
              (curve.toAffine.slope u (-1) y (-2)))
            (curve.toAffine.addY u (-1) y
              (curve.toAffine.slope u (-1) y (-2))) hsum := by
      rw [sub_eq_add_neg, hnegD]
      exact WeierstrassCurve.Affine.Point.add_of_X_ne huD
    apply decompose_of_sub_eq_some hsub
    · rw [haddXsq]
      exact pow_ne_zero 2
        (div_ne_zero hnumerator (mul_ne_zero huplus hz0))
    · refine ⟨w, ?_⟩
      simpa [pow_two] using haddXsq

private lemma decompose_three_class
    {u y z : ℚ} (hu0 : u ≠ 0)
    (hP : curve.toAffine.Nonsingular u y)
    (hu : u = 3 * z ^ 2) :
    ∃ Q : curve.toAffine.Point,
      .some u y hP = F + (2 : ℕ) • Q := by
  have hcurve := curve_equation_of_nonsingular hP
  rcases eq_or_ne u 3 with huF | huF
  · clear hu
    subst u
    have hySq : y ^ 2 = (6 : ℚ) ^ 2 := by
      norm_num at hcurve ⊢
      exact hcurve
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hySq with hy | hy
    · subst y
      refine ⟨0, ?_⟩
      simp [F]
    · have hy' : y = -6 := by simpa using hy
      subst y
      have hpoint :
          (.some 3 (-6) hP : curve.toAffine.Point) = -F := by
        rw [F, WeierstrassCurve.Affine.Point.neg_some]
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        norm_num [WeierstrassCurve.Affine.negY, curve]
      refine ⟨-F, ?_⟩
      rw [hpoint]
      simp only [two_nsmul]
      abel
  · have hz0 : z ≠ 0 := by
      intro hz
      rw [hz] at hu
      norm_num at hu
      exact hu0 hu
    have huminus : u - 3 ≠ 0 := by
      intro h
      apply huF
      linarith
    have hslope :
        curve.toAffine.slope u 3 y (-6) = (y + 6) / (u - 3) := by
      simp [WeierstrassCurve.Affine.slope, huF]
    have haddX :
        curve.toAffine.addX u 3
            (curve.toAffine.slope u 3 y (-6)) =
          ((y + 6) / (u - 3)) ^ 2 - u - 5 := by
      rw [hslope]
      simp only [WeierstrassCurve.Affine.addX]
      norm_num [curve]
      ring
    have hnumerator : -6 * u - 3 * y ≠ 0 := by
      intro hzero
      have hy : y = -2 * u := by linarith
      have hfactor : u * ((u + 1) * (u - 3)) = 0 := by
        rw [hy] at hcurve
        nlinarith [hcurve]
      rcases mul_eq_zero.mp hfactor with hu' | hfactor
      · exact hu0 hu'
      rcases mul_eq_zero.mp hfactor with hleft | hright
      · have huminusone : u = -1 := by linarith
        rw [huminusone] at hu
        nlinarith [sq_nonneg z]
      · apply huF
        linarith
    let w : ℚ := (-6 * u - 3 * y) / ((u - 3) * (3 * z))
    have haddXsq :
        curve.toAffine.addX u 3
            (curve.toAffine.slope u 3 y (-6)) = w ^ 2 := by
      rw [haddX]
      dsimp [w]
      field_simp [huminus, hz0]
      nlinarith [hcurve, hu]
    let hsum : curve.toAffine.Nonsingular
        (curve.toAffine.addX u 3
          (curve.toAffine.slope u 3 y (-6)))
        (curve.toAffine.addY u 3 y
          (curve.toAffine.slope u 3 y (-6))) :=
      WeierstrassCurve.Affine.nonsingular_add hP nonsingular_three_neg_six
        (fun h ↦ huF h.1)
    have hnegF :
        -F = .some 3 (-6) nonsingular_three_neg_six := by
      rw [F, WeierstrassCurve.Affine.Point.neg_some]
      simp only [WeierstrassCurve.Affine.Point.some.injEq]
      norm_num [WeierstrassCurve.Affine.negY, curve]
    have hsub :
        (.some u y hP : curve.toAffine.Point) - F =
          .some
            (curve.toAffine.addX u 3
              (curve.toAffine.slope u 3 y (-6)))
            (curve.toAffine.addY u 3 y
              (curve.toAffine.slope u 3 y (-6))) hsum := by
      rw [sub_eq_add_neg, hnegF]
      exact WeierstrassCurve.Affine.Point.add_of_X_ne huF
    apply decompose_of_sub_eq_some hsub
    · rw [haddXsq]
      exact pow_ne_zero 2
        (div_ne_zero hnumerator
          (mul_ne_zero huminus (mul_ne_zero (by norm_num) hz0)))
    · refine ⟨w, ?_⟩
      simpa [pow_two] using haddXsq

/-- Every rational point lies in one of four explicit cosets of twice the
rational point group. -/
theorem four_doubling_cosets (P : curve.toAffine.Point) :
    (∃ Q : curve.toAffine.Point, P = (2 : ℕ) • Q) ∨
      (∃ Q : curve.toAffine.Point, P = D + (2 : ℕ) • Q) ∨
      (∃ Q : curve.toAffine.Point, P = F + (2 : ℕ) • Q) ∨
      (∃ Q : curve.toAffine.Point, P = T + (2 : ℕ) • Q) := by
  cases P with
  | zero =>
    left
    exact ⟨0, rfl⟩
  | some u y hP =>
    have hcurve := curve_equation_of_nonsingular hP
    rcases eq_or_ne u 0 with rfl | hu0
    · have hy : y = 0 := by
        norm_num at hcurve
        nlinarith [sq_nonneg y]
      subst y
      right; right; right
      refine ⟨0, ?_⟩
      simp [T]
    · rcases curve_abscissa_squareclass hu0 hcurve with
        ⟨z, hu⟩ | ⟨z, hu⟩ | ⟨z, hu⟩ | ⟨z, hu⟩
      · left
        obtain ⟨Q, hQ⟩ :=
          double_of_square_abscissa hu0 hP ⟨z, by simpa [pow_two] using hu⟩
        exact ⟨Q, hQ.symm⟩
      · right; left
        exact decompose_neg_one_class hu0 hP hu
      · right; right; left
        exact decompose_three_class hu0 hP hu
      · right; right; right
        exact decompose_neg_three_class hu0 hP hu

/-- The image of multiplication by two on the rational point group. -/
abbrev doublingRange : AddSubgroup curve.toAffine.Point :=
  (nsmulAddMonoidHom (α := curve.toAffine.Point) 2).range

private def doublingRepresentative : Fin 4 → curve.toAffine.Point
  | 0 => 0
  | 1 => D
  | 2 => F
  | 3 => T

private lemma doubling_quotient_surjective :
    Function.Surjective
      (fun i : Fin 4 ↦
        QuotientAddGroup.mk' doublingRange (doublingRepresentative i)) := by
  intro c
  obtain ⟨P, rfl⟩ := QuotientAddGroup.mk'_surjective doublingRange c
  rcases four_doubling_cosets P with
      ⟨Q, hQ⟩ | ⟨Q, hQ⟩ | ⟨Q, hQ⟩ | ⟨Q, hQ⟩
  · refine ⟨0, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm
  · refine ⟨1, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm
  · refine ⟨2, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
    refine ⟨(2 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
    simpa [doublingRepresentative] using hQ.symm
  · refine ⟨3, (QuotientAddGroup.mk'_eq_mk' doublingRange).mpr ?_⟩
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

/-- The multiplication-by-two index is at most four. -/
theorem doubling_index_le_four : doublingRange.index ≤ 4 := by
  rw [AddSubgroup.index_eq_card]
  exact (Nat.card_le_card_of_surjective _
    doubling_quotient_surjective).trans_eq (by simp)

private lemma double_T : (2 : ℕ) • T = 0 := by
  simp only [two_nsmul]
  rw [T]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY, curve]

private lemma double_A : (2 : ℕ) • A = 0 := by
  simp only [two_nsmul]
  rw [A]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY, curve]

private lemma double_B : (2 : ℕ) • B = 0 := by
  simp only [two_nsmul]
  rw [B]
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  norm_num [WeierstrassCurve.Affine.negY, curve]

private def fourToTwoTorsion :
    Fin 4 → {P : curve.toAffine.Point // (2 : ℕ) • P = 0}
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨T, double_T⟩
  | 2 => ⟨A, double_A⟩
  | 3 => ⟨B, double_B⟩

private lemma fourToTwoTorsion_injective :
    Function.Injective fourToTwoTorsion := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [fourToTwoTorsion, T, A, B] at hij ⊢
  all_goals norm_num at hij

/-- The curve has exactly four rational points killed by two. -/
theorem two_torsion_card_eq_four :
    Nat.card {P : curve.toAffine.Point // (2 : ℕ) • P = 0} = 4 := by
  letI : Finite {P : curve.toAffine.Point // (2 : ℕ) • P = 0} :=
    MazurTorsion.finite_two_torsion curve
  apply le_antisymm
  · change Set.ncard {P : curve.toAffine.Point | (2 : ℕ) • P = 0} ≤ 4
    exact MazurTorsion.ncard_two_torsion_le_four curve
  · simpa using
      (Nat.card_le_card_of_injective fourToTwoTorsion
        fourToTwoTorsion_injective)

/-- The rational point group has Mordell--Weil rank zero. -/
theorem point_rank_zero :
    Module.finrank ℤ curve.toAffine.Point = 0 := by
  letI : AddGroup.FG curve.toAffine.Point := point_fg
  have hker :
      Nat.card
          (nsmulAddMonoidHom (α := curve.toAffine.Point) 2).ker =
        4 := by
    change Nat.card
      {P : curve.toAffine.Point // (2 : ℕ) • P = 0} = 4
    exact two_torsion_card_eq_four
  have hformula :=
    AddSubgroup.index_range_nsmul_of_fg curve.toAffine.Point
      (by norm_num : (2 : ℕ) ≠ 0)
  rw [hker] at hformula
  have hpow : 2 ^ Module.finrank ℤ curve.toAffine.Point ≤ 1 := by
    have := doubling_index_le_four
    change
      (nsmulAddMonoidHom (α := curve.toAffine.Point) 2).range.index ≤ 4 at this
    omega
  have hpowequal : 2 ^ Module.finrank ℤ curve.toAffine.Point = 1 :=
    le_antisymm hpow
      (Nat.one_le_pow _ _ (by norm_num))
  simpa using hpowequal

/-- All rational points on the curve are torsion, hence the rational point
group is finite. -/
theorem point_finite : Finite curve.toAffine.Point := by
  letI : AddGroup.FG curve.toAffine.Point := point_fg
  letI : Module.Finite ℤ curve.toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr point_fg
  have hmoduleTorsion : Module.IsTorsion ℤ curve.toAffine.Point :=
    (Module.finrank_eq_zero_iff_isTorsion (R := ℤ)).mp point_rank_zero
  exact AddCommGroup.finite_of_fg_torsion curve.toAffine.Point
    (AddMonoid.isTorsion_iff_isTorsion_int.mpr hmoduleTorsion)









end MazurTorsion.ExceptionalCubic

end

theorem solution :
    Finite (⟨0, 2, 0, -3, 0⟩ : WeierstrassCurve ℚ).toAffine.Point :=
  MazurTorsion.ExceptionalCubic.point_finite
#print axioms solution
