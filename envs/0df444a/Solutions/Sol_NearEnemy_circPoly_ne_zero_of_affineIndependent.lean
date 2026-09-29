-- Prove2me | solution 1 for NearEnemy.circPoly_ne_zero_of_affineIndependent
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-18T15:06:28.664004+00:00
-- url     : https://prove2.me/submissions/7e506068-f466-48d0-81c5-3bd5a9e1473c

import Mathlib
import Definitions.Def_NearEnemyDefs
import Theorems.Thm_NearEnemy_eval_innerPoly
import Theorems.Thm_NearEnemy_innerPoly_ne_zero

universe u_1
open scoped RealInnerProductSpace
open scoped Classical
open MvPolynomial
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]
open NearEnemy
namespace NearEnemy

/-- **Separating row**: four pairwise distinct points admit a row vector
whose inner products with them are pairwise distinct.  Polynomial
nonvanishing over the six difference forms. -/
theorem exists_row_pairwise_ne {a b c e : EuclideanSpace ℝ ι}
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e)
    (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) :
    ∃ v : EuclideanSpace ℝ ι,
      ⟪v, a⟫ ≠ ⟪v, b⟫ ∧ ⟪v, a⟫ ≠ ⟪v, c⟫ ∧ ⟪v, a⟫ ≠ ⟪v, e⟫ ∧
      ⟪v, b⟫ ≠ ⟪v, c⟫ ∧ ⟪v, b⟫ ≠ ⟪v, e⟫ ∧ ⟪v, c⟫ ≠ ⟪v, e⟫ := by
  set P : MvPolynomial (Fin 2 × ι) ℝ :=
    innerPoly 0 (a - b) * innerPoly 0 (a - c) * innerPoly 0 (a - e) *
      innerPoly 0 (b - c) * innerPoly 0 (b - e) * innerPoly 0 (c - e) with hP
  have hPne : P ≠ 0 := by
    rw [hP]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (innerPoly_ne_zero hab) (innerPoly_ne_zero hac)) (innerPoly_ne_zero hae))
      (innerPoly_ne_zero hbc)) (innerPoly_ne_zero hbe)) (innerPoly_ne_zero hce)
  have hpoint : ∃ f : Fin 2 × ι → ℝ, eval f P ≠ 0 := by
    by_contra h
    push Not at h
    exact hPne (MvPolynomial.funext fun f ↦ by simpa using h f)
  obtain ⟨f, hf⟩ := hpoint
  rw [hP] at hf
  simp only [map_mul] at hf
  have h1 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul
    (left_ne_zero_of_mul (left_ne_zero_of_mul hf))))
  have h2 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul
    (left_ne_zero_of_mul (left_ne_zero_of_mul hf))))
  have h3 := right_ne_zero_of_mul (left_ne_zero_of_mul
    (left_ne_zero_of_mul (left_ne_zero_of_mul hf)))
  have h4 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hf))
  have h5 := right_ne_zero_of_mul (left_ne_zero_of_mul hf)
  have h6 := right_ne_zero_of_mul hf
  exact ⟨rowOf f 0,
    sub_ne_zero.mp (by simpa [eval_innerPoly, inner_sub_right] using h1),
    sub_ne_zero.mp (by simpa [eval_innerPoly, inner_sub_right] using h2),
    sub_ne_zero.mp (by simpa [eval_innerPoly, inner_sub_right] using h3),
    sub_ne_zero.mp (by simpa [eval_innerPoly, inner_sub_right] using h4),
    sub_ne_zero.mp (by simpa [eval_innerPoly, inner_sub_right] using h5),
    sub_ne_zero.mp (by simpa [eval_innerPoly, inner_sub_right] using h6)⟩

omit [Fintype ι] in
/-- A row-pair assignment extracts to the given rows. -/
theorem rowOf_pair (p q : EuclideanSpace ℝ ι) (k : Fin 2) :
    rowOf (fun ki ↦ ![p, q] ki.1 ki.2) k = ![p, q] k := rfl

end NearEnemy

open NearEnemy in
theorem solution {a b c e : EuclideanSpace ℝ ι}
    (hind : AffineIndependent ℝ ![a, b, c, e]) :
    circPoly a b c e ≠ 0 := by
  intro hcirc
  have hinj := hind.injective
  have hab : a ≠ b := fun h =>
    absurd (hinj (show ![a, b, c, e] 0 = ![a, b, c, e] 1 from h)) (by decide)
  have hac : a ≠ c := fun h =>
    absurd (hinj (show ![a, b, c, e] 0 = ![a, b, c, e] 2 from h)) (by decide)
  have hae : a ≠ e := fun h =>
    absurd (hinj (show ![a, b, c, e] 0 = ![a, b, c, e] 3 from h)) (by decide)
  have hbc : b ≠ c := fun h =>
    absurd (hinj (show ![a, b, c, e] 1 = ![a, b, c, e] 2 from h)) (by decide)
  have hbe : b ≠ e := fun h =>
    absurd (hinj (show ![a, b, c, e] 1 = ![a, b, c, e] 3 from h)) (by decide)
  have hce : c ≠ e := fun h =>
    absurd (hinj (show ![a, b, c, e] 2 = ![a, b, c, e] 3 from h)) (by decide)
  obtain ⟨v, hd₁₂, hd₁₃, hd₁₄, hd₂₃, hd₂₄, hd₃₄⟩ :=
    exists_row_pairwise_ne hab hac hae hbc hbe hce
  set m : EuclideanSpace ℝ ι :=
    ((⟪v, c⟫ - ⟪v, e⟫) * (⟪v, b⟫ - ⟪v, c⟫) * (⟪v, b⟫ - ⟪v, e⟫)) • a +
      (-((⟪v, c⟫ - ⟪v, e⟫) * (⟪v, a⟫ - ⟪v, c⟫) * (⟪v, a⟫ - ⟪v, e⟫))) • b +
      ((⟪v, b⟫ - ⟪v, e⟫) * (⟪v, a⟫ - ⟪v, b⟫) * (⟪v, a⟫ - ⟪v, e⟫)) • c +
      (-((⟪v, b⟫ - ⟪v, c⟫) * (⟪v, a⟫ - ⟪v, b⟫) * (⟪v, a⟫ - ⟪v, c⟫))) • e
    with hmdef
  have hE1 := congrArg (eval fun ki ↦ ![v, m] ki.1 ki.2) hcirc
  have hE2 := congrArg (eval fun ki ↦ ![v, (2 : ℝ) • m] ki.1 ki.2) hcirc
  rw [map_zero] at hE1 hE2
  simp only [circPoly, map_add, map_sub, map_mul, map_pow, eval_innerPoly,
    rowOf_pair, Matrix.cons_val_zero, Matrix.cons_val_one,
    real_inner_smul_left] at hE1 hE2
  -- The parabola determinant, extracted from two scalings of the second row.
  have hP : ((⟪v, c⟫ - ⟪v, e⟫) * (⟪v, b⟫ - ⟪v, c⟫) * (⟪v, b⟫ - ⟪v, e⟫)) * ⟪m, a⟫
      + (-((⟪v, c⟫ - ⟪v, e⟫) * (⟪v, a⟫ - ⟪v, c⟫) * (⟪v, a⟫ - ⟪v, e⟫))) * ⟪m, b⟫
      + ((⟪v, b⟫ - ⟪v, e⟫) * (⟪v, a⟫ - ⟪v, b⟫) * (⟪v, a⟫ - ⟪v, e⟫)) * ⟪m, c⟫
      + (-((⟪v, b⟫ - ⟪v, c⟫) * (⟪v, a⟫ - ⟪v, b⟫) * (⟪v, a⟫ - ⟪v, c⟫))) * ⟪m, e⟫
      = 0 := by
    linear_combination (4 / 3 : ℝ) * hE1 - (1 / 6 : ℝ) * hE2
  have hmm : ⟪m, m⟫ = (0 : ℝ) := by
    nth_rewrite 2 [hmdef]
    rw [inner_add_right, inner_add_right, inner_add_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right]
    linear_combination hP
  have hm0 : m = 0 := inner_self_eq_zero.mp hmm
  rw [hmdef] at hm0
  -- Affine independence kills the Vandermonde weights, but the first one is
  -- a product of nonzero differences.
  have hw := affineIndependent_iff.mp hind Finset.univ
    ![((⟪v, c⟫ - ⟪v, e⟫) * (⟪v, b⟫ - ⟪v, c⟫) * (⟪v, b⟫ - ⟪v, e⟫)),
      -((⟪v, c⟫ - ⟪v, e⟫) * (⟪v, a⟫ - ⟪v, c⟫) * (⟪v, a⟫ - ⟪v, e⟫)),
      ((⟪v, b⟫ - ⟪v, e⟫) * (⟪v, a⟫ - ⟪v, b⟫) * (⟪v, a⟫ - ⟪v, e⟫)),
      -((⟪v, b⟫ - ⟪v, c⟫) * (⟪v, a⟫ - ⟪v, b⟫) * (⟪v, a⟫ - ⟪v, c⟫))]
    (by simp [Fin.sum_univ_four]; ring)
    (by simpa [Fin.sum_univ_four] using hm0)
    0 (Finset.mem_univ _)
  simp only [Matrix.cons_val_zero] at hw
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hd₃₄)
    (sub_ne_zero.mpr hd₂₃)) (sub_ne_zero.mpr hd₂₄) hw
