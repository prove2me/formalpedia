-- Prove2me | solution 1 for GiuntiStudenikin2015.mixing_matrix_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T09:50:58.135352+00:00
-- url     : https://prove2.me/submissions/304158d5-1822-44c9-96e7-20d8de3b3642

import Mathlib
import Definitions.Def_GiuntiStudenikin2015_oscillation

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


theorem gs15_d00 (θ12 θ13 θ23 δ : ℝ) :
    GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ 0 0 =
      (Real.cos θ12 : ℂ) * (Real.cos θ13 : ℂ) := rfl

theorem gs15_d01 (θ12 θ13 θ23 δ : ℝ) :
    GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ 0 1 =
      (Real.sin θ12 : ℂ) * (Real.cos θ13 : ℂ) := rfl

theorem gs15_d02 (θ12 θ13 θ23 δ : ℝ) :
    GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ 0 2 =
      (Real.sin θ13 : ℂ) * Complex.exp (-(Complex.I * (δ : ℂ))) := rfl

theorem gs15_d10 (θ12 θ13 θ23 δ : ℝ) :
    GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ 1 0 =
      -(Real.sin θ12 : ℂ) * (Real.cos θ23 : ℂ) - (Real.cos θ12 : ℂ) * (Real.sin θ23 : ℂ) * (Real.sin θ13 : ℂ) * Complex.exp (Complex.I * (δ : ℂ)) := rfl

theorem gs15_d11 (θ12 θ13 θ23 δ : ℝ) :
    GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ 1 1 =
      (Real.cos θ12 : ℂ) * (Real.cos θ23 : ℂ) - (Real.sin θ12 : ℂ) * (Real.sin θ23 : ℂ) * (Real.sin θ13 : ℂ) * Complex.exp (Complex.I * (δ : ℂ)) := rfl

theorem gs15_d12 (θ12 θ13 θ23 δ : ℝ) :
    GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ 1 2 =
      (Real.sin θ23 : ℂ) * (Real.cos θ13 : ℂ) := rfl

theorem gs15_d20 (θ12 θ13 θ23 δ : ℝ) :
    GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ 2 0 =
      (Real.sin θ12 : ℂ) * (Real.sin θ23 : ℂ) - (Real.cos θ12 : ℂ) * (Real.cos θ23 : ℂ) * (Real.sin θ13 : ℂ) * Complex.exp (Complex.I * (δ : ℂ)) := rfl

theorem gs15_d21 (θ12 θ13 θ23 δ : ℝ) :
    GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ 2 1 =
      -(Real.cos θ12 : ℂ) * (Real.sin θ23 : ℂ) - (Real.sin θ12 : ℂ) * (Real.cos θ23 : ℂ) * (Real.sin θ13 : ℂ) * Complex.exp (Complex.I * (δ : ℂ)) := rfl

theorem gs15_d22 (θ12 θ13 θ23 δ : ℝ) :
    GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ 2 2 =
      (Real.cos θ23 : ℂ) * (Real.cos θ13 : ℂ) := rfl

theorem gs15_star_real (x : ℝ) : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x

theorem gs15_hf (δ : ℝ) :
    Complex.exp (-(Complex.I * (δ : ℂ))) = star (Complex.exp (Complex.I * (δ : ℂ))) := by
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring_nf

theorem gs15_hE (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) * star (Complex.exp (Complex.I * (x : ℂ))) = 1 := by
  rw [show Complex.I * (x : ℂ) = (x : ℂ) * Complex.I from mul_comm _ _, Complex.star_def,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

theorem gs15_hE' (x : ℝ) :
    star (Complex.exp (Complex.I * (x : ℂ))) * Complex.exp (Complex.I * (x : ℂ)) = 1 :=
  (mul_comm _ _).trans (gs15_hE x)

theorem gs15_hE'' (x : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * (x : ℂ))) * Complex.exp (Complex.I * (x : ℂ)) = 1 := by
  exact gs15_hE' x

theorem gs15_pyth (x : ℝ) : (Real.sin x : ℂ) ^ 2 + (Real.cos x : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.sin_sq_add_cos_sq x

theorem gs15_sms_00 (θ12 θ13 θ23 δ : ℝ) :
    (star (GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) *
      GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) 0 0 = 1 := by
  have h1 := gs15_pyth θ12
  have h2 := gs15_pyth θ13
  have h3 := gs15_pyth θ23
  have hE := gs15_hE δ
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, gs15_d00, gs15_d01, gs15_d02,
    gs15_d10, gs15_d11, gs15_d12, gs15_d20, gs15_d21, gs15_d22, gs15_hf, star_sub, star_add,
    star_neg, star_mul', star_star, gs15_star_real]
  generalize star (Complex.exp (Complex.I * (δ : ℂ))) = f at hE ⊢
  generalize Complex.exp (Complex.I * (δ : ℂ)) = e at hE ⊢
  generalize (Real.cos θ12 : ℂ) = c1 at h1 ⊢
  generalize (Real.sin θ12 : ℂ) = s1 at h1 ⊢
  generalize (Real.cos θ13 : ℂ) = c2 at h2 ⊢
  generalize (Real.sin θ13 : ℂ) = s2 at h2 ⊢
  generalize (Real.cos θ23 : ℂ) = c3 at h3 ⊢
  generalize (Real.sin θ23 : ℂ) = s3 at h3 ⊢
  linear_combination (s2^2*s3^2*e*f + s2^2*c3^2*e*f + c2^2) * h1 + (1 - s1^2) * h2 + (s2^2*e*f + s1^2 - s1^2*s2^2*e*f) * h3 + (s2^2 - s1^2*s2^2) * hE

theorem gs15_sms_01 (θ12 θ13 θ23 δ : ℝ) :
    (star (GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) *
      GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) 0 1 = 0 := by
  have h1 := gs15_pyth θ12
  have h2 := gs15_pyth θ13
  have h3 := gs15_pyth θ23
  have hE := gs15_hE δ
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, gs15_d00, gs15_d01, gs15_d02,
    gs15_d10, gs15_d11, gs15_d12, gs15_d20, gs15_d21, gs15_d22, gs15_hf, star_sub, star_add,
    star_neg, star_mul', star_star, gs15_star_real]
  generalize star (Complex.exp (Complex.I * (δ : ℂ))) = f at hE ⊢
  generalize Complex.exp (Complex.I * (δ : ℂ)) = e at hE ⊢
  generalize (Real.cos θ12 : ℂ) = c1 at h1 ⊢
  generalize (Real.sin θ12 : ℂ) = s1 at h1 ⊢
  generalize (Real.cos θ13 : ℂ) = c2 at h2 ⊢
  generalize (Real.sin θ13 : ℂ) = s2 at h2 ⊢
  generalize (Real.cos θ23 : ℂ) = c3 at h3 ⊢
  generalize (Real.sin θ23 : ℂ) = s3 at h3 ⊢
  linear_combination (c1*s1) * h2 + (-c1*s1 + c1*s1*s2^2*e*f) * h3 + (c1*s1*s2^2) * hE

theorem gs15_sms_02 (θ12 θ13 θ23 δ : ℝ) :
    (star (GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) *
      GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) 0 2 = 0 := by
  have h1 := gs15_pyth θ12
  have h2 := gs15_pyth θ13
  have h3 := gs15_pyth θ23
  have hE := gs15_hE δ
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, gs15_d00, gs15_d01, gs15_d02,
    gs15_d10, gs15_d11, gs15_d12, gs15_d20, gs15_d21, gs15_d22, gs15_hf, star_sub, star_add,
    star_neg, star_mul', star_star, gs15_star_real]
  generalize star (Complex.exp (Complex.I * (δ : ℂ))) = f at hE ⊢
  generalize Complex.exp (Complex.I * (δ : ℂ)) = e at hE ⊢
  generalize (Real.cos θ12 : ℂ) = c1 at h1 ⊢
  generalize (Real.sin θ12 : ℂ) = s1 at h1 ⊢
  generalize (Real.cos θ13 : ℂ) = c2 at h2 ⊢
  generalize (Real.sin θ13 : ℂ) = s2 at h2 ⊢
  generalize (Real.cos θ23 : ℂ) = c3 at h3 ⊢
  generalize (Real.sin θ23 : ℂ) = s3 at h3 ⊢
  linear_combination (-c1*c2*s2*f) * h3

theorem gs15_sms_10 (θ12 θ13 θ23 δ : ℝ) :
    (star (GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) *
      GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) 1 0 = 0 := by
  have h1 := gs15_pyth θ12
  have h2 := gs15_pyth θ13
  have h3 := gs15_pyth θ23
  have hE := gs15_hE δ
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, gs15_d00, gs15_d01, gs15_d02,
    gs15_d10, gs15_d11, gs15_d12, gs15_d20, gs15_d21, gs15_d22, gs15_hf, star_sub, star_add,
    star_neg, star_mul', star_star, gs15_star_real]
  generalize star (Complex.exp (Complex.I * (δ : ℂ))) = f at hE ⊢
  generalize Complex.exp (Complex.I * (δ : ℂ)) = e at hE ⊢
  generalize (Real.cos θ12 : ℂ) = c1 at h1 ⊢
  generalize (Real.sin θ12 : ℂ) = s1 at h1 ⊢
  generalize (Real.cos θ13 : ℂ) = c2 at h2 ⊢
  generalize (Real.sin θ13 : ℂ) = s2 at h2 ⊢
  generalize (Real.cos θ23 : ℂ) = c3 at h3 ⊢
  generalize (Real.sin θ23 : ℂ) = s3 at h3 ⊢
  linear_combination (c1*s1) * h2 + (-c1*s1 + c1*s1*s2^2*e*f) * h3 + (c1*s1*s2^2) * hE

theorem gs15_sms_11 (θ12 θ13 θ23 δ : ℝ) :
    (star (GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) *
      GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) 1 1 = 1 := by
  have h1 := gs15_pyth θ12
  have h2 := gs15_pyth θ13
  have h3 := gs15_pyth θ23
  have hE := gs15_hE δ
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, gs15_d00, gs15_d01, gs15_d02,
    gs15_d10, gs15_d11, gs15_d12, gs15_d20, gs15_d21, gs15_d22, gs15_hf, star_sub, star_add,
    star_neg, star_mul', star_star, gs15_star_real]
  generalize star (Complex.exp (Complex.I * (δ : ℂ))) = f at hE ⊢
  generalize Complex.exp (Complex.I * (δ : ℂ)) = e at hE ⊢
  generalize (Real.cos θ12 : ℂ) = c1 at h1 ⊢
  generalize (Real.sin θ12 : ℂ) = s1 at h1 ⊢
  generalize (Real.cos θ13 : ℂ) = c2 at h2 ⊢
  generalize (Real.sin θ13 : ℂ) = s2 at h2 ⊢
  generalize (Real.cos θ23 : ℂ) = c3 at h3 ⊢
  generalize (Real.sin θ23 : ℂ) = s3 at h3 ⊢
  linear_combination (s3^2 + c3^2) * h1 + (s1^2) * h2 + (1 - s1^2 + s1^2*s2^2*e*f) * h3 + (s1^2*s2^2) * hE

theorem gs15_sms_12 (θ12 θ13 θ23 δ : ℝ) :
    (star (GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) *
      GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) 1 2 = 0 := by
  have h1 := gs15_pyth θ12
  have h2 := gs15_pyth θ13
  have h3 := gs15_pyth θ23
  have hE := gs15_hE δ
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, gs15_d00, gs15_d01, gs15_d02,
    gs15_d10, gs15_d11, gs15_d12, gs15_d20, gs15_d21, gs15_d22, gs15_hf, star_sub, star_add,
    star_neg, star_mul', star_star, gs15_star_real]
  generalize star (Complex.exp (Complex.I * (δ : ℂ))) = f at hE ⊢
  generalize Complex.exp (Complex.I * (δ : ℂ)) = e at hE ⊢
  generalize (Real.cos θ12 : ℂ) = c1 at h1 ⊢
  generalize (Real.sin θ12 : ℂ) = s1 at h1 ⊢
  generalize (Real.cos θ13 : ℂ) = c2 at h2 ⊢
  generalize (Real.sin θ13 : ℂ) = s2 at h2 ⊢
  generalize (Real.cos θ23 : ℂ) = c3 at h3 ⊢
  generalize (Real.sin θ23 : ℂ) = s3 at h3 ⊢
  linear_combination (-s1*c2*s2*f) * h3

theorem gs15_sms_20 (θ12 θ13 θ23 δ : ℝ) :
    (star (GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) *
      GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) 2 0 = 0 := by
  have h1 := gs15_pyth θ12
  have h2 := gs15_pyth θ13
  have h3 := gs15_pyth θ23
  have hE := gs15_hE δ
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, gs15_d00, gs15_d01, gs15_d02,
    gs15_d10, gs15_d11, gs15_d12, gs15_d20, gs15_d21, gs15_d22, gs15_hf, star_sub, star_add,
    star_neg, star_mul', star_star, gs15_star_real]
  generalize star (Complex.exp (Complex.I * (δ : ℂ))) = f at hE ⊢
  generalize Complex.exp (Complex.I * (δ : ℂ)) = e at hE ⊢
  generalize (Real.cos θ12 : ℂ) = c1 at h1 ⊢
  generalize (Real.sin θ12 : ℂ) = s1 at h1 ⊢
  generalize (Real.cos θ13 : ℂ) = c2 at h2 ⊢
  generalize (Real.sin θ13 : ℂ) = s2 at h2 ⊢
  generalize (Real.cos θ23 : ℂ) = c3 at h3 ⊢
  generalize (Real.sin θ23 : ℂ) = s3 at h3 ⊢
  linear_combination (-c1*c2*s2*e) * h3

theorem gs15_sms_21 (θ12 θ13 θ23 δ : ℝ) :
    (star (GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) *
      GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) 2 1 = 0 := by
  have h1 := gs15_pyth θ12
  have h2 := gs15_pyth θ13
  have h3 := gs15_pyth θ23
  have hE := gs15_hE δ
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, gs15_d00, gs15_d01, gs15_d02,
    gs15_d10, gs15_d11, gs15_d12, gs15_d20, gs15_d21, gs15_d22, gs15_hf, star_sub, star_add,
    star_neg, star_mul', star_star, gs15_star_real]
  generalize star (Complex.exp (Complex.I * (δ : ℂ))) = f at hE ⊢
  generalize Complex.exp (Complex.I * (δ : ℂ)) = e at hE ⊢
  generalize (Real.cos θ12 : ℂ) = c1 at h1 ⊢
  generalize (Real.sin θ12 : ℂ) = s1 at h1 ⊢
  generalize (Real.cos θ13 : ℂ) = c2 at h2 ⊢
  generalize (Real.sin θ13 : ℂ) = s2 at h2 ⊢
  generalize (Real.cos θ23 : ℂ) = c3 at h3 ⊢
  generalize (Real.sin θ23 : ℂ) = s3 at h3 ⊢
  linear_combination (-s1*c2*s2*e) * h3

theorem gs15_sms_22 (θ12 θ13 θ23 δ : ℝ) :
    (star (GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) *
      GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) 2 2 = 1 := by
  have h1 := gs15_pyth θ12
  have h2 := gs15_pyth θ13
  have h3 := gs15_pyth θ23
  have hE := gs15_hE δ
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.star_apply, gs15_d00, gs15_d01, gs15_d02,
    gs15_d10, gs15_d11, gs15_d12, gs15_d20, gs15_d21, gs15_d22, gs15_hf, star_sub, star_add,
    star_neg, star_mul', star_star, gs15_star_real]
  generalize star (Complex.exp (Complex.I * (δ : ℂ))) = f at hE ⊢
  generalize Complex.exp (Complex.I * (δ : ℂ)) = e at hE ⊢
  generalize (Real.cos θ12 : ℂ) = c1 at h1 ⊢
  generalize (Real.sin θ12 : ℂ) = s1 at h1 ⊢
  generalize (Real.cos θ13 : ℂ) = c2 at h2 ⊢
  generalize (Real.sin θ13 : ℂ) = s2 at h2 ⊢
  generalize (Real.cos θ23 : ℂ) = c3 at h3 ⊢
  generalize (Real.sin θ23 : ℂ) = s3 at h3 ⊢
  linear_combination (s3^2 + c3^2) * h2 + (1 - s2^2) * h3 + (s2^2) * hE

theorem gs15_diag (θ12 θ13 θ23 δ : ℝ) (i : Fin 3) :
    (star (GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) *
      GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) i i = 1 := by
  fin_cases i
  · exact gs15_sms_00 θ12 θ13 θ23 δ
  · exact gs15_sms_11 θ12 θ13 θ23 δ
  · exact gs15_sms_22 θ12 θ13 θ23 δ

theorem gs15_offdiag (θ12 θ13 θ23 δ : ℝ) (i j : Fin 3) (h : i ≠ j) :
    (star (GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) *
      GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ) i j = 0 := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl h
    | exact gs15_sms_01 θ12 θ13 θ23 δ
    | exact gs15_sms_02 θ12 θ13 θ23 δ
    | exact gs15_sms_10 θ12 θ13 θ23 δ
    | exact gs15_sms_12 θ12 θ13 θ23 δ
    | exact gs15_sms_20 θ12 θ13 θ23 δ
    | exact gs15_sms_21 θ12 θ13 θ23 δ

theorem gs15_dirac_unitary (θ12 θ13 θ23 δ : ℝ) :
    GiuntiStudenikin2015.diracMixing θ12 θ13 θ23 δ ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq]; exact gs15_diag θ12 θ13 θ23 δ i
  · rw [Matrix.one_apply_ne h]; exact gs15_offdiag θ12 θ13 θ23 δ i j h

theorem gs15_maj (l1 l2 : ℝ) :
    GiuntiStudenikin2015.majoranaPhases l1 l2 ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  unfold GiuntiStudenikin2015.majoranaPhases
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp [gs15_hE', gs15_hE'']

open GiuntiStudenikin2015 in
theorem solution (θ12 θ13 θ23 δ13 lam21 lam31 : ℝ)
    (h12 : 0 ≤ θ12 ∧ θ12 ≤ Real.pi / 2) (h13 : 0 ≤ θ13 ∧ θ13 ≤ Real.pi / 2)
    (h23 : 0 ≤ θ23 ∧ θ23 ≤ Real.pi / 2) (hδ : 0 ≤ δ13 ∧ δ13 < 2 * Real.pi) :
    diracMixing θ12 θ13 θ23 δ13 ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧
    diracMixing θ12 θ13 θ23 δ13 * majoranaPhases lam21 lam31 ∈
      Matrix.unitaryGroup (Fin 3) ℂ := by
  exact ⟨gs15_dirac_unitary θ12 θ13 θ23 δ13,
    mul_mem (gs15_dirac_unitary θ12 θ13 θ23 δ13) (gs15_maj lam21 lam31)⟩
