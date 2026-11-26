-- Prove2me | solution 1 for LogLogJam.lemma_4_8
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:13:38.63563+00:00
-- url     : https://prove2.me/submissions/4eb5c094-8657-478c-bdce-aec46a7a9cef

import Definitions.Def_LogLogJam_VK

open Matrix LogLogJam
open scoped ComplexOrder

theorem solution (lam θ : ℝ) (hlam : 1 ≤ lam) (k : ℕ) :
    InSiegelDisk ((((lam - 1) / (lam + 1) : ℝ) * Complex.exp (2 * θ * Complex.I)) •
        (1 : Matrix (Fin k) (Fin k) ℂ)) ∧
      VK ((((lam - 1) / (lam + 1) : ℝ) * Complex.exp (2 * θ * Complex.I)) •
        (1 : Matrix (Fin k) (Fin k) ℂ)) = VsqK lam θ k := by
  let a := (lam - 1) / (lam + 1)
  let d := 1 - a ^ 2
  let z : ℂ := (a : ℂ) * Complex.exp (((2 * θ : ℝ) : ℂ) * Complex.I)
  let M (x : ℂ) : Matrix (Fin k) (Fin k) ℂ := diagonal (fun _ => x)
  have hL : 0 < lam := by linarith
  have hLp : 0 < lam + 1 := by linarith
  have hdEq : d = 4 * lam / (lam + 1)^2 := by
    dsimp [d, a]
    field_simp
    ring
  have hd : 0 < d := by rw [hdEq]; positivity
  have hzsq : Complex.normSq z = a^2 := by
    simp only [z, Complex.normSq_eq_norm_sq, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one, sq_abs]
  have hzRe : z.re = a * Real.cos (2 * θ) := by
    simp only [z, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_ofReal_mul_I_re]
  have hzIm : z.im = a * Real.sin (2 * θ) := by
    simp only [z, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.exp_ofReal_mul_I_im]
  have hK : ((((lam - 1) / (lam + 1) : ℝ) * Complex.exp (2 * θ * Complex.I)) •
      (1 : Matrix (Fin k) (Fin k) ℂ)) = M z := by
    simp [M, Matrix.smul_one_eq_diagonal, z, a]
  have hMmul (x y : ℂ) : M x * M y = M (x * y) := diagonal_mul_diagonal _ _
  have hMstar : (M z)ᴴ = M (star z) := diagonal_conjTranspose _
  have hm1 : star z * z = ((a ^ 2 : ℝ) : ℂ) := by
    rw [← hzsq]; exact Complex.normSq_eq_conj_mul_self.symm
  have hleft : (M z)ᴴ * M z = M ((a ^ 2 : ℝ) : ℂ) := by rw [hMstar, hMmul, hm1]
  have hright : M z * (M z)ᴴ = M ((a ^ 2 : ℝ) : ℂ) := by
    rw [hMstar, hMmul, mul_comm z, hm1]
  have hdiff : 1 - M ((a ^ 2 : ℝ) : ℂ) = M (d : ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [M, d, h]
  have hInv : (M (d : ℂ))⁻¹ = M ((d⁻¹ : ℝ) : ℂ) := by
    apply Matrix.inv_eq_right_inv
    rw [hMmul, ← Complex.ofReal_mul, mul_inv_cancel₀ hd.ne', Complex.ofReal_one]
    exact diagonal_one
  rw [hK]
  constructor
  · refine ⟨diagonal_transpose _, ?_⟩
    rw [hright, hdiff]
    apply Matrix.PosDef.diagonal
    intro i
    exact_mod_cast hd
  · unfold VK
    rw [hleft, hright, hdiff, hInv, hMmul, hMmul]
    have hq : a^2 * d⁻¹ = (lam - 1)^2 / (4 * lam) := by
      rw [hdEq]
      dsimp [a]
      field_simp
    have hr : d⁻¹ * a = (lam^2 - 1) / (4 * lam) := by
      rw [hdEq]
      dsimp [a]
      field_simp
      ring
    rw [← Complex.ofReal_mul]
    set q := a^2 * d⁻¹
    ext ⟨u,i⟩ ⟨v,j⟩
    fin_cases u <;> fin_cases v <;> by_cases hij : i = j
    all_goals simp [Matrix.of_apply, M, VsqK, Vsq, rot, Matrix.kroneckerMap_apply,
      Matrix.diagonal_apply, hij, Ne.symm, Matrix.vecMul, dotProduct,
      Matrix.transpose_apply, Fin.sum_univ_two, hzRe, hzIm, Complex.mul_re,
      Complex.mul_im, ← mul_assoc, hr]
    all_goals simp only [hq, Real.cos_two_mul', Real.sin_two_mul]
    all_goals (field_simp; ring_nf)
    all_goals
      rw [show Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 by linarith [Real.sin_sq_add_cos_sq θ]]
      ring
