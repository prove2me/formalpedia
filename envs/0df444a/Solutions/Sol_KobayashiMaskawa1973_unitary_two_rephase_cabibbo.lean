-- Prove2me | solution 1 for KobayashiMaskawa1973.unitary_two_rephase_cabibbo
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T07:25:15.272552+00:00
-- url     : https://prove2.me/submissions/3489560a-4c7e-45e6-a320-cec31fb824b6

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open KobayashiMaskawa1973 Matrix in
theorem kmr_star_real (x : ℝ) : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x

open KobayashiMaskawa1973 Matrix in
theorem kmr_hE (δ : ℝ) :
    Complex.exp ((δ : ℂ) * Complex.I) * star (Complex.exp ((δ : ℂ) * Complex.I)) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

open KobayashiMaskawa1973 Matrix in
theorem kmr_pyth (x : ℝ) : (Real.sin x : ℂ) ^ 2 + (Real.cos x : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.sin_sq_add_cos_sq x

open KobayashiMaskawa1973 Matrix in
theorem kmr_polar (z : ℂ) :
    z * Complex.exp (((-(Complex.arg z) : ℝ) : ℂ) * Complex.I) = ((‖z‖ : ℝ) : ℂ) := by
  have h0 : (Complex.arg z : ℂ) * Complex.I + ((-(Complex.arg z) : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast; ring
  calc z * Complex.exp (((-(Complex.arg z) : ℝ) : ℂ) * Complex.I)
      = ((‖z‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg z : ℂ) * Complex.I) *
          Complex.exp (((-(Complex.arg z) : ℝ) : ℂ) * Complex.I) := by
        rw [Complex.norm_mul_exp_arg_mul_I]
    _ = ((‖z‖ : ℝ) : ℂ) := by rw [mul_assoc, ← Complex.exp_add, h0, Complex.exp_zero, mul_one]

open KobayashiMaskawa1973 Matrix in
theorem kmr_cs (u v : ℝ) (h : u ^ 2 + v ^ 2 = 1) :
    Real.cos (Complex.arg ((u : ℂ) + (v : ℂ) * Complex.I)) = u ∧
    Real.sin (Complex.arg ((u : ℂ) + (v : ℂ) * Complex.I)) = v := by
  set z : ℂ := (u : ℂ) + (v : ℂ) * Complex.I with hz
  have hre : z.re = u := by simp [hz]
  have him : z.im = v := by simp [hz]
  have hn2 : ‖z‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; linear_combination h
  have hn : ‖z‖ = 1 := by
    have h0 : 0 ≤ ‖z‖ := norm_nonneg z
    nlinarith
  have hc := Complex.norm_mul_cos_arg z
  have hs := Complex.norm_mul_sin_arg z
  rw [hn, one_mul] at hc hs
  exact ⟨hc.trans hre, hs.trans him⟩

open KobayashiMaskawa1973 Matrix in
theorem kmr_phase_mem (m : ℕ) (a : Fin m → ℝ) :
    phaseDiag a ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  unfold phaseDiag
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext k
  exact kmr_hE (a k)

open KobayashiMaskawa1973 Matrix in
theorem kmr_cab00 (θ : ℝ) : cabibboMatrix θ 0 0 = (Real.cos θ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_cab01 (θ : ℝ) : cabibboMatrix θ 0 1 = (Real.sin θ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_cab10 (θ : ℝ) : cabibboMatrix θ 1 0 = -(Real.sin θ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_cab11 (θ : ℝ) : cabibboMatrix θ 1 1 = (Real.cos θ : ℂ) := rfl

open KobayashiMaskawa1973 Matrix in
theorem kmr_cab_mem (θ : ℝ) : cabibboMatrix θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h := kmr_pyth θ
  have e00 : (star (cabibboMatrix θ) * cabibboMatrix θ) 0 0 = 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, kmr_cab00, kmr_cab01,
      kmr_cab10, kmr_cab11, star_neg, kmr_star_real]
    linear_combination h
  have e01 : (star (cabibboMatrix θ) * cabibboMatrix θ) 0 1 = 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, kmr_cab00, kmr_cab01,
      kmr_cab10, kmr_cab11, star_neg, kmr_star_real]
    ring
  have e10 : (star (cabibboMatrix θ) * cabibboMatrix θ) 1 0 = 0 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, kmr_cab00, kmr_cab01,
      kmr_cab10, kmr_cab11, star_neg, kmr_star_real]
    ring
  have e11 : (star (cabibboMatrix θ) * cabibboMatrix θ) 1 1 = 1 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, kmr_cab00, kmr_cab01,
      kmr_cab10, kmr_cab11, star_neg, kmr_star_real]
    linear_combination h
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using e00
  · simpa using e01
  · simpa using e10
  · simpa using e11

open KobayashiMaskawa1973 Matrix in
theorem solution (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ) :
    ∃ θ : ℝ, RephasingEquiv U (cabibboMatrix θ) := by
  set a : Fin 2 → ℝ := fun i => -(Complex.arg (U i 0)) with ha
  set U1 := phaseDiag a * U with hU1
  have hU1m : U1 ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ (kmr_phase_mem 2 a) hU
  have hc0 : ∀ i, U1 i 0 = ((‖U i 0‖ : ℝ) : ℂ) := by
    intro i
    simp only [hU1, phaseDiag, Matrix.diagonal_mul, ha]
    rw [mul_comm]
    exact kmr_polar _
  set x0 := ‖U 0 0‖ with hx0
  set x1 := ‖U 1 0‖ with hx1
  have hx : x0 ^ 2 + x1 ^ 2 = 1 := by
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hU1m) 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hc0, kmr_star_real,
      Matrix.one_apply_eq] at h
    have : ((x0 ^ 2 + x1 ^ 2 : ℝ) : ℂ) = 1 := by push_cast; linear_combination h
    exact_mod_cast this
  obtain ⟨hcos, hsin⟩ := kmr_cs x0 (-x1) (by linear_combination hx)
  set θ := Complex.arg ((x0 : ℂ) + ((-x1 : ℝ) : ℂ) * Complex.I) with hθ
  set A := cabibboMatrix θ with hA
  have hAm : A ∈ Matrix.unitaryGroup (Fin 2) ℂ := kmr_cab_mem θ
  set W := star A * U1 with hW
  have hWm : W ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ (Unitary.star_mem hAm) hU1m
  have hW00 : W 0 0 = 1 := by
    simp only [hW, hA, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hc0, kmr_cab00,
      kmr_cab01, kmr_cab10, kmr_cab11, star_neg, kmr_star_real, hcos, hsin]
    have : ((x0 ^ 2 + x1 ^ 2 : ℝ) : ℂ) = 1 := by rw [hx]; simp
    push_cast at this ⊢
    linear_combination this
  have hW10 : W 1 0 = 0 := by
    simp only [hW, hA, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hc0, kmr_cab00,
      kmr_cab01, kmr_cab10, kmr_cab11, star_neg, kmr_star_real, hcos, hsin]
    push_cast
    ring
  have hW01 : W 0 1 = 0 := by
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hWm) 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hW00, hW10] at h
    simp at h
    exact h
  set b : Fin 2 → ℝ := ![0, -(Complex.arg (W 1 1))] with hb
  set M := W * phaseDiag b with hM
  have hMm : M ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ hWm (kmr_phase_mem 2 b)
  have hM11 : M 1 1 = ((‖W 1 1‖ : ℝ) : ℂ) := by
    simp only [hM, phaseDiag, Matrix.mul_diagonal, hb]
    exact kmr_polar _
  have hM00 : M 0 0 = 1 := by
    simp [hM, phaseDiag, Matrix.mul_diagonal, hb, hW00]
  have hM01 : M 0 1 = 0 := by
    simp [hM, phaseDiag, Matrix.mul_diagonal, hb, hW01]
  have hM10 : M 1 0 = 0 := by
    simp [hM, phaseDiag, Matrix.mul_diagonal, hb, hW10]
  have hy : ‖W 1 1‖ = 1 := by
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hMm) 1) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hM11, hM10,
      kmr_star_real, Matrix.one_apply_eq] at h
    have h2 : ((‖W 1 1‖ ^ 2 : ℝ) : ℂ) = 1 := by push_cast; simpa [sq] using h
    have h3 : ‖W 1 1‖ ^ 2 = 1 := by exact_mod_cast h2
    have h0 : 0 ≤ ‖W 1 1‖ := norm_nonneg _
    nlinarith
  have hM1 : M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM00, hM01, hM10, hM11, hy]
  refine ⟨θ, a, b, ?_⟩
  have hAA : A * star A = 1 := Matrix.mem_unitaryGroup_iff.mp hAm
  calc phaseDiag a * U * phaseDiag b = (A * star A) * U1 * phaseDiag b := by
        rw [hAA, one_mul]
    _ = A * M := by simp only [hM, hW, Matrix.mul_assoc]
    _ = cabibboMatrix θ := by rw [hM1, Matrix.mul_one]
