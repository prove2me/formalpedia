-- Prove2me | solution 2 for KobayashiMaskawa1973.rephasingEquiv_quartet_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T02:27:58.446376+00:00
-- url     : https://prove2.me/submissions/9055614b-d498-43bf-aa27-e96b35162fd9

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open KobayashiMaskawa1973 Matrix in
theorem kmx_hE (δ : ℝ) :
    Complex.exp ((δ : ℂ) * Complex.I) * star (Complex.exp ((δ : ℂ) * Complex.I)) = 1 := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

open KobayashiMaskawa1973 Matrix in
theorem kmx_phase (u00 u11 u01 u10 : ℂ) (a0 a1 b0 b1 : ℝ) :
    (Complex.exp ((a0 : ℂ) * Complex.I) * u00 * Complex.exp ((b0 : ℂ) * Complex.I)) *
    (Complex.exp ((a1 : ℂ) * Complex.I) * u11 * Complex.exp ((b1 : ℂ) * Complex.I)) *
    star (Complex.exp ((a0 : ℂ) * Complex.I) * u01 * Complex.exp ((b1 : ℂ) * Complex.I)) *
    star (Complex.exp ((a1 : ℂ) * Complex.I) * u10 * Complex.exp ((b0 : ℂ) * Complex.I)) =
    u00 * u11 * star u01 * star u10 := by
  have hA := kmx_hE a0
  have hB := kmx_hE a1
  have hC := kmx_hE b0
  have hD := kmx_hE b1
  simp only [star_mul']
  generalize star u01 = v01
  generalize star u10 = v10
  generalize star (Complex.exp ((a0 : ℂ) * Complex.I)) = fa0 at hA ⊢
  generalize star (Complex.exp ((a1 : ℂ) * Complex.I)) = fa1 at hB ⊢
  generalize star (Complex.exp ((b0 : ℂ) * Complex.I)) = fb0 at hC ⊢
  generalize star (Complex.exp ((b1 : ℂ) * Complex.I)) = fb1 at hD ⊢
  generalize Complex.exp ((a0 : ℂ) * Complex.I) = ea0 at hA ⊢
  generalize Complex.exp ((a1 : ℂ) * Complex.I) = ea1 at hB ⊢
  generalize Complex.exp ((b0 : ℂ) * Complex.I) = eb0 at hC ⊢
  generalize Complex.exp ((b1 : ℂ) * Complex.I) = eb1 at hD ⊢
  linear_combination (u00 * u11 * v01 * v10) * (ea1 * fa1) * (eb0 * fb0) * (eb1 * fb1) * hA
    + (u00 * u11 * v01 * v10) * (eb0 * fb0) * (eb1 * fb1) * hB
    + (u00 * u11 * v01 * v10) * (eb1 * fb1) * hC
    + (u00 * u11 * v01 * v10) * hD

open KobayashiMaskawa1973 Matrix in
theorem kmx_rephase (U V : Matrix (Fin 3) (Fin 3) ℂ) (h : RephasingEquiv U V) :
    V 0 0 * V 1 1 * star (V 0 1) * star (V 1 0) = U 0 0 * U 1 1 * star (U 0 1) * star (U 1 0) := by
  obtain ⟨a, b, rfl⟩ := h
  simp only [phaseDiag, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact kmx_phase (U 0 0) (U 1 1) (U 0 1) (U 1 0) (a 0) (a 1) (b 0) (b 1)

open KobayashiMaskawa1973 Matrix in
theorem solution (U V : Matrix (Fin 3) (Fin 3) ℂ) (h : RephasingEquiv U V) :
    V 0 0 * V 1 1 * star (V 0 1) * star (V 1 0) = U 0 0 * U 1 1 * star (U 0 1) * star (U 1 0) := by
  exact kmx_rephase U V h
