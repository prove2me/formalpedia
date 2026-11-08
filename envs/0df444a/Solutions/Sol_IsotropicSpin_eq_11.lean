-- Prove2me | solution 1 for IsotropicSpin.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:37:53.30544+00:00
-- url     : https://prove2.me/submissions/6754ae6c-2f48-4e21-84c8-d9379a1af432

import Mathlib
import Definitions.Def_IsotropicSpin_spinHalf
import Definitions.Def_IsotropicSpin_isotropicChannel
import Definitions.Def_IsotropicSpin_timeReversal

open scoped Matrix

open IsotropicSpin in
theorem solution (ρ : Matrix (Fin 2) (Fin 2) ℂ) (hρ : ρ.IsHermitian) :
    isotropicChannel (1 / 2) spinHalf ρ =
      (ρ.trace / 3) • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 / 3 : ℂ) • timeReversal ρ := by
  have h00 : (starRingEnd ℂ) (ρ 0 0) = ρ 0 0 := hρ.apply 0 0
  have h01 : (starRingEnd ℂ) (ρ 1 0) = ρ 0 1 := hρ.apply 0 1
  have h10 : (starRingEnd ℂ) (ρ 0 1) = ρ 1 0 := hρ.apply 1 0
  have h11 : (starRingEnd ℂ) (ρ 1 1) = ρ 1 1 := hρ.apply 1 1
  have hs : (((1 / 2 : ℝ) * (1 / 2 + 1))⁻¹ : ℝ) = 4 / 3 := by norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [isotropicChannel, spinHalf, timeReversal, hs, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sum_apply, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.mul_apply, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.map_apply,
      Matrix.conjTranspose_apply, Matrix.one_apply, Matrix.trace_fin_two, smul_eq_mul,
      Fin.isValue, h00, h01, h10, h11, star_zero, star_one, star_neg, Complex.ofReal_div,
      Complex.ofReal_ofNat] <;>
    norm_num <;> (try ring_nf) <;> (try simp only [Complex.I_sq]) <;> (try ring_nf)
