-- Prove2me | solution 1 for LandauFunction.ford_prime_counting_error
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:40:03.582673+00:00
-- url     : https://prove2.me/submissions/a7adc1dc-5ffc-44cc-ba7f-3b6a0e8324ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LandauFunction_logIntegral
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_VonKoch_primeCounting_sub_logIntegral_of_riemannHypothesis



namespace LandauFunction
end LandauFunction
open LandauFunction
theorem solution :
    ∃ c : ℝ, 0 < c ∧
      (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x) =O[Filter.atTop]
        (fun x : ℝ => x * Real.exp (-c * Real.log x ^ ((3 : ℝ) / 5) *
          Real.log (Real.log x) ^ (-(1 : ℝ) / 5))) := by
  obtain ⟨C, hC⟩ :=
    VonKoch.primeCounting_sub_logIntegral_of_riemannHypothesis mathlib_riemannHypothesis
  refine ⟨1 / 4, by norm_num, Asymptotics.IsBigO.of_bound (4 * |C|) ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 3)] with x hx
  obtain ⟨L, rfl⟩ : ∃ L : ℝ, x = Real.exp L :=
    ⟨Real.log x, (Real.exp_log (lt_of_lt_of_le (Real.exp_pos 3) hx)).symm⟩
  have hL : (3 : ℝ) ≤ L := Real.exp_le_exp.mp hx
  have h3 : (3 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hK := hC (Real.exp L) h3
  rw [← Real.exp_half, Real.log_exp] at hK
  have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlogL : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hM1 : Real.log L ^ (-(1 : ℝ) / 5) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlogL (by norm_num)
  have hM0 : 0 ≤ Real.log L ^ (-(1 : ℝ) / 5) := Real.rpow_nonneg (by linarith) _
  have hP : L ^ ((3 : ℝ) / 5) ≤ L := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ L by linarith)
      (show (3 : ℝ) / 5 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hA : L ^ ((3 : ℝ) / 5) * Real.log L ^ (-(1 : ℝ) / 5) ≤ L := by
    calc L ^ ((3 : ℝ) / 5) * Real.log L ^ (-(1 : ℝ) / 5) ≤ L * 1 :=
          mul_le_mul hP hM1 hM0 (by linarith)
      _ = L := mul_one L
  have hexp : Real.exp (-(L / 4)) ≤
      Real.exp (-(1 / 4) * L ^ ((3 : ℝ) / 5) * Real.log L ^ (-(1 : ℝ) / 5)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hL4 : L ≤ 4 * Real.exp (L / 4) := by linarith [Real.add_one_le_exp (L / 4)]
  have hsplit : Real.exp (L / 2) * Real.exp (L / 4) = Real.exp L * Real.exp (-(L / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hC' : C * Real.exp (L / 2) * L ≤ |C| * Real.exp (L / 2) * L :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le) (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.log_exp,
    abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  calc |(Nat.primeCounting ⌊Real.exp L⌋₊ : ℝ) - logIntegral (Real.exp L)|
      ≤ C * Real.exp (L / 2) * L := hK
    _ ≤ |C| * Real.exp (L / 2) * L := hC'
    _ ≤ |C| * Real.exp (L / 2) * (4 * Real.exp (L / 4)) :=
        mul_le_mul_of_nonneg_left hL4 (mul_nonneg (abs_nonneg C) (Real.exp_pos _).le)
    _ = 4 * |C| * (Real.exp L * Real.exp (-(L / 4))) := by
        rw [← hsplit]
        ring
    _ ≤ 4 * |C| * (Real.exp L * Real.exp (-(1 / 4) * L ^ ((3 : ℝ) / 5) *
          Real.log L ^ (-(1 : ℝ) / 5))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le)
          (mul_nonneg (by norm_num) (abs_nonneg C))
