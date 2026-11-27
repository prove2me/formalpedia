-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_exponential_cosine_mesh_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T22:10:20.546617+00:00
-- url     : https://prove2.me/submissions/71ba3a79-cb53-42a1-b641-23b0b01f0f61

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_exponential_real_remainder
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (T : NNReal) (z : ℂ) (n : ℕ) (hn : 0 < n)
    (hs : (T:ℝ)*‖z‖/(n:ℝ) ≤ 1) :
    |(n:ℝ)*(1-(Complex.exp (((((T/(n:NNReal)):NNReal):ℝ):ℂ)*z)).re) -
      (-(T:ℝ)*z.re)| ≤ ((T:ℝ)*‖z‖)^2/(n:ℝ) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  let x : ℝ := (T:ℝ)/(n:ℝ)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have h := Kyprianou.Ch04.ito43_exponential_real_remainder x z hx (by
    simpa [x,div_mul_eq_mul_div] using hs)
  have H := mul_le_mul_of_nonneg_left h hnR.le
  rw [← abs_of_pos hnR,← abs_mul] at H
  simp only [NNReal.coe_div,NNReal.coe_natCast]
  dsimp [x] at H
  simp only [abs_of_pos hnR] at H
  let r : ℝ := (Complex.exp ((x:ℂ)*z)).re
  change |(n:ℝ)*(1-r)-(-(T:ℝ)*z.re)| ≤ _
  change |(n:ℝ)*(1-r+(T:ℝ)/(n:ℝ)*z.re)| ≤ _ at H
  have hL : (n:ℝ)*(1-r)-(-(T:ℝ)*z.re) =
      (n:ℝ)*(1-r+(T:ℝ)/(n:ℝ)*z.re) := by field_simp <;> ring
  have hR : (n:ℝ)*((T:ℝ)/(n:ℝ)*‖z‖)^2 = ((T:ℝ)*‖z‖)^2/(n:ℝ) := by
    field_simp <;> ring
  rw [hL,← hR]
  exact H
