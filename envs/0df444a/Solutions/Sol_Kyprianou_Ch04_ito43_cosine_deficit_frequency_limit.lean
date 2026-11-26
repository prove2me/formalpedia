-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cosine_deficit_frequency_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:37:42.109455+00:00
-- url     : https://prove2.me/submissions/0d8870f4-5381-489f-9a0e-134852f43f62

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_qv_cosine_bounds
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution (z : ℝ) :
    Tendsto (fun m : ℕ => (1-Real.cos (((m:ℝ)+1)*z))/((m:ℝ)+1)^2) atTop (nhds 0) := by
  have h : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun m : ℕ => (2:ℝ)/((m:ℝ)+1)^2) atTop (nhds 0) := by
    have H := (h.mul h).const_mul (2:ℝ)
    convert H using 1
    · funext m
      have hn : (m:ℝ)+1 ≠ 0 := by positivity
      field_simp
      <;> ring
    · norm_num
  exact squeeze_zero
    (fun m => (Kyprianou.Ch04.ito43_qv_cosine_bounds ((m:ℝ)+1) z).1)
    (fun m => (Kyprianou.Ch04.ito43_qv_cosine_bounds ((m:ℝ)+1) z).2.1) hlim
