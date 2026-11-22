-- Prove2me | solution 1 for LongGapsBetweenPrimes.long_gap_theorem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:23:49.277808+00:00
-- url     : https://prove2.me/submissions/4ca63440-404e-4ae8-89ee-e6dc8aae6ace

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_coverEta_pos
import Theorems.Thm_LongGapsBetweenPrimes_eventually_prime_gaps_in_x
import Theorems.Thm_LongGapsBetweenPrimes_eventually_coverScale_div_eight
import Theorems.Thm_LongGapsBetweenPrimes_gapScale_eq_coverScale_log

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : LongGapTheorem := by
  refine ⟨coverEta / 128, by have h := coverEta_pos; positivity, ?_⟩
  have hx : Filter.Tendsto (fun X : ℝ => Real.log X / 8) Filter.atTop Filter.atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) Real.tendsto_log_atTop
  filter_upwards [hx.eventually eventually_prime_gaps_in_x,
    Real.tendsto_log_atTop.eventually eventually_coverScale_div_eight,
    Filter.eventually_gt_atTop (0 : ℝ)] with X hgap hscale hX
  obtain ⟨p, q, hpq, hq, hwidth⟩ := hgap
  refine ⟨p, q, hpq, ?_, ?_⟩
  · have he : 8 * (Real.log X / 8) = Real.log X := by ring
    rw [he, Real.exp_log hX] at hq
    exact hq
  · rw [gapScale_eq_coverScale_log]
    have hη : 0 ≤ coverEta / 2 := by have h := coverEta_pos; positivity
    have hm := mul_le_mul_of_nonneg_left hscale hη
    nlinarith
end LongGapsBetweenPrimes
