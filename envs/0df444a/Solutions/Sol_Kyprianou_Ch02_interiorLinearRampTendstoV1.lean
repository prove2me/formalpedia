-- Prove2me | solution 1 for Kyprianou.Ch02.interiorLinearRampTendstoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:13:20.041801+00:00
-- url     : https://prove2.me/submissions/31e52619-ed93-4591-933c-620c2be91928

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_interiorLinearRampBoundsV1
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (r : ℝ) (hr : 0 < r) (x : ℝ) :
    Tendsto (fun n : ℕ => min (max 0 (x - 1 / ((n : ℝ) + 1))) (max 0 (((n : ℝ) + 1) * (r - x)))) atTop
      (nhds ((Ioo (0 : ℝ) r).indicator id x)) := by
  let g (n : ℕ) : ℝ := min (max 0 (x - 1 / ((n : ℝ) + 1))) (max 0 (((n : ℝ) + 1) * (r - x)))
  change Tendsto g atTop (nhds ((Ioo (0 : ℝ) r).indicator id x))
  by_cases hx : x ∈ Ioo (0 : ℝ) r
  · rw [indicator_of_mem hx]
    have hlim : Tendsto (fun n : ℕ => max 0 (x - 1 / ((n : ℝ) + 1))) atTop (nhds x) := by
      have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [max_eq_right hx.1.le] using
        (tendsto_const_nhds (x := (0 : ℝ))).max ((tendsto_const_nhds (x := x)).sub ht)
    apply hlim.congr'
    obtain ⟨N, hN⟩ := exists_nat_gt (x / (r - x))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hpos : 0 < r - x := sub_pos.mpr hx.2
    have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hmul : x ≤ ((n : ℝ) + 1) * (r - x) := by
      have hq : x < (N : ℝ) * (r - x) := (div_lt_iff₀ hpos).mp hN
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) + 1 - (N : ℝ) by linarith) hpos.le]
    symm
    exact min_eq_left ((max_le hx.1.le (sub_le_self _ (by positivity))).trans
      (hmul.trans (le_max_right _ _)))
  · rw [indicator_of_notMem hx]
    apply tendsto_const_nhds.congr'
    filter_upwards with n
    obtain ⟨h0, hle, _, _⟩ := Kyprianou.Ch02.interiorLinearRampBoundsV1 r hr n x
    rw [indicator_of_notMem hx] at hle
    exact (le_antisymm hle h0).symm
