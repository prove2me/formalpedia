-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.translationTermCount_log_div_eventually_lt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:52:02.386994+00:00
-- url     : https://prove2.me/submissions/62b75e8b-9a10-41b8-bcee-3309804c120a

import Mathlib
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent
theorem solution
    (m : ℕ) {v : ℝ} (hv : 0 < v) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ H : ℝ in atTop,
      Real.log (translationTermCount m v H : ℝ) / H < ε := by
  have t1 : Filter.Tendsto (fun H : ℝ => Real.log (H + 1) / H) Filter.atTop (nhds 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (Filter.tendsto_atTop_add_const_right Filter.atTop 1 Filter.tendsto_id)
    refine this.congr' ?_
    filter_upwards with H
    simp only [Function.comp_apply, id, pow_one, one_mul]
    congr 1; ring
  have t2 : Filter.Tendsto (fun H : ℝ => Real.log (H / v + 1) / H) Filter.atTop (nhds 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop v (-v) 1 hv.ne').comp
      (Filter.tendsto_atTop_add_const_right Filter.atTop 1
        (Filter.tendsto_id.atTop_div_const hv))
    refine this.congr' ?_
    filter_upwards with H
    simp only [Function.comp_apply, id, pow_one]
    congr 1; field_simp; ring
  have t3 : Filter.Tendsto (fun H : ℝ => (2 * (m : ℝ)) * (Real.log (H + 1) / H) + Real.log (H / v + 1) / H)
      Filter.atTop (nhds 0) := by
    simpa using (t1.const_mul (2 * (m : ℝ))).add t2
  filter_upwards [t3.eventually (gt_mem_nhds hε), Filter.eventually_gt_atTop (0 : ℝ)] with H h1 hH
  have hc : ((translationTermCount m v H : ℕ) : ℝ) ≤ (H + 1) ^ (2 * m) * (H / v + 1) := by
    unfold translationTermCount
    push_cast
    have e1 : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le hH.le
    have e2 : (⌊H / v⌋₊ : ℝ) ≤ H / v := Nat.floor_le (by positivity)
    gcongr
  have hpos : (0 : ℝ) < (translationTermCount m v H : ℕ) := by
    unfold translationTermCount; positivity
  have hlog : Real.log ((translationTermCount m v H : ℕ) : ℝ) ≤
      (2 * (m : ℝ)) * Real.log (H + 1) + Real.log (H / v + 1) := by
    calc Real.log ((translationTermCount m v H : ℕ) : ℝ) ≤ Real.log ((H + 1) ^ (2 * m) * (H / v + 1)) :=
          Real.log_le_log hpos hc
      _ = _ := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
  calc Real.log ((translationTermCount m v H : ℕ) : ℝ) / H
      ≤ ((2 * (m : ℝ)) * Real.log (H + 1) + Real.log (H / v + 1)) / H :=
        div_le_div_of_nonneg_right hlog hH.le
    _ = (2 * (m : ℝ)) * (Real.log (H + 1) / H) + Real.log (H / v + 1) / H := by ring
    _ < ε := h1
