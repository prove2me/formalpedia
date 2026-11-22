-- Prove2me | solution 1 for LongGapsBetweenPrimes.eventually_coverScale_div_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:16:11.038612+00:00
-- url     : https://prove2.me/submissions/442a02b0-7bb8-4a55-81ed-08dad0adc107

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_eventually_cover_parameters
import Theorems.Thm_LongGapsBetweenPrimes_half_log_le_log_div

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : ∀ᶠ y : ℝ in Filter.atTop,
    coverScale y / 64 ≤ coverScale (y / 8) := by
  have hlog := Real.tendsto_log_atTop
  have hloglog := hlog.comp hlog
  have hlogloglog := hlog.comp hloglog
  filter_upwards [eventually_cover_parameters,
    hlog.eventually_ge_atTop (2 * Real.log 8),
    hloglog.eventually_ge_atTop (2 * Real.log 2),
    hlogloglog.eventually_ge_atTop (2 * Real.log 2)] with y hy h₁ h₂ h₃
  obtain ⟨hy, hL, hLL, hLLL, _⟩ := hy
  have hy0 : 0 < y := by linarith
  have hL0 : 0 < Real.log y := by linarith
  have hLL0 : 0 < Real.log (Real.log y) := by linarith
  have h₁' := half_log_le_log_div hy0 (by norm_num : (0 : ℝ) < 8) h₁
  have h₂' : Real.log (Real.log y) / 2 ≤ Real.log (Real.log (y / 8)) :=
    (half_log_le_log_div hL0 (by norm_num : (0 : ℝ) < 2) h₂).trans
      (Real.log_le_log (by positivity) h₁')
  have h₃' : Real.log (Real.log (Real.log y)) / 2 ≤
      Real.log (Real.log (Real.log (y / 8))) :=
    (half_log_le_log_div hLL0 (by norm_num : (0 : ℝ) < 2) h₃).trans
      (Real.log_le_log (by positivity) h₂')
  have hL0' : 0 < Real.log (y / 8) := by linarith
  have hLL0' : 0 < Real.log (Real.log (y / 8)) := by linarith
  have hLLL0' : 0 < Real.log (Real.log (Real.log (y / 8))) := by linarith
  have hden : Real.log (Real.log (y / 8)) ≤ Real.log (Real.log y) :=
    Real.log_le_log hL0' (Real.log_le_log (by positivity) (by linarith))
  unfold coverScale
  calc
    _ = (y / 8) * (Real.log y / 2) ^ 2 *
        (Real.log (Real.log (Real.log y)) / 2) / Real.log (Real.log y) ^ 2 := by ring
    _ ≤ _ := by gcongr
end LongGapsBetweenPrimes
