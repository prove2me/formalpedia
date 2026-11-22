-- Prove2me | solution 1 for LongGapsBetweenPrimes.eventually_greedy_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:36.791797+00:00
-- url     : https://prove2.me/submissions/319a5895-1e2c-4b53-8b1d-681e96c625a9

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_smoothScaleConstant_pos
import Theorems.Thm_LongGapsBetweenPrimes_eventually_cover_parameters
import Theorems.Thm_LongGapsBetweenPrimes_coverW_le_coverZ
import Theorems.Thm_LongGapsBetweenPrimes_coverW_ge_two
import Theorems.Thm_LongGapsBetweenPrimes_greedy_product_le

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution : ∀ᶠ x : ℝ in Filter.atTop,
    (∏ p ∈ auxiliaryPrimes (coverW x) (coverZ x), (1 - 1 / (p : ℝ))) ≤
      10 * smoothScaleConstant * Real.exp 6 * Real.log (Real.log x) ^ 2 /
        (Real.log x * Real.log (Real.log (Real.log x))) := by
  filter_upwards [eventually_cover_parameters] with x hparameters
  obtain ⟨hx, hl, hll, hlll, _, _, _, hZlow, _⟩ := hparameters
  have hx1 : 1 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hll0 : 0 < Real.log (Real.log x) := by linarith
  have hlll0 : 0 < Real.log (Real.log (Real.log x)) := by linarith
  have hW : 2 ≤ coverW x := coverW_ge_two hl
  have hWZ : coverW x ≤ coverZ x := coverW_le_coverZ hx1 hZlow
  have hW0 : 0 < (coverW x : ℝ) := by exact_mod_cast (by omega : 0 < coverW x)
  have hnum : 1 + Real.log (coverW x) ≤ 5 * Real.log (Real.log x) := by
    have hlogW : Real.log (coverW x) ≤ 4 * Real.log (Real.log x) := by
      calc
        _ ≤ Real.log (Real.log x ^ 4) :=
          Real.log_le_log hW0 (Nat.floor_le (by positivity))
        _ = _ := by rw [Real.log_pow]; norm_num
    linarith
  have hlogZ : coverLogZ x / 2 ≤ Real.log (coverZ x) := by
    have hexp : 2 ≤ Real.exp (coverLogZ x / 2) := by
      linarith [Real.add_one_le_exp (coverLogZ x / 2)]
    have hsquare : Real.exp (coverLogZ x) = Real.exp (coverLogZ x / 2) ^ 2 := by
      rw [pow_two, ← Real.exp_add, add_halves]
    have hfloor : Real.exp (coverLogZ x) < (coverZ x : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    calc
      _ = Real.log (Real.exp (coverLogZ x / 2)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by nlinarith)
  calc
    _ ≤ Real.exp 6 * (1 + Real.log (coverW x)) / Real.log (coverZ x) :=
      greedy_product_le hW hWZ
    _ ≤ Real.exp 6 * (5 * Real.log (Real.log x)) / (coverLogZ x / 2) := by
      gcongr
      linarith
    _ = _ := by
      unfold coverLogZ
      field_simp [smoothScaleConstant_pos.ne', hl0.ne', hll0.ne', hlll0.ne']
      ring
end LongGapsBetweenPrimes
