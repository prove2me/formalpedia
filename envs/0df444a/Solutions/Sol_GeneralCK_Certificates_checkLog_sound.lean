-- Prove2me | solution 1 for GeneralCK.Certificates.checkLog_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T20:49:10.179382+00:00
-- url     : https://prove2.me/submissions/ee39206c-5bf2-406a-b8dc-24ede5ff2b6d

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_LogBounds

open GeneralCK.Certificates
open scoped BigOperators

theorem solution {w lo hi : ℚ} {n : ℕ}
    (hc : checkLog w n lo hi = true) :
    (lo : ℝ) ≤ Real.log ((1 + (w : ℝ)) / (1 - (w : ℝ))) ∧
    Real.log ((1 + (w : ℝ)) / (1 - (w : ℝ))) ≤ (hi : ℝ) := by
  have hh : 0 ≤ w ∧ w < 1 ∧ lo ≤ logLower w n ∧ logUpper w n ≤ hi :=
    of_decide_eq_true hc
  obtain ⟨hw₀, hw₁, hl, hu⟩ := hh
  have hw₀' : (0 : ℝ) ≤ w := by exact_mod_cast hw₀
  have hw₁' : (w : ℝ) < 1 := by exact_mod_cast hw₁
  have lower := Real.sum_range_le_log_div hw₀' hw₁' n
  have upper := Real.log_div_le_sum_range_add hw₀' hw₁' n
  dsimp [logLower, logUpper] at hl hu
  have hl' : (lo : ℝ) ≤
      2 * ∑ i ∈ Finset.range n, (w : ℝ) ^ (2 * i + 1) / (2 * i + 1) := by
    exact_mod_cast hl
  have hu' :
      2 * ∑ i ∈ Finset.range n, (w : ℝ) ^ (2 * i + 1) / (2 * i + 1) +
      2 * (w : ℝ) ^ (2 * n + 1) / (1 - (w : ℝ) ^ 2) ≤ (hi : ℝ) := by
    exact_mod_cast hu
  rw [mul_div_assoc] at hu'
  constructor <;> linarith
