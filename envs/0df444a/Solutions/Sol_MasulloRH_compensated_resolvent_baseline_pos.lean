-- Prove2me | solution 1 for MasulloRH.compensated_resolvent_baseline_pos
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T00:42:30.958196+00:00
-- url     : https://prove2.me/submissions/b081732f-3762-4b15-a214-b9c4dcce01a4

import Mathlib

theorem solution
    (β γ : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hγ : 36 ≤ γ ^ 2) :
    let a := 3 - β
    let b := 5 / 2 - β
    let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
    0 < c0 := by
  dsimp
  let a : ℝ := 3 - β
  let b : ℝ := 5 / 2 - β
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha3 : a ≤ 3 := by dsimp [a]; linarith
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hb25 : b ≤ 5 / 2 := by dsimp [b]; linarith
  have hab : a * b ≤ (15 / 2 : ℝ) := by
    have h := mul_le_mul ha3 hb25 hb0 (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  have hgap : 0 < γ ^ 2 - a * b := by nlinarith
  have hdena : 0 < a ^ 2 + γ ^ 2 := by positivity
  have hdenb : 0 < b ^ 2 + γ ^ 2 := by positivity
  have hc0 : 0 < a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2) := by
    rw [div_sub_div _ _ (ne_of_gt hdena) (ne_of_gt hdenb)]
    have hnum : 0 < a * (b ^ 2 + γ ^ 2) - b * (a ^ 2 + γ ^ 2) := by
      have heq : a * (b ^ 2 + γ ^ 2) - b * (a ^ 2 + γ ^ 2) =
          (a - b) * (γ ^ 2 - a * b) := by ring
      rw [heq]
      have habdiff : a - b = (1 / 2 : ℝ) := by
        dsimp [a, b]
        ring
      exact mul_pos (by linarith [habdiff]) hgap
    simpa [mul_comm] using div_pos hnum (mul_pos hdena hdenb)
  exact hc0
