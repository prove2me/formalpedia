-- Prove2me | solution 1 for MasulloRH.compensated_resolvent_kernel_pos
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T00:03:33.024285+00:00
-- url     : https://prove2.me/submissions/e66c56f3-00f1-40ca-82ab-968df62b013a

import Mathlib


theorem solution
    (β γ T : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hγ : 36 ≤ γ ^ 2) :
    let a := 3 - β
    let b := 5 / 2 - β
    let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
    let k := a / (a ^ 2 + (T - γ) ^ 2) - b / (b ^ 2 + γ ^ 2) + 8 * c0
    0 < k ∧ a / (a ^ 2 + (T - γ) ^ 2) ≤ k := by
  dsimp
  let a : ℝ := 3 - β
  let b : ℝ := 5 / 2 - β
  let d : ℝ := T - γ
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha2 : 2 ≤ a := by dsimp [a]; linarith
  have ha3 : a ≤ 3 := by dsimp [a]; linarith
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hb15 : 3 / 2 ≤ b := by dsimp [b]; linarith
  have hb25 : b ≤ 5 / 2 := by dsimp [b]; linarith
  have hab : a * b ≤ (15 / 2 : ℝ) := by
    have h := mul_le_mul ha3 hb25 hb0 (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  have h4a0 : 0 ≤ 4 + a := by linarith
  have h4a7 : 4 + a ≤ 7 := by linarith
  have hab4a : a * b * (4 + a) ≤ (105 / 2 : ℝ) := by
    have h := mul_le_mul hab h4a7 h4a0 (by norm_num : (0 : ℝ) ≤ 15 / 2)
    nlinarith
  have hleft : (105 / 2 : ℝ) ≤ (4 - b) * γ ^ 2 := by
    have hcoeff : (3 / 2 : ℝ) ≤ 4 - b := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg γ)
    nlinarith
  have hdena : 0 < a ^ 2 + γ ^ 2 := by positivity
  have hdenb : 0 < b ^ 2 + γ ^ 2 := by positivity
  have hdenab : 0 < (a ^ 2 + γ ^ 2) * (b ^ 2 + γ ^ 2) :=
    mul_pos hdena hdenb
  have hgap : 0 < γ ^ 2 - a * b := by nlinarith
  have habdiff : a - b = (1 / 2 : ℝ) := by
    dsimp [a, b]
    ring
  have hc0 : 0 < a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2) := by
    rw [div_sub_div _ _ (ne_of_gt hdena) (ne_of_gt hdenb)]
    have hnum : 0 < a * (b ^ 2 + γ ^ 2) - b * (a ^ 2 + γ ^ 2) := by
      have heq : a * (b ^ 2 + γ ^ 2) - b * (a ^ 2 + γ ^ 2) =
          (a - b) * (γ ^ 2 - a * b) := by ring
      rw [heq]
      exact mul_pos (by linarith) hgap
    have hdiv := div_pos hnum (mul_pos hdena hdenb)
    simpa [mul_comm] using hdiv
  have h8 : b / (b ^ 2 + γ ^ 2) ≤
      8 * (a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)) := by
    rw [div_sub_div _ _ (ne_of_gt hdena) (ne_of_gt hdenb)]
    have hnum : a * (b ^ 2 + γ ^ 2) - (a ^ 2 + γ ^ 2) * b =
        (a - b) * (γ ^ 2 - a * b) := by ring
    have hkey0 : b * (a ^ 2 + γ ^ 2) ≤
        4 * (γ ^ 2 - a * b) := by
      nlinarith [hleft, hab4a]
    have hkey : b * (a ^ 2 + γ ^ 2) ≤ 8 *
        (a * (b ^ 2 + γ ^ 2) - (a ^ 2 + γ ^ 2) * b) := by
      rw [hnum]
      nlinarith [habdiff, hkey0]
    calc
      b / (b ^ 2 + γ ^ 2) =
          (b * (a ^ 2 + γ ^ 2)) / ((a ^ 2 + γ ^ 2) * (b ^ 2 + γ ^ 2)) := by
            apply (div_eq_div_iff (ne_of_gt hdenb) (ne_of_gt hdenab)).2
            ring
      _ ≤ (8 * (a * (b ^ 2 + γ ^ 2) - (a ^ 2 + γ ^ 2) * b)) /
          ((a ^ 2 + γ ^ 2) * (b ^ 2 + γ ^ 2)) := by
            apply (div_le_div_iff_of_pos_right hdenab).2
            exact hkey
      _ = 8 * ((a * (b ^ 2 + γ ^ 2) - (a ^ 2 + γ ^ 2) * b) /
          ((a ^ 2 + γ ^ 2) * (b ^ 2 + γ ^ 2))) := by
            ring
  have hbase : 0 < a / (a ^ 2 + d ^ 2) := by positivity
  have hbase' : 0 < a / (a ^ 2 + (T - γ) ^ 2) := by simpa [d] using hbase
  constructor
  · nlinarith [h8, hbase']
  · nlinarith [h8]

