-- Prove2me | solution 1 for MasulloRH.compensated_resolvent_kernel_local_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T00:05:20.401075+00:00
-- url     : https://prove2.me/submissions/c7136fe0-25c3-4373-b7a4-130abf334313

import Mathlib
import Theorems.Thm_MasulloRH_compensated_resolvent_kernel_pos

theorem solution
    (β γ T : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hγ : 36 ≤ γ ^ 2)
    (hnear : |T - γ| ≤ 1) :
    let a := 3 - β
    let b := 5 / 2 - β
    let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
    let k := a / (a ^ 2 + (T - γ) ^ 2) - b / (b ^ 2 + γ ^ 2) + 8 * c0
    (3 / 10 : ℝ) ≤ k := by
  dsimp
  let a : ℝ := 3 - β
  let d : ℝ := T - γ
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha2 : 2 ≤ a := by dsimp [a]; linarith
  have ha3 : a ≤ 3 := by dsimp [a]; linarith
  have hnear' : -1 ≤ d ∧ d ≤ 1 := by
    dsimp [d]
    exact abs_le.mp hnear
  have hdsq : d ^ 2 ≤ 1 := by
    have hmul : 0 ≤ (1 - d) * (1 + d) :=
      mul_nonneg (by linarith [hnear'.2]) (by linarith [hnear'.1])
    nlinarith [hmul]
  have hdenda : 0 < a ^ 2 + d ^ 2 := by positivity
  have hfac : 0 ≤ (3 - a) * (3 * a - 1) + 3 * (1 - d ^ 2) := by
    have h1 : 0 ≤ (3 - a) * (3 * a - 1) :=
      mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ 3 * (1 - d ^ 2) := by nlinarith
    linarith
  have hbase : (3 / 10 : ℝ) ≤ a / (a ^ 2 + d ^ 2) := by
    apply (le_div_iff₀ hdenda).2
    nlinarith [hfac]
  have hmain := (MasulloRH.compensated_resolvent_kernel_pos β γ T hβ0 hβ1 hγ).2
  have hbase' : (3 / 10 : ℝ) ≤
      (3 - β) / ((3 - β) ^ 2 + (T - γ) ^ 2) := by
    simpa [a, d] using hbase
  nlinarith [hbase', hmain]
