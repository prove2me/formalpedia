-- Prove2me | solution 1 for InventoryAnomaly.EW.lemma_19
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-25T23:17:44.254443+00:00
-- url     : https://prove2.me/submissions/df6de659-d74c-4a1f-8cc2-f5709dd42960

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

private theorem aux19 (x y xh yh δ : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (hxh : 0 ≤ xh ∧ xh ≤ 1) (hyh : 0 ≤ yh ∧ yh ≤ 1) (hxy : 0 < x + y)
    (h1 : |xh - x| ≤ δ) (h2 : |yh - y| ≤ δ) (hS : 0 < xh + yh) :
    |xh / (xh + yh) - x / (x + y)| ≤ δ / (x + y) ∧ |xh / (xh + yh) - x / (x + y)| ≤ δ / (xh + yh) := by
  obtain ⟨a1, a2⟩ := abs_le.mp h1
  obtain ⟨b1, b2⟩ := abs_le.mp h2
  have key : xh / (xh + yh) - x / (x + y) = (xh * y - x * yh) / ((xh + yh) * (x + y)) := by
    field_simp; ring
  rw [key, abs_div, abs_of_pos (mul_pos hS hxy)]
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) h1
  constructor
  · rw [div_le_div_iff₀ (mul_pos hS hxy) hxy]
    have : |xh * y - x * yh| ≤ δ * (xh + yh) := by
      rw [abs_le]; constructor <;> nlinarith [hx.1, hy.1, hxh.1, hyh.1]
    nlinarith [mul_le_mul_of_nonneg_right this hxy.le]
  · rw [div_le_div_iff₀ (mul_pos hS hxy) hS]
    have : |xh * y - x * yh| ≤ δ * (x + y) := by
      rw [abs_le]; constructor <;> nlinarith [hx.1, hy.1, hxh.1, hyh.1]
    nlinarith [mul_le_mul_of_nonneg_right this hS.le]

theorem solution (x y xh yh δ : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (hxh : 0 ≤ xh ∧ xh ≤ 1) (hyh : 0 ≤ yh ∧ yh ≤ 1) (hxy : 0 < x + y)
    (h1 : |xh - x| ≤ δ) (h2 : |yh - y| ≤ δ) :
    let sh := if 0 < xh + yh then xh / (xh + yh) else 0
    |sh - x / (x + y)| ≤ min (δ / (x + y)) 1 ∧
      (0 < xh + yh → |sh - x / (x + y)| ≤ δ / (xh + yh)) := by
  intro sh
  have hq0 : 0 ≤ x / (x + y) := div_nonneg hx.1 hxy.le
  have hq1 : x / (x + y) ≤ 1 := (div_le_one hxy).2 (by linarith [hy.1])
  by_cases hS : 0 < xh + yh
  · have hsh : sh = xh / (xh + yh) := if_pos hS
    have hp0 : 0 ≤ xh / (xh + yh) := div_nonneg hxh.1 hS.le
    have hp1 : xh / (xh + yh) ≤ 1 := (div_le_one hS).2 (by linarith [hyh.1])
    obtain ⟨c1, c2⟩ := aux19 x y xh yh δ hx hy hxh hyh hxy h1 h2 hS
    rw [hsh]
    refine ⟨le_min c1 ?_, fun _ => c2⟩
    rw [abs_le]; constructor <;> linarith
  · have hsh : sh = 0 := if_neg hS
    have e1 : xh = 0 := by linarith [hxh.1, hyh.1, not_lt.mp hS]
    have e2 : yh = 0 := by linarith [hxh.1, hyh.1, not_lt.mp hS]
    subst e1 e2
    rw [hsh]
    refine ⟨le_min ?_ ?_, fun h => absurd h hS⟩
    · rw [zero_sub, abs_neg, abs_of_nonneg hq0]
      have : x ≤ δ := by
        have := (abs_le.mp h1).1; linarith
      exact div_le_div_of_nonneg_right this hxy.le
    · rw [zero_sub, abs_neg, abs_of_nonneg hq0]; exact hq1
