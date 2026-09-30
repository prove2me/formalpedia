-- Prove2me | solution 1 for InventoryControl.two_level_integer_k
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T04:50:19.275136+00:00
-- url     : https://prove2.me/submissions/a2f1f32c-203c-49e8-998c-af8c1dc29969

import Mathlib
import Definitions.Def_InventoryControl_serial

set_option autoImplicit false

open InventoryControl in
lemma f8efe01c_cost_le_iff (d A1 A2 e1 e2 a b : ℝ) (hd : 0 < d) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (he1 : 0 < e1) (he2 : 0 < e2) (_ha : 0 < a) (hb : 0 < b) :
    twoLevelOptCost d A1 A2 e1 e2 a ≤ twoLevelOptCost d A1 A2 e1 e2 b ↔
      (A1 + A2 / a) * (e1 + a * e2) ≤ (A1 + A2 / b) * (e1 + b * e2) := by
  unfold twoLevelOptCost
  have hb' : 0 ≤ 2 * (A1 + A2 / b) * d * (e1 + b * e2) := by positivity
  rw [Real.sqrt_le_sqrt_iff hb']
  constructor
  · intro h
    have h2 : 0 < 2 * d := by positivity
    nlinarith [h]
  · intro h
    have h2 : 0 < 2 * d := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h h2.le]

open InventoryControl in
theorem solution (d A1 A2 e1 e2 : ℝ) (hd : 0 < d) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (he1 : 0 < e1) (he2 : 0 < e2) :
    (∀ k : ℕ, 0 < k →
        (twoLevelOptCost d A1 A2 e1 e2 k ≤ twoLevelOptCost d A1 A2 e1 e2 (k + 1)
          ↔ Real.sqrt (A2 * e1 / (A1 * e2)) / k ≤ (k + 1) / Real.sqrt (A2 * e1 / (A1 * e2))))
      ∧ (A2 / e2 ≤ A1 / e1 → ∀ k : ℕ, 0 < k →
          twoLevelOptCost d A1 A2 e1 e2 1 ≤ twoLevelOptCost d A1 A2 e1 e2 k) := by
  constructor
  · intro k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
    rw [f8efe01c_cost_le_iff d A1 A2 e1 e2 _ _ hd hA1 hA2 he1 he2 hk' hk1]
    have hs : 0 < A2 * e1 / (A1 * e2) := by positivity
    have hsq : 0 < Real.sqrt (A2 * e1 / (A1 * e2)) := Real.sqrt_pos.mpr hs
    rw [div_le_div_iff₀ hk' hsq, Real.mul_self_sqrt hs.le, div_le_iff₀ (by positivity)]
    have hdiff : (A1 + A2 / ((k : ℝ) + 1)) * (e1 + ((k : ℝ) + 1) * e2)
        - (A1 + A2 / (k : ℝ)) * (e1 + (k : ℝ) * e2)
        = (A1 * e2 * ((k : ℝ) * ((k : ℝ) + 1)) - A2 * e1) / ((k : ℝ) * ((k : ℝ) + 1)) := by
      field_simp
      ring
    have hden : 0 < (k : ℝ) * ((k : ℝ) + 1) := by positivity
    constructor
    · intro h
      have h0 : 0 ≤ (A1 * e2 * ((k : ℝ) * ((k : ℝ) + 1)) - A2 * e1) / ((k : ℝ) * ((k : ℝ) + 1)) := by
        rw [← hdiff]; linarith
      rw [le_div_iff₀ hden] at h0
      nlinarith
    · intro h
      have h0 : 0 ≤ (A1 * e2 * ((k : ℝ) * ((k : ℝ) + 1)) - A2 * e1) / ((k : ℝ) * ((k : ℝ) + 1)) := by
        apply div_nonneg _ hden.le
        nlinarith
      rw [← hdiff] at h0
      linarith
  · intro hle k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [f8efe01c_cost_le_iff d A1 A2 e1 e2 _ _ hd hA1 hA2 he1 he2 one_pos hk']
    have hc : A2 * e1 ≤ A1 * e2 := by
      rw [div_le_div_iff₀ he2 he1] at hle; linarith
    have hdiff : (A1 + A2 / (k : ℝ)) * (e1 + (k : ℝ) * e2) - (A1 + A2 / 1) * (e1 + 1 * e2)
        = ((k : ℝ) - 1) * (A1 * e2 * (k : ℝ) - A2 * e1) / (k : ℝ) := by
      field_simp
      ring
    have h0 : 0 ≤ ((k : ℝ) - 1) * (A1 * e2 * (k : ℝ) - A2 * e1) / (k : ℝ) := by
      apply div_nonneg _ hk'.le
      apply mul_nonneg (by linarith)
      have hp : 0 < A1 * e2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hk1 hp.le]
    linarith
