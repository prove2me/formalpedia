-- Prove2me | solution 1 for InventoryControl.pot_round_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T16:32:30.96998+00:00
-- url     : https://prove2.me/submissions/9c09349a-324f-4f79-9d00-be0a5bf82c26

import Mathlib
import Definitions.Def_InventoryControl_serial

open InventoryControl in
theorem solution (q Q Q' : ℝ) (hq : 0 < q) (hQ : 0 < Q) (hQ' : 0 < Q') (hle : Q ≤ Q') :
    potRound q Q ≤ potRound q Q'
      ∧ Real.sqrt 2 / 2 * Q ≤ (2 : ℝ) ^ potRound q Q * q
      ∧ (2 : ℝ) ^ potRound q Q * q ≤ Real.sqrt 2 * Q := by
  have hQq : 0 < Q / q := div_pos hQ hq
  have hQq' : 0 < Q' / q := div_pos hQ' hq
  have hs2 : Real.sqrt 2 = (2 : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow 2
  have hs2pos : 0 < Real.sqrt 2 := by positivity
  have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  set L := Real.logb 2 (Q / q) with hL
  have h2L : (2 : ℝ) ^ L = Q / q := Real.rpow_logb (by norm_num) (by norm_num) hQq
  set m := potRound q Q with hm
  have hmdef : m = ⌊L + 1 / 2⌋ := rfl
  have hzp : (2 : ℝ) ^ m = (2 : ℝ) ^ (m : ℝ) := (Real.rpow_intCast 2 m).symm
  have hup : (m : ℝ) ≤ L + 1 / 2 := by rw [hmdef]; exact Int.floor_le _
  have hlo : L + 1 / 2 < (m : ℝ) + 1 := by rw [hmdef]; exact Int.lt_floor_add_one _
  have hupper : (2 : ℝ) ^ (m : ℝ) ≤ Q / q * Real.sqrt 2 := by
    calc (2 : ℝ) ^ (m : ℝ) ≤ (2 : ℝ) ^ (L + 1 / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hup
      _ = Q / q * Real.sqrt 2 := by
          rw [Real.rpow_add (by norm_num), h2L, hs2]
  have hlower : Q / q = (2 : ℝ) ^ (L - 1 / 2) * Real.sqrt 2 := by
    rw [hs2, ← Real.rpow_add (by norm_num)]
    simp [h2L]
  have hlow2 : (2 : ℝ) ^ (L - 1 / 2) < (2 : ℝ) ^ (m : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · apply Int.floor_le_floor
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hQq
      (div_le_div_of_nonneg_right hle hq.le)
    linarith
  · rw [hzp]
    have h1 : Q = (2 : ℝ) ^ (L - 1 / 2) * Real.sqrt 2 * q := by
      rw [← hlower]; field_simp
    have key : Real.sqrt 2 / 2 * Q = (2 : ℝ) ^ (L - 1 / 2) * q := by
      rw [h1]
      field_simp
      nlinarith [hsq]
    rw [key]
    exact (mul_lt_mul_of_pos_right hlow2 hq).le
  · rw [hzp]
    calc (2 : ℝ) ^ (m : ℝ) * q ≤ Q / q * Real.sqrt 2 * q :=
          mul_le_mul_of_nonneg_right hupper hq.le
      _ = Real.sqrt 2 * Q := by field_simp
