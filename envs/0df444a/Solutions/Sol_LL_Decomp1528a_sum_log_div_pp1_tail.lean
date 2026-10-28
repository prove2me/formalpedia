-- Prove2me | solution 1 for LL_Decomp1528a.sum_log_div_pp1_tail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T17:30:20.745885+00:00
-- url     : https://prove2.me/submissions/49502629-17ce-4333-af37-f98d00563fdd

import Mathlib

open Real Finset

namespace S218LT

noncomputable def f (m : ℝ) : ℝ := (log m + 2) / m

lemma step {m : ℝ} (hm : 2 ≤ m) :
    log m / (m * (m - 1)) ≤ f (m - 1) - f m := by
  unfold f
  have h1 : 0 < m - 1 := by linarith
  have h0 : 0 < m := by linarith
  have hkey : m * (log m - log (m - 1)) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (x := m / (m - 1)) (by positivity)
    rw [Real.log_div h0.ne' h1.ne'] at h
    have he : m / (m - 1) - 1 = 1 / (m - 1) := by field_simp; ring
    rw [he] at h
    have : m * (1 / (m - 1)) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ h1]; linarith
    calc m * (log m - log (m - 1)) ≤ m * (1 / (m - 1)) := mul_le_mul_of_nonneg_left h h0.le
      _ ≤ 2 := this
  rw [le_sub_iff_add_le, div_add_div _ _ (by positivity) h0.ne', div_le_div_iff₀ (by positivity) h1]
  nlinarith [mul_pos h0 h1]

lemma f_nonneg {m : ℝ} (hm : 1 ≤ m) : 0 ≤ f m :=
  div_nonneg (by linarith [Real.log_nonneg hm]) (by linarith)

lemma tele (k : ℕ) :
    ∑ m ∈ Ioc 1000 (1000 + k), log m / ((m : ℝ) * ((m : ℝ) - 1)) ≤ f 1000 - f ((1000 + k : ℕ) : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 1000 + (k + 1) = (1000 + k) + 1 by ring, sum_Ioc_succ_top (by omega)]
    have := step (m := ((1000 + k + 1 : ℕ) : ℝ)) (by push_cast; linarith)
    have hc : ((1000 + k + 1 : ℕ) : ℝ) - 1 = ((1000 + k : ℕ) : ℝ) := by push_cast; ring
    rw [hc] at this ⊢
    linarith

end S218LT

theorem solution (n : ℕ) :
    ∑ m ∈ Ioc 1000 n, log m / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 0.009 := by
  have hf : S218LT.f 1000 ≤ 0.009 := by
    unfold S218LT.f
    have hl : log 1000 ≤ 7 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h7 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h7]
      have := Real.exp_one_gt_d9
      calc (1000:ℝ) ≤ 2.7182818283 ^ 7 := by norm_num
        _ ≤ Real.exp 1 ^ 7 := by gcongr
    rw [div_le_iff₀ (by norm_num)]; linarith
  rcases le_or_gt n 1000 with h | h
  · rw [Ioc_eq_empty (by omega), sum_empty]; norm_num
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.le
    have := S218LT.tele k
    have := S218LT.f_nonneg (m := ((1000 + k : ℕ) : ℝ)) (by push_cast; linarith)
    linarith
