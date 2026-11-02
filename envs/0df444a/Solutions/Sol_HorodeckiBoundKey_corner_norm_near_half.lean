-- Prove2me | solution 1 for HorodeckiBoundKey.corner_norm_near_half
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T04:14:27.756233+00:00
-- url     : https://prove2.me/submissions/bd55fe78-198f-47b8-bf3f-eca8e529bbfa

import Mathlib
import Definitions.Def_HorodeckiBoundKey_cornerNormValue

theorem solution (p : ℝ) (hp : 1 / 4 < p) (hp' : p ≤ 1 / 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∃ l₀ : ℕ, ∀ l : ℕ, l₀ ≤ l →
      1 / 2 - ε < HorodeckiBoundKey.cornerNormValue p l n := by
  set δ := min ε (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min hε (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  set r := (1 - 2 * p) / (2 * p) with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) (by linarith)
  have hr1 : r < 1 := by rw [div_lt_one (by linarith)]; linarith
  -- `r^n → 0`
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp ((tendsto_order.1 hlim).2 δ hδ0)
  refine ⟨n₀, fun n hn => ?_⟩
  have hrn : r ^ n < δ := hn₀ n hn
  -- `(1 - 2^{-l})^n → 1` as `l → ∞` (Bernoulli)
  obtain ⟨l₀, hl₀⟩ := pow_unbounded_of_one_lt ((n : ℝ) / δ) (by norm_num : (1 : ℝ) < 2)
  refine ⟨l₀, fun l hl => ?_⟩
  have h2l : (2 : ℝ) ^ l₀ ≤ 2 ^ l := pow_le_pow_right₀ (by norm_num) hl
  have h2pos : (0 : ℝ) < 2 ^ l := by positivity
  have hsmall : (n : ℝ) * (1 / 2 ^ l) ≤ δ := by
    rw [mul_one_div, div_le_iff₀ h2pos]
    have : (n : ℝ) / δ < 2 ^ l := lt_of_lt_of_le hl₀ h2l
    rw [div_lt_iff₀ hδ0] at this
    linarith
  have hq : (1 : ℝ) / 2 ^ l ≤ 1 := by
    rw [div_le_one h2pos]; exact one_le_pow₀ (by norm_num)
  have hbern : 1 + (n : ℝ) * (-(1 / 2 ^ l)) ≤ (1 + -(1 / 2 ^ l)) ^ n :=
    one_add_mul_le_pow (by linarith) n
  have hA : 1 - δ ≤ (1 - 1 / 2 ^ l) ^ n := by
    rw [← sub_eq_add_neg] at hbern
    linarith
  have hB : 1 - δ ≤ 1 / (1 + r ^ n) := by
    have hrn0 : 0 ≤ r ^ n := pow_nonneg hr0 n
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  unfold HorodeckiBoundKey.cornerNormValue
  have h1 : 0 ≤ 1 - δ := by linarith
  calc 1 / 2 - ε ≤ 1 / 2 - δ := by linarith
    _ < 1 / 2 * (1 - δ) * (1 - δ) := by nlinarith
    _ ≤ 1 / 2 * (1 - 1 / 2 ^ l) ^ n * (1 / (1 + ((1 - 2 * p) / (2 * p)) ^ n)) := by
        have h2 : 1 / 2 * (1 - δ) ≤ 1 / 2 * (1 - 1 / 2 ^ l) ^ n := by linarith
        exact mul_le_mul h2 hB h1 (by nlinarith)
