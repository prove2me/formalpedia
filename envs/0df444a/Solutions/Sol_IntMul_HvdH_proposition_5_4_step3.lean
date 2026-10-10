-- Prove2me | solution 1 for IntMul.HvdH.proposition_5_4_step3
-- status  : ACCEPTED   (prove)
-- author  : @avi
-- created : 2026-10-09T12:41:50.786357+00:00
-- url     : https://prove2.me/submissions/e137725b-6802-486f-a647-1759af04dbca

import Mathlib

theorem solution (n b p γ T S : ℕ) (hb : 4096 ≤ b) (hp : p = 6 * b)
    (hγ : (γ : ℝ) < 8 * (b : ℝ) ^ ((2 : ℝ) / 3)) (hT1 : 1 ≤ T) (hTn : T < n) (hn : n ≤ 2 ^ b)
    (hTb : T * b < 8 * n) (hS : S ≤ T) {ι : Type*} [Fintype ι] (w w' : ι → ℂ)
    (herr : (2 : ℝ) ^ p * ‖w' - w‖ < (2 : ℝ) ^ (γ + 8) * (T : ℝ) ^ 2 * Real.logb 2 T) :
    ‖((2 : ℂ) ^ (2 * b) * S) • w - ((2 : ℂ) ^ (2 * b) * S) • w'‖ < 1 / 4 := by
  -- (5.5) gives γ < 8 b^{2/3} ≤ b / 2, hence γ + 13 ≤ b
  have hbR : (4096 : ℝ) ≤ b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) ≤ b := by linarith
  set y := (b : ℝ) ^ ((2 : ℝ) / 3) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg hb0 _
  have hy3 : y ^ 3 = (b : ℝ) ^ 2 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hb0]; norm_num
  have hyb : y ≤ b / 16 := by
    by_contra h
    rw [not_le] at h
    have h1 : ((b : ℝ) / 16) ^ 3 < y ^ 3 := pow_lt_pow_left₀ h (by positivity) (by norm_num)
    rw [hy3] at h1
    nlinarith [h1, sq_nonneg (b : ℝ)]
  have hγb : γ + 13 ≤ b := by
    have : (γ : ℝ) + 13 ≤ b := by linarith
    exact_mod_cast this
  -- rewrite the left side as 2^{2b} S ‖w' - w‖
  rw [← smul_sub, norm_smul, norm_sub_rev]
  have hc : ‖(2 : ℂ) ^ (2 * b) * (S : ℂ)‖ = (2 : ℝ) ^ (2 * b) * S := by
    rw [norm_mul, norm_pow]; simp
  rw [hc]
  set D := ‖w' - w‖ with hDdef
  set L := Real.logb 2 T with hLdef
  have hD0 : 0 ≤ D := norm_nonneg _
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) hTR
  have hT2b : (T : ℝ) ≤ 2 ^ b := by
    have : T ≤ 2 ^ b := by omega
    exact_mod_cast this
  -- log₂ T ≤ b, so T log₂ T ≤ T b < 8 n ≤ 2^{b+3}
  have hLb : L ≤ b := by
    have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith) hT2b
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
  have hTL : (T : ℝ) * L < 2 ^ (b + 3) := by
    have h1 : (T : ℝ) * b < 8 * n := by exact_mod_cast hTb
    have h2 : (n : ℝ) ≤ 2 ^ b := by exact_mod_cast hn
    have h3 : (T : ℝ) * L ≤ T * b := mul_le_mul_of_nonneg_left hLb (by linarith)
    rw [pow_add]; linarith
  have hT2 : (T : ℝ) ^ 2 ≤ 2 ^ (2 * b) := by
    rw [pow_mul']
    exact pow_le_pow_left₀ (by linarith) hT2b 2
  have hS' : (S : ℝ) ≤ T := by exact_mod_cast hS
  have hD : D * 2 ^ (6 * b) < 2 ^ (γ + 8) * (T : ℝ) ^ 2 * L := by
    rw [hp] at herr; linarith
  -- 2^{2b} T · 2^{γ+8} T² log₂ T · 4 < 2^{5b+γ+13} ≤ 2^{6b}
  have key : (2 : ℝ) ^ (2 * b) * T * (2 ^ (γ + 8) * (T : ℝ) ^ 2 * L) * 4 < 2 ^ (6 * b) := by
    have hTL0 : 0 ≤ (T : ℝ) * L := by positivity
    have e1 : (2 : ℝ) ^ (2 * b) * T * (2 ^ (γ + 8) * (T : ℝ) ^ 2 * L) * 4 =
        2 ^ (2 * b) * 2 ^ (γ + 8) * 4 * (T : ℝ) ^ 2 * (T * L) := by ring
    have h3 : (2 : ℝ) ^ (2 * b) * 2 ^ (γ + 8) * 4 * (T : ℝ) ^ 2 * (T * L) ≤
        2 ^ (2 * b) * 2 ^ (γ + 8) * 4 * 2 ^ (2 * b) * (T * L) := by gcongr
    have h4 : (2 : ℝ) ^ (2 * b) * 2 ^ (γ + 8) * 4 * 2 ^ (2 * b) * (T * L) <
        2 ^ (2 * b) * 2 ^ (γ + 8) * 4 * 2 ^ (2 * b) * 2 ^ (b + 3) :=
      mul_lt_mul_of_pos_left hTL (by positivity)
    have h5 : (2 : ℝ) ^ (2 * b) * 2 ^ (γ + 8) * 4 * 2 ^ (2 * b) * 2 ^ (b + 3) =
        2 ^ (5 * b + γ + 13) := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
      congr 1; ring
    have h6 : (2 : ℝ) ^ (5 * b + γ + 13) ≤ 2 ^ (6 * b) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hfin : (2 : ℝ) ^ (2 * b) * T * D * 4 < 1 := by
    have hpos : (0 : ℝ) < 2 ^ (6 * b) := by positivity
    have : (2 : ℝ) ^ (2 * b) * T * D * 4 * 2 ^ (6 * b) < 1 * 2 ^ (6 * b) := by
      calc (2 : ℝ) ^ (2 * b) * T * D * 4 * 2 ^ (6 * b)
          = 2 ^ (2 * b) * T * 4 * (D * 2 ^ (6 * b)) := by ring
        _ ≤ 2 ^ (2 * b) * T * 4 * (2 ^ (γ + 8) * (T : ℝ) ^ 2 * L) :=
          mul_le_mul_of_nonneg_left hD.le (by positivity)
        _ = 2 ^ (2 * b) * T * (2 ^ (γ + 8) * (T : ℝ) ^ 2 * L) * 4 := by ring
        _ < 2 ^ (6 * b) := key
        _ = 1 * 2 ^ (6 * b) := (one_mul _).symm
    exact lt_of_mul_lt_mul_right this hpos.le
  have hSD : (2 : ℝ) ^ (2 * b) * S * D ≤ 2 ^ (2 * b) * T * D := by gcongr
  linarith
