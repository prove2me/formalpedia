-- Prove2me | solution 1 for KalaiKleitman92.Diameter.bound_recursion
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T02:12:27.471478+00:00
-- url     : https://prove2.me/submissions/64ed5fba-2ffb-4702-a443-e1c3a9dad8f1

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Aux_KK92_bound_recursion

lemma rpow_logb_swap {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x ^ Real.logb 2 y = y ^ Real.logb 2 x := by
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, Real.logb, Real.logb]
  congr 1
  ring

lemma two_rpow_logb {x : ℝ} (hx : 0 < x) :
    (2 : ℝ) ^ Real.logb 2 x = x := by
  rw [rpow_logb_swap (by norm_num : (0 : ℝ) < 2) hx]
  have hlog2 : Real.logb 2 (2 : ℝ) = 1 := by
    unfold Real.logb
    exact div_self (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  rw [hlog2, Real.rpow_one]

lemma rpow_two_eq_sq (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

end Aux_KK92_bound_recursion

open Aux_KK92_bound_recursion

theorem solution (d n : ℕ) (hd : 2 ≤ d) (hn : d + 1 ≤ n) :
    ⌊((n - 1 : ℕ) : ℝ) ^ (Real.logb 2 ((d - 1 : ℕ) : ℝ) + 2)⌋₊
      + 2 * ⌊((n / 2 : ℕ) : ℝ) ^ (Real.logb 2 (d : ℝ) + 2)⌋₊ + 2
      ≤ ⌊(n : ℝ) ^ (Real.logb 2 (d : ℝ) + 2)⌋₊ := by
  have hn3 : 3 ≤ n := by omega
  have hd1_nat : 1 ≤ d - 1 := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hdR : (0 : ℝ) < (d : ℝ) := by positivity
  have hd1R_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hd1_nat
  have hd1R_ge1 : (1 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hd1_nat
  have hdR_ge2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hnR_ge3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
  set t : ℝ := Real.logb 2 (n : ℝ) with ht_def
  have ht1 : (1 : ℝ) ≤ t := by
    rw [ht_def, Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hnR, Real.rpow_one]
    linarith
  have ht0 : 0 ≤ t - 1 := by linarith
  have hlog_d1_nn : 0 ≤ Real.logb 2 ((d - 1 : ℕ) : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hd1R_pos, Real.rpow_zero]
    exact hd1R_ge1
  have hlog_d_nn : 0 ≤ Real.logb 2 (d : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hdR, Real.rpow_zero]
    linarith
  set e₁ : ℝ := Real.logb 2 ((d - 1 : ℕ) : ℝ) + 2
  set e₂ : ℝ := Real.logb 2 (d : ℝ) + 2
  have he₁_nn : 0 ≤ e₁ := by linarith
  have he₂_nn : 0 ≤ e₂ := by linarith
  have hC_eq : (n : ℝ) ^ e₂ = (d : ℝ) * (d : ℝ) ^ (t - 1) * (n : ℝ) ^ 2 := by
    rw [Real.rpow_add hnR, rpow_logb_swap hnR hdR, ← ht_def, rpow_two_eq_sq]
    have hdt : (d : ℝ) ^ t = (d : ℝ) * (d : ℝ) ^ (t - 1) := by
      conv_lhs => rw [show t = 1 + (t - 1) by ring]
      rw [Real.rpow_add hdR, Real.rpow_one]
    rw [hdt]
  have hn1_le : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hd1_eq : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  have hA_le : ((n - 1 : ℕ) : ℝ) ^ e₁ ≤ ((d : ℝ) - 1) * (d : ℝ) ^ (t - 1) * (n : ℝ) ^ 2 := by
    have h1 : ((n - 1 : ℕ) : ℝ) ^ e₁ ≤ (n : ℝ) ^ e₁ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hn1_le he₁_nn
    have h2 : (n : ℝ) ^ e₁ = ((d - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) ^ (t - 1) * (n : ℝ) ^ 2 := by
      rw [Real.rpow_add hnR, rpow_logb_swap hnR hd1R_pos, ← ht_def, rpow_two_eq_sq]
      have hd1t : ((d - 1 : ℕ) : ℝ) ^ t = ((d - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) ^ (t - 1) := by
        conv_lhs => rw [show t = 1 + (t - 1) by ring]
        rw [Real.rpow_add hd1R_pos, Real.rpow_one]
      rw [hd1t]
    have h3 : ((d - 1 : ℕ) : ℝ) ^ (t - 1) ≤ (d : ℝ) ^ (t - 1) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le d 1) ht0
    have h4 : ((d - 1 : ℕ) : ℝ) * ((d - 1 : ℕ) : ℝ) ^ (t - 1) * (n : ℝ) ^ 2
        ≤ ((d - 1 : ℕ) : ℝ) * (d : ℝ) ^ (t - 1) * (n : ℝ) ^ 2 := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)) ?_
      positivity
    have h5 : ((n - 1 : ℕ) : ℝ) ^ e₁ ≤ ((d - 1 : ℕ) : ℝ) * (d : ℝ) ^ (t - 1) * (n : ℝ) ^ 2 :=
      h1.trans (h2.le.trans h4)
    rwa [hd1_eq] at h5
  have hn2_le : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    have hdiv : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    have hdivR : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdiv
    linarith
  have h2B_le : 2 * ((n / 2 : ℕ) : ℝ) ^ e₂ ≤ (1 / 2 : ℝ) * (d : ℝ) ^ (t - 1) * (n : ℝ) ^ 2 := by
    have hb1 : ((n / 2 : ℕ) : ℝ) ^ e₂ ≤ ((n : ℝ) / 2) ^ e₂ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hn2_le he₂_nn
    have h2e : (2 : ℝ) ^ e₂ = 4 * (d : ℝ) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), two_rpow_logb hdR, rpow_two_eq_sq]
      ring
    have hmul : ((n : ℝ) / 2) ^ e₂ * (4 * (d : ℝ)) = (n : ℝ) ^ e₂ := by
      rw [← h2e, ← Real.mul_rpow (by positivity : 0 ≤ (n : ℝ) / 2) (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    have hhalf_eq : ((n : ℝ) / 2) ^ e₂ = (1 / 4 : ℝ) * (d : ℝ) ^ (t - 1) * (n : ℝ) ^ 2 := by
      have hcomb : ((n : ℝ) / 2) ^ e₂ * (4 * (d : ℝ))
          = ((1 / 4 : ℝ) * (d : ℝ) ^ (t - 1) * (n : ℝ) ^ 2) * (4 * (d : ℝ)) := by
        rw [hmul, hC_eq]
        ring
      exact mul_right_cancel₀ (by positivity : 4 * (d : ℝ) ≠ 0) hcomb
    linarith
  have hd_pow_ge1 : (1 : ℝ) ≤ (d : ℝ) ^ (t - 1) := Real.one_le_rpow (by linarith) ht0
  have hn_sq_ge9 : (9 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have htwo_le : (2 : ℝ) ≤ (1 / 2 : ℝ) * (d : ℝ) ^ (t - 1) * (n : ℝ) ^ 2 := by nlinarith
  have hfA : (⌊((n - 1 : ℕ) : ℝ) ^ e₁⌋₊ : ℝ) ≤ ((n - 1 : ℕ) : ℝ) ^ e₁ :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hfB : (⌊((n / 2 : ℕ) : ℝ) ^ e₂⌋₊ : ℝ) ≤ ((n / 2 : ℕ) : ℝ) ^ e₂ :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine Nat.le_floor ?_
  push_cast
  linarith [hfA, hfB, hA_le, h2B_le, htwo_le, hC_eq]
