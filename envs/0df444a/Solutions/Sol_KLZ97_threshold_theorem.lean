-- Prove2me | solution 1 for KLZ97.threshold_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T07:48:24.595981+00:00
-- url     : https://prove2.me/submissions/2998d5e9-e207-45a2-ba28-cb4f029a45fe

import Mathlib
import Definitions.Def_KLZ97_model

open KLZ97

namespace Ag2Aux_KLZThreshold

theorem closed (f p : ℝ) (h : ℕ) :
    levelError f p h = f ^ (2 ^ h - 1) * p ^ (2 ^ h) := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [levelError_succ, ih]
    have h1 : 1 ≤ 2 ^ h := Nat.one_le_two_pow
    have h2 : 2 ^ (h + 1) - 1 = 2 * (2 ^ h - 1) + 1 := by rw [pow_succ]; omega
    rw [h2, show 2 ^ (h + 1) = 2 ^ h * 2 by ring, pow_add, pow_mul, pow_mul]
    ring

theorem thr (f p : ℝ) (hf : f ≠ 0) (h : ℕ) :
    levelError f p h = (f * p) ^ (2 ^ h) / f := by
  rw [closed, mul_pow]
  have h1 : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have : f ^ (2 ^ h) = f ^ (2 ^ h - 1) * f := by
    rw [← pow_succ]; congr 1; omega
  rw [this]; field_simp

theorem levels (f p q : ℝ) (n : ℕ) (h : ℕ) (hp : 0 < f * p) (hfp : f * p < 1)
    (hq : 0 < q) (hqn : q < n)
    (hlevels : Real.log ((n : ℝ) / q) / Real.log (1 / (f * p)) < (2 : ℝ) ^ h) :
    (n : ℝ) * (f * p) ^ (2 ^ h) < q := by
  have hn : (0 : ℝ) < n := lt_trans hq hqn
  have hL : 0 < Real.log (1 / (f * p)) := Real.log_pos (by rw [lt_div_iff₀ hp]; linarith)
  rw [div_lt_iff₀ hL] at hlevels
  rw [one_div, Real.log_inv] at hlevels
  have hx : 0 < (n : ℝ) / q * (f * p) ^ (2 ^ h) := by positivity
  have hlog : Real.log ((n : ℝ) / q * (f * p) ^ (2 ^ h)) < 0 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    linarith
  have := (Real.log_neg_iff hx).1 hlog
  rw [div_mul_eq_mul_div, div_lt_one hq] at this
  exact this

theorem overhead (K L : ℝ) (hK : 2 ≤ K) (hL : 1 ≤ L) :
    K ^ (⌈Real.logb 2 L⌉₊) ≤ K * L ^ Real.logb 2 K := by
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < L := by linarith
  have hlb : 0 ≤ Real.logb 2 L := Real.logb_nonneg (by norm_num) hL
  have hc : (⌈Real.logb 2 L⌉₊ : ℝ) ≤ Real.logb 2 L + 1 := (Nat.ceil_lt_add_one hlb).le
  have h1 : K ^ (⌈Real.logb 2 L⌉₊) ≤ K ^ (Real.logb 2 L + 1) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hK1 hc
  have h2 : K ^ (Real.logb 2 L + 1) = K * L ^ Real.logb 2 K := by
    rw [Real.rpow_add hK0, Real.rpow_one, mul_comm]
    congr 1
    rw [Real.rpow_def_of_pos hK0, Real.rpow_def_of_pos hL0, Real.logb, Real.logb]
    congr 1; ring
  exact h1.trans h2.le

end Ag2Aux_KLZThreshold

open Ag2Aux_KLZThreshold

theorem solution (f K p q : ℝ) (n : ℕ) (hf : 1 ≤ f) (hK : 2 ≤ K) (hp : 0 ≤ p)
    (hthreshold : p < 1 / f) (hq : 0 < q) (hqn : q < n) :
    ∃ h : ℕ, (n : ℝ) * levelError f p h < q ∧
      K ^ h ≤ K ^ 2 *
        (max 1 (Real.log ((n : ℝ) / q) / Real.log (1 / (f * p)))) ^ Real.logb 2 K := by
  have hf0 : 0 < f := by linarith
  have hK0 : 0 < K := by linarith
  set M := max 1 (Real.log ((n : ℝ) / q) / Real.log (1 / (f * p))) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := by linarith
  refine ⟨⌈Real.logb 2 M⌉₊ + 1, ?_, ?_⟩
  · rcases hp.lt_or_eq with hp' | hp'
    · have hfp : 0 < f * p := by positivity
      have hfp1 : f * p < 1 := by rw [lt_div_iff₀ hf0] at hthreshold; linarith
      rw [thr f p hf0.ne']
      have key := levels f p q n (⌈Real.logb 2 M⌉₊ + 1) hfp hfp1 hq hqn (by
        have h1 : Real.log ((n : ℝ) / q) / Real.log (1 / (f * p)) ≤ M := le_max_right _ _
        have h2 : M ≤ (2 : ℝ) ^ (⌈Real.logb 2 M⌉₊) := by
          have := Nat.le_ceil (Real.logb 2 M)
          calc M = (2 : ℝ) ^ (Real.logb 2 M) := (Real.rpow_logb (by norm_num) (by norm_num) hM0).symm
            _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 M⌉₊ : ℕ) : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) this
            _ = _ := Real.rpow_natCast _ _
        have h3 : (2 : ℝ) ^ (⌈Real.logb 2 M⌉₊) < (2 : ℝ) ^ (⌈Real.logb 2 M⌉₊ + 1) := by
          rw [pow_succ]; have : (0:ℝ) < 2 ^ (⌈Real.logb 2 M⌉₊) := by positivity
          linarith
        linarith)
      have hpow : 0 ≤ (f * p) ^ (2 ^ (⌈Real.logb 2 M⌉₊ + 1)) := by positivity
      have : (n : ℝ) * ((f * p) ^ (2 ^ (⌈Real.logb 2 M⌉₊ + 1)) / f) ≤
          (n : ℝ) * (f * p) ^ (2 ^ (⌈Real.logb 2 M⌉₊ + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact div_le_self hpow hf
      linarith
    · subst hp'
      have : levelError f 0 (⌈Real.logb 2 M⌉₊ + 1) = 0 := by
        rw [closed]; simp
      rw [this]; simpa using hq
  · have := overhead K M hK hM1
    rw [pow_succ, sq]
    calc K ^ ⌈Real.logb 2 M⌉₊ * K ≤ K * M ^ Real.logb 2 K * K :=
          mul_le_mul_of_nonneg_right this hK0.le
      _ = K * K * M ^ Real.logb 2 K := by ring
