-- Prove2me | solution 1 for MatrixSpencer.eq_2_14
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-13T12:18:03.190213+00:00
-- url     : https://prove2.me/submissions/6384e800-7e53-4698-8d85-91e68228ba14

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open scoped BigOperators
open Real

private lemma scalar_bound {x u D d : ℝ} (hx : 0 < x) (hxu : x ≤ u)
    (huD : u ≤ D) (hd : 0 ≤ d) (hdD : d ≤ D) :
    x * max 1 (log (d / x)) ≤ u * (1 + log (2 * D / u)) := by
  have hu : 0 < u := lt_of_lt_of_le hx hxu
  have hD : 0 < D := lt_of_lt_of_le hu huD
  have hq : 0 ≤ log (D / u) := log_nonneg (by rwa [one_le_div hu])
  have hl2 : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hl : log (2 * D / u) = log 2 + log (D / u) := by
    rw [show 2 * D / u = 2 * (D / u) by ring, log_mul (by norm_num) (ne_of_gt (div_pos hD hu))]
  rw [mul_max_of_nonneg _ _ hx.le]
  apply max_le
  · nlinarith [mul_nonneg hu.le hq, mul_nonneg hu.le hl2]
  · by_cases hd0 : d = 0
    · simp only [hd0, zero_div, log_zero, mul_zero]
      rw [hl]
      positivity
    have hdp : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
    have hlog : log (d / x) ≤ log (D / x) :=
      log_le_log (div_pos hdp hx) (div_le_div_of_nonneg_right hdD hx.le)
    have heq : log (D / x) = log (D / u) + log (u / x) := by
      rw [log_div hD.ne' hx.ne', log_div hD.ne' hu.ne', log_div hu.ne' hx.ne']
      ring
    have hr := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hu hx)) hx.le
    have hcancel : x * (u / x - 1) = u - x := by field_simp
    rw [hcancel] at hr
    have hmul := mul_le_mul_of_nonneg_left hlog hx.le
    have hqmul := mul_le_mul_of_nonneg_right hxu hq
    rw [heq] at hmul
    rw [hl]
    nlinarith [mul_nonneg hu.le hl2]

theorem solution (T n d : ℕ) (m : ℕ → ℕ) (hm1 : ∀ k < T, 1 ≤ m k)
    (hm2 : ∀ k < T, (m k : ℝ) ≤ (n : ℝ) / 2 ^ k) :
    let L : ℝ := 1 + Real.log (2 * ((max d n : ℕ) : ℝ) / n)
    let a : ℕ → ℝ := fun k => (2 : ℝ) ^ (-(k : ℝ) / 2) * √(1 + (k : ℝ) * Real.log 2 / L)
    let b : ℕ → ℝ := fun k => (1 + (k : ℝ)) * (2 : ℝ) ^ (-(k : ℝ) / 2)
    Summable a ∧ Summable b ∧
    ∑ k ∈ Finset.range T, √((m k : ℝ) * max 1 (Real.log ((d : ℝ) / m k))) ≤
      √((n : ℝ) * L) * ∑' k, a k ∧
    √((n : ℝ) * L) * ∑' k, a k ≤ √((n : ℝ) * L) * ∑' k, b k ∧
    √((n : ℝ) * L) * ∑' k, b k = √((n : ℝ) * L) / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 ∧
    √((n : ℝ) * L) / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 ≤
      (√(2 + Real.log 2) / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2) *
        (√(n : ℝ) * √(max 1 (Real.log ((d : ℝ) / n)))) := by
  dsimp only
  let L : ℝ := 1 + log (2 * ((max d n : ℕ) : ℝ) / n)
  let r : ℝ := (2 : ℝ) ^ (-(1 / 2) : ℝ)
  let a : ℕ → ℝ := fun k => (2 : ℝ) ^ (-(k : ℝ) / 2) * √(1 + (k : ℝ) * log 2 / L)
  let b : ℕ → ℝ := fun k => (1 + (k : ℝ)) * (2 : ℝ) ^ (-(k : ℝ) / 2)
  change Summable a ∧ Summable b ∧ _ ∧ _ ∧ _ ∧ _
  have hl2 : 0 ≤ log 2 := log_nonneg (by norm_num)
  have hl21 : log 2 ≤ 1 := by
    have := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hL : 1 ≤ L := by
    by_cases hn : n = 0
    · simp [L, hn]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hDn : (n : ℝ) ≤ ((max d n : ℕ) : ℝ) := by exact_mod_cast le_max_right d n
    have harg : (1 : ℝ) ≤ 2 * ((max d n : ℕ) : ℝ) / n := by
      rw [le_div_iff₀ hnpos]
      linarith
    have := log_nonneg harg
    dsimp [L]
    linarith
  have hLp : 0 < L := by linarith
  have hrp : 0 < r := rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hrnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hrp]
  have hq (k : ℕ) : (2 : ℝ) ^ (-(k : ℝ) / 2) = r ^ k := by
    dsimp [r]
    rw [← rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hb : Summable b := by
    have hg := summable_geometric_of_norm_lt_one hrnorm
    have hk := (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable
    simpa only [b, hq, add_mul, one_mul] using hg.add hk
  have hab (k : ℕ) : a k ≤ b k := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hratio : log 2 / L ≤ 1 := (div_le_one hLp).mpr (hl21.trans hL)
    have hs : √(1 + (k : ℝ) * log 2 / L) ≤ 1 + k := by
      rw [sqrt_le_iff]
      constructor
      · positivity
      · have hprod := mul_le_mul_of_nonneg_left hratio hk
        rw [← mul_div_assoc] at hprod
        have := sq_nonneg (k : ℝ)
        nlinarith
    dsimp [a, b]
    nlinarith [mul_le_mul_of_nonneg_left hs (rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-(k : ℝ) / 2))]
  have ha : Summable a := Summable.of_nonneg_of_le (fun k => by dsimp [a]; positivity) hab hb
  have hbval : ∑' k, b k = 1 / (1 - r) ^ 2 := by
    have hg := summable_geometric_of_norm_lt_one hrnorm
    have hk := (hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).summable
    simp only [b, hq, add_mul, one_mul]
    rw [hg.tsum_add hk, tsum_geometric_of_norm_lt_one hrnorm,
      tsum_coe_mul_geometric_of_norm_lt_one hrnorm]
    field_simp
    <;> ring
  refine ⟨ha, hb, ?_, ?_, ?_, ?_⟩
  · by_cases hn : n = 0
    · have hT : T = 0 := by
        by_contra hT
        have h0 := hm2 0 (Nat.pos_of_ne_zero hT)
        have h1 := hm1 0 (Nat.pos_of_ne_zero hT)
        simp only [hn, Nat.cast_zero, zero_div] at h0
        have : (1 : ℝ) ≤ m 0 := by exact_mod_cast h1
        linarith
      simp [hT, hn]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hDn : (n : ℝ) ≤ ((max d n : ℕ) : ℝ) := by exact_mod_cast le_max_right d n
    have hDpos : (0 : ℝ) < ((max d n : ℕ) : ℝ) := lt_of_lt_of_le hnpos hDn
    have stage (k : ℕ) (hk : k ∈ Finset.range T) :
        √((m k : ℝ) * max 1 (log ((d : ℝ) / m k))) ≤ √((n : ℝ) * L) * a k := by
      have hkT := Finset.mem_range.mp hk
      have hmp : (0 : ℝ) < m k := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (hm1 k hkT))
      have hpow : (0 : ℝ) < 2 ^ k := by positivity
      have hu : (n : ℝ) / 2 ^ k ≤ ((max d n : ℕ) : ℝ) :=
        (div_le_self hnpos.le (one_le_pow₀ (by norm_num) : (1 : ℝ) ≤ 2 ^ k)).trans hDn
      have hdD : (d : ℝ) ≤ ((max d n : ℕ) : ℝ) := by exact_mod_cast le_max_left d n
      have hs := scalar_bound hmp (hm2 k hkT) hu (Nat.cast_nonneg d) hdD
      have hlog : log (2 * ((max d n : ℕ) : ℝ) / ((n : ℝ) / 2 ^ k)) = L + (k : ℝ) * log 2 - 1 := by
        dsimp [L]
        rw [show 2 * ((max d n : ℕ) : ℝ) / ((n : ℝ) / 2 ^ k) =
          (2 * ((max d n : ℕ) : ℝ) / n) * 2 ^ k by field_simp]
        rw [log_mul (by positivity) hpow.ne', log_pow]
        ring
      rw [hlog] at hs
      have hqsq : ((2 : ℝ) ^ (-(k : ℝ) / 2)) ^ 2 = 1 / (2 : ℝ) ^ k := by
        rw [← rpow_natCast, ← rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num only [Nat.cast_ofNat]
        rw [show -(k : ℝ) / 2 * (2 : ℝ) = -(k : ℝ) by ring, rpow_neg (by norm_num), rpow_natCast]
        simp only [one_div]
      have hsqr : (√((n : ℝ) * L) * a k) ^ 2 = ((n : ℝ) / 2 ^ k) * (L + (k : ℝ) * log 2) := by
        dsimp [a]
        rw [mul_pow, mul_pow, sq_sqrt (by positivity), hqsq, sq_sqrt (by positivity)]
        field_simp
        <;> ring
      rw [sqrt_le_iff]
      exact ⟨by dsimp [a]; positivity, by rw [hsqr]; linarith [hs]⟩
    calc
      _ ≤ ∑ k ∈ Finset.range T, √((n : ℝ) * L) * a k := Finset.sum_le_sum stage
      _ = √((n : ℝ) * L) * ∑ k ∈ Finset.range T, a k := by rw [Finset.mul_sum]
      _ ≤ √((n : ℝ) * L) * ∑' k, a k :=
        mul_le_mul_of_nonneg_left (ha.sum_le_tsum (Finset.range T) (fun k _ => by dsimp [a]; positivity)) (sqrt_nonneg _)
  · exact mul_le_mul_of_nonneg_left (ha.tsum_le_tsum hab hb) (sqrt_nonneg _)
  · rw [hbval]
    dsimp [r]
    ring
  · by_cases hn : n = 0
    · simp [hn]
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hbound : L ≤ (2 + log 2) * max 1 (log ((d : ℝ) / n)) := by
      by_cases hdn : d ≤ n
      · have hLn : L = 1 + log 2 := by simp [L, max_eq_right hdn, hnpos.ne']
        rw [hLn]
        have := le_max_left (1 : ℝ) (log ((d : ℝ) / n))
        nlinarith [mul_le_mul_of_nonneg_left this hl2]
      · have hnd : n ≤ d := Nat.le_of_lt (Nat.lt_of_not_ge hdn)
        have hdp : (0 : ℝ) < d := by exact_mod_cast lt_of_lt_of_le (Nat.pos_of_ne_zero hn) hnd
        have hLd : L = 1 + log 2 + log ((d : ℝ) / n) := by
          dsimp [L]
          rw [max_eq_left hnd, show 2 * (d : ℝ) / n = 2 * ((d : ℝ) / n) by ring,
            log_mul (by norm_num) (ne_of_gt (div_pos hdp hnpos))]
          ring
        rw [hLd]
        have h1 := le_max_left (1 : ℝ) (log ((d : ℝ) / n))
        have h2 := le_max_right (1 : ℝ) (log ((d : ℝ) / n))
        nlinarith [mul_le_mul_of_nonneg_left h1 hl2]
    have hsq : √((n : ℝ) * L) ≤ √(2 + log 2) * (√(n : ℝ) * √(max 1 (log ((d : ℝ) / n)))) := by
      rw [sqrt_le_iff]
      constructor
      · positivity
      · rw [mul_pow, mul_pow, sq_sqrt (by positivity), sq_sqrt (Nat.cast_nonneg n), sq_sqrt (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hbound hnpos.le]
    have := div_le_div_of_nonneg_right hsq (sq_nonneg (1 - r))
    dsimp only [r] at this
    simpa only [div_mul_eq_mul_div] using this

#print axioms solution



