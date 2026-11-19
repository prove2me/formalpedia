-- Prove2me | solution 1 for MarkdownReadjust.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T08:05:02.383204+00:00
-- url     : https://prove2.me/submissions/7db00b0d-02c5-4cc1-954c-671c5c7da10d

import Mathlib
import Definitions.Def_MarkdownReadjust_tgrid
import Definitions.Def_MarkdownReadjust_eta

open MarkdownReadjust Finset Real

theorem solution (lam α : ℝ) (hlam : 0 < lam) (x : ℕ) (hx : 1 ≤ x) (τ : ℝ) (hτ : 0 < τ)
    (N : ℕ) (hN : 1 ≤ N) :
    (∀ n : ℕ, n < N → eta lam α x τ N (n + 1) < eta lam α x τ N n) ∧
      ∑ n ∈ Finset.range (N + 1), (tgrid x τ N (n + 1) - tgrid x τ N n) * eta lam α x τ N n
        = 0 := by
  set r : ℝ := ((x : ℝ) + 1) ^ (-(1 : ℝ) / ((N : ℝ) + 2)) with hr
  have hx1 : (1 : ℝ) < (x : ℝ) + 1 := by have : (1 : ℝ) ≤ x := by exact_mod_cast hx
                                         linarith
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by linarith) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hx1 (by
    have : (0 : ℝ) < (N : ℝ) + 2 := by positivity
    exact div_neg_of_neg_of_pos (by norm_num) this)
  have hpow : ∀ n : ℕ, ((x : ℝ) + 1) ^ (-(n : ℝ) / ((N : ℝ) + 2)) = r ^ n := by
    intro n
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1; ring
  have ht : ∀ n, n ≤ N → tgrid x τ N n = τ * (1 - r ^ n) := by
    intro n hn; unfold tgrid; rw [if_pos hn, hpow]
  have htN : tgrid x τ N (N + 1) = τ := by unfold tgrid; rw [if_neg (by omega)]
  -- increments
  have hD : ∀ n, n < N → tgrid x τ N (n + 1) - tgrid x τ N n = τ * r ^ n * (1 - r) := by
    intro n hn; rw [ht n hn.le, ht (n + 1) hn]; ring
  have hDN : tgrid x τ N (N + 1) - tgrid x τ N N = τ * r ^ N := by
    rw [htN, ht N le_rfl]; ring
  have hT : ∀ m, m < N → τ - tgrid x τ N (m + 1) = τ * r ^ (m + 1) := by
    intro m hm; rw [ht (m + 1) hm]; ring
  set c : ℝ := Real.log ((x : ℝ) + 1) ^ α / Real.sqrt (lam * τ) with hc
  have hc0 : 0 < c := by
    apply div_pos (Real.rpow_pos_of_pos (Real.log_pos hx1) _) (Real.sqrt_pos.mpr (by positivity))
  set g : ℕ → ℝ := fun m => Real.sqrt τ * Real.sqrt (tgrid x τ N (m + 1) - tgrid x τ N m) /
    (τ - tgrid x τ N (m + 1)) with hg
  set A : ℕ → ℝ := fun n => if n < N then Real.sqrt τ / Real.sqrt (tgrid x τ N (n + 1) - tgrid x τ N n) else 0 with hA
  have heta : ∀ n, eta lam α x τ N n = c * (A n - ∑ m ∈ range n, g m) := fun n => rfl
  have hsq : ∀ n, n < N → Real.sqrt (tgrid x τ N (n + 1) - tgrid x τ N n) =
      Real.sqrt τ * (Real.sqrt r) ^ n * Real.sqrt (1 - r) := by
    intro n hn
    have hp : Real.sqrt (r ^ n) = Real.sqrt r ^ n := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
        Real.mul_self_sqrt hr0.le]
    rw [hD n hn, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), hp]
  have hsr : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hs1 : 0 < Real.sqrt (1 - r) := Real.sqrt_pos.mpr (by linarith)
  have hst : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hrr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
  have h1r : Real.sqrt (1 - r) ^ 2 = 1 - r := Real.sq_sqrt (by linarith)
  have hgm : ∀ m, m < N → g m = Real.sqrt (1 - r) / (Real.sqrt r ^ m * r) := by
    intro m hm
    simp only [hg]
    have hrm : r ^ (m + 1) = (Real.sqrt r ^ m) ^ 2 * r := by
      rw [← pow_mul, pow_mul', hrr, pow_succ]
    rw [hsq m hm, hT m hm, hrm]
    set st := Real.sqrt τ with hst'
    set sr := Real.sqrt r with hsr'
    set su := Real.sqrt (1 - r) with hsu'
    have hτ2 : τ = st ^ 2 := (Real.sq_sqrt hτ.le).symm
    rw [hτ2]
    field_simp
  have hAn : ∀ n, n < N → A n = 1 / (Real.sqrt r ^ n * Real.sqrt (1 - r)) := by
    intro n hn
    simp only [hA, if_pos hn]
    rw [hsq n hn]; field_simp
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [heta, heta, sum_range_succ]
    apply mul_lt_mul_of_pos_left _ hc0
    rw [hAn n hn, hgm n hn]
    by_cases hn1 : n + 1 < N
    · rw [hAn (n + 1) hn1]
      have keyg : ∀ sq u P : ℝ, 0 < sq → sq < 1 → 0 < u → 0 < P → sq ^ 2 = r → u ^ 2 = 1 - r →
          1 / (P * sq * u) < 1 / (P * u) + u / (P * r) := by
        intro sq u P hs hs1 hu hP hsr' hur
        rw [← hsr']
        rw [div_add_div _ _ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity) (by positivity)]
        have h0 : P * P * sq * u * (u ^ 2 - (1 - sq ^ 2)) = 0 := by rw [hur, hsr']; ring
        nlinarith [mul_pos (mul_pos (mul_pos (mul_pos hP hP) hs) hu) (sub_pos.mpr hs1)]
      have hs1' : Real.sqrt r < 1 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt hr0.le hr1
      have key := keyg (Real.sqrt r) (Real.sqrt (1 - r)) (Real.sqrt r ^ n) hsr hs1' hs1 (pow_pos hsr n) hrr h1r
      rw [pow_succ]
      rw [show Real.sqrt r ^ n * Real.sqrt r * Real.sqrt (1 - r) = Real.sqrt r ^ n * Real.sqrt r * Real.sqrt (1 - r) from rfl]
      linarith
    · have : A (n + 1) = 0 := by simp only [hA]; rw [if_neg hn1]
      rw [this]
      have : 0 < 1 / (Real.sqrt r ^ n * Real.sqrt (1 - r)) + Real.sqrt (1 - r) / (Real.sqrt r ^ n * r) := by
        positivity
      linarith
  · simp_rw [heta]
    have e1 : ∀ n ∈ range (N + 1), (tgrid x τ N (n + 1) - tgrid x τ N n) * (c * (A n - ∑ m ∈ range n, g m)) =
        c * ((tgrid x τ N (n + 1) - tgrid x τ N n) * A n -
          ∑ m ∈ range n, (tgrid x τ N (n + 1) - tgrid x τ N n) * g m) := by
      intro n _; rw [← mul_sum]; ring
    rw [sum_congr rfl e1, ← mul_sum, sum_sub_distrib]
    apply mul_eq_zero_of_right
    rw [sub_eq_zero]
    -- swap
    rw [sum_comm' (t' := range N) (s' := fun m => Ico (m + 1) (N + 1))
      (h := by intro n m; simp only [mem_range, mem_Ico]; omega)]
    rw [sum_range_succ]
    simp only [hA, lt_irrefl, if_false, mul_zero, add_zero]
    apply sum_congr rfl; intro m hm
    rw [mem_range] at hm
    rw [if_pos hm, ← sum_mul]
    have htel : ∑ n ∈ Ico (m + 1) (N + 1), (tgrid x τ N (n + 1) - tgrid x τ N n) =
        τ - tgrid x τ N (m + 1) := by
      rw [sum_Ico_eq_sum_range]
      have := sum_range_sub (fun k => tgrid x τ N (m + 1 + k)) (N + 1 - (m + 1))
      rw [show m + 1 + (N + 1 - (m + 1)) = N + 1 by omega, add_zero, htN] at this
      rw [← this]; apply sum_congr rfl; intro k _; rw [Nat.add_assoc (m + 1) k 1]
    rw [htel]
    have hTm : τ - tgrid x τ N (m + 1) ≠ 0 := by rw [hT m hm]; positivity
    have hDm : 0 < tgrid x τ N (m + 1) - tgrid x τ N m := by rw [hD m hm]; have := pow_pos hr0 m; nlinarith [mul_pos hτ (mul_pos this (by linarith : (0:ℝ) < 1 - r))]
    simp only [hg]
    set w := Real.sqrt (tgrid x τ N (m + 1) - tgrid x τ N m) with hw
    have hwsq : w ^ 2 = tgrid x τ N (m + 1) - tgrid x τ N m := Real.sq_sqrt hDm.le
    have hw0 : 0 < w := Real.sqrt_pos.mpr hDm
    rw [← hwsq]
    field_simp
