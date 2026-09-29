-- Prove2me | solution 1 for LiuPass.entropy_ge_of_statDist_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T20:17:59.207368+00:00
-- url     : https://prove2.me/submissions/77a78264-6ac0-40bd-aa84-850189e29b48

import Mathlib
import Definitions.Def_LiuPass_crypto

set_option autoImplicit false

open Finset
open scoped Classical

open LiuPass in
theorem solution (n : ℕ) (hn : 4 ≤ n) (p : (Fin n → Bool) → ℝ)
    (hp : IsProbVector p) (hsd : statDist p (unifVector (Fin n → Bool)) ≤ 1 / (n : ℝ) ^ 2) :
    (n : ℝ) - 2 ≤ shannonEntropy p := by
  obtain ⟨hp0, hp1⟩ := hp
  have hcard : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by simp
  set u : ℝ := 1 / (2 : ℝ) ^ n with hu
  have hunif : unifVector (Fin n → Bool) = fun _ => u := by
    funext a
    simp only [unifVector, hcard, hu]
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hupos : 0 < u := by positivity
  have hlog2u : Real.logb 2 (2 * u) = 1 - n := by
    rw [hu, Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num),
      one_div, Real.logb_inv, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    ring
  have hle1 : ∀ a, p a ≤ 1 := fun a => by
    rw [← hp1]
    exact Finset.single_le_sum (fun b _ => hp0 b) (Finset.mem_univ a)
  have key : ∀ a, ((n : ℝ) - 1) * p a - 2 * ((n : ℝ) - 1) * |p a - u|
      ≤ -(p a) * Real.logb 2 (p a) := by
    intro a
    have h0 := hp0 a
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
    by_cases hbig : 2 * u < p a
    · have hl : Real.logb 2 (p a) ≤ 0 := Real.logb_nonpos (by norm_num) h0 (hle1 a)
      have habs : |p a - u| = p a - u := abs_of_pos (by linarith)
      rw [habs]
      nlinarith [mul_nonneg h0 (neg_nonneg.mpr hl), mul_nonneg hn1 (by linarith : (0:ℝ) ≤ p a - 2 * u)]
    · replace hbig : p a ≤ 2 * u := not_lt.mp hbig
      rcases h0.eq_or_lt with h | h
      · rw [← h]
        have := abs_nonneg ((0 : ℝ) - u)
        simp only [mul_zero, neg_zero, zero_mul, zero_sub]
        nlinarith [mul_nonneg hn1 (abs_nonneg (-u))]
      · have hl : Real.logb 2 (p a) ≤ 1 - n := by
          rw [← hlog2u]
          exact Real.logb_le_logb_of_le (by norm_num) h hbig
        nlinarith [mul_le_mul_of_nonneg_left hl h0, mul_nonneg hn1 (abs_nonneg (p a - u))]
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (univ : Finset (Fin n → Bool))) => key a)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp1] at hsum
  unfold statDist at hsd
  rw [hunif] at hsd
  unfold shannonEntropy
  have hsd' : ∑ a, |p a - u| ≤ 2 / (n : ℝ) ^ 2 := by
    have : (2 : ℝ) / (n : ℝ) ^ 2 = 2 * (1 / (n : ℝ) ^ 2) := by ring
    rw [this]
    linarith
  have hfin : 2 * ((n : ℝ) - 1) * (2 / (n : ℝ) ^ 2) ≤ 1 := by
    rw [show 2 * ((n : ℝ) - 1) * (2 / (n : ℝ) ^ 2) = (4 * ((n : ℝ) - 1)) / (n : ℝ) ^ 2 by ring]
    rw [div_le_one (by positivity)]
    nlinarith
  have hmul : 2 * ((n : ℝ) - 1) * ∑ a, |p a - u| ≤ 2 * ((n : ℝ) - 1) * (2 / (n : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hsd' (by linarith)
  linarith
