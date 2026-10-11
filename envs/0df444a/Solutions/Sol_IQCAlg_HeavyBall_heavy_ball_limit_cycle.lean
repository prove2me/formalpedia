-- Prove2me | solution 1 for IQCAlg.HeavyBall.heavy_ball_limit_cycle
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T21:00:44.199692+00:00
-- url     : https://prove2.me/submissions/f31c5d50-63ba-4115-a347-eb2e1bff8dbb

import Mathlib
import Definitions.Def_IQCAlg_HeavyBall_Setting

namespace RRAux_IQCAlg_HeavyBall_heavy_ball_limit_cycle

open IQCAlg.HeavyBall

lemma alpha_eq : hbAlpha 25 1 = 1 / 9 := by
  have h : Real.sqrt 25 = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp [hbAlpha, h]
  norm_num

lemma beta_eq : hbBeta 25 1 = 4 / 9 := by
  have h : Real.sqrt 25 = 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp [hbBeta, kappa, h]
  norm_num

noncomputable def x (k : ℕ) : ℝ := hbRun gradF (1 / 9) (4 / 9) (33 / 10) k

lemma x_rec (k : ℕ) : x (k + 2) = x (k + 1) - 1 / 9 * gradF (x (k + 1)) + 4 / 9 * (x (k + 1) - x k) := by
  simp only [x]
  rfl

lemma x0 : x 0 = 33 / 10 := rfl
lemma x1 : x 1 = -16 / 5 := by
  simp only [x, hbRun, gradF]; norm_num
lemma x2 : x 2 = 14 / 5 := by rw [x_rec, x1, x0]; norm_num [gradF]
lemma x3 : x 3 = 16 / 45 := by rw [x_rec, x2, x1]; norm_num [gradF]
lemma x4 : x 4 = -232 / 135 := by rw [x_rec, x3, x2]; norm_num [gradF]
lemma x5 : x 5 = 32 / 15 := by rw [x_rec, x4, x3]; norm_num [gradF]
lemma x6 : x 6 = 712 / 1215 := by rw [x_rec, x5, x4]; norm_num [gradF]
lemma x7 : x 7 = -6304 / 3645 := by rw [x_rec, x6, x5]; norm_num [gradF]
lemma x8 : x 8 = 7456 / 3645 := by rw [x_rec, x7, x6]; norm_num [gradF]
lemma x9 : x 9 = 23224 / 32805 := by rw [x_rec, x8, x7]; norm_num [gradF]

/-- 24 if `k ≡ 2 (mod 3)`, else 0. -/
noncomputable def off (k : ℕ) : ℝ := if k % 3 = 2 then 24 else 0

lemma region (k : ℕ) (y : ℝ) (hy : |y - cyc k| ≤ 1 / 10) : gradF y = 25 * y - off k := by
  rw [abs_le] at hy
  unfold cyc pC qC rC at hy
  unfold gradF off
  have h3 : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
  · simp only [h] at hy ⊢; norm_num at hy
    rw [if_pos (show y < 1 by linarith)]; norm_num
  · simp only [h] at hy ⊢; norm_num at hy
    rw [if_pos (show y < 1 by linarith)]; norm_num
  · simp only [h] at hy ⊢; norm_num at hy
    rw [if_neg (show ¬ y < 1 by linarith), if_neg (show ¬ y < 2 by linarith)]; norm_num

lemma cyc_rec (k : ℕ) :
    cyc (k + 2) = 13 / 9 * cyc (k + 1) - 4 / 9 * cyc k - 1 / 9 * (25 * cyc (k + 1) - off (k + 1)) := by
  unfold cyc off pC qC rC
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
  · have h1 : (k + 1) % 3 = 1 := by omega
    have h2 : (k + 2) % 3 = 2 := by omega
    simp only [h, h1, h2]; norm_num
  · have h1 : (k + 1) % 3 = 2 := by omega
    have h2 : (k + 2) % 3 = 0 := by omega
    simp only [h, h1, h2]; norm_num
  · have h1 : (k + 1) % 3 = 0 := by omega
    have h2 : (k + 2) % 3 = 1 := by omega
    simp only [h, h1, h2]; norm_num

noncomputable def e (k : ℕ) : ℝ := x k - cyc k

lemma e_rec (k : ℕ) (h : |e (k + 1)| ≤ 1 / 10) :
    e (k + 2) = -(4 / 3) * e (k + 1) - 4 / 9 * e k := by
  have hg := region (k + 1) (x (k + 1)) h
  simp only [e]
  rw [x_rec, hg, cyc_rec]
  ring

lemma step_bound (ek ek1 u j1 j2 : ℝ) (hj1 : 0 ≤ j1) (hj2 : j2 ≤ j1)
    (he : |ek| ≤ 1 / 10 * j1) (hu : |u| ≤ 7 / 300 * j2) (hdef : u = ek1 + 2 / 3 * ek) :
    |ek1| ≤ 1 / 10 * (9 / 10 * j1) := by
  have : ek1 = u - 2 / 3 * ek := by linarith
  rw [this]
  calc |u - 2 / 3 * ek| ≤ |u| + |2 / 3 * ek| := abs_sub _ _
    _ = |u| + 2 / 3 * |ek| := by rw [abs_mul]; norm_num
    _ ≤ 7 / 300 * j2 + 2 / 3 * (1 / 10 * j1) := by linarith
    _ ≤ 1 / 10 * (9 / 10 * j1) := by nlinarith

lemma main_bound : ∀ j : ℕ, |e (8 + j)| ≤ 1 / 10 * (9 / 10) ^ j ∧
    |e (8 + j + 1) + 2 / 3 * e (8 + j)| ≤ 7 / 300 * (2 / 3) ^ j := by
  intro j
  induction j with
  | zero =>
    simp only [e, x8, x9, add_zero, pow_zero, mul_one,
      show (8 : ℕ) + 1 = 9 from rfl]
    unfold cyc pC qC rC
    norm_num [abs_le]
  | succ j ih =>
    obtain ⟨he, hu⟩ := ih
    have hpow : (2 / 3 : ℝ) ^ j ≤ (9 / 10) ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
    have he1 : |e (8 + j + 1)| ≤ 1 / 10 * (9 / 10 * (9 / 10) ^ j) :=
      step_bound _ _ _ _ _ (by positivity) hpow he hu rfl
    have he1' : |e (8 + j + 1)| ≤ 1 / 10 := by
      have : (9 / 10 : ℝ) * (9 / 10) ^ j ≤ 1 := by
        have := pow_le_one₀ (n := j) (by norm_num : (0 : ℝ) ≤ 9 / 10) (by norm_num)
        nlinarith
      linarith
    have hrec := e_rec (8 + j) he1'
    refine ⟨?_, ?_⟩
    · rw [show 8 + (j + 1) = 8 + j + 1 by omega, pow_succ]
      linarith [he1]
    · rw [show 8 + (j + 1) + 1 = 8 + j + 2 by omega, show 8 + (j + 1) = 8 + j + 1 by omega, hrec]
      have : -(4 / 3) * e (8 + j + 1) - 4 / 9 * e (8 + j) + 2 / 3 * e (8 + j + 1) =
          -(2 / 3) * (e (8 + j + 1) + 2 / 3 * e (8 + j)) := by ring
      rw [this, abs_mul, pow_succ]
      norm_num
      nlinarith [abs_nonneg (e (8 + j + 1) + 2 / 3 * e (8 + j))]

lemma e_tendsto : Filter.Tendsto e Filter.atTop (nhds 0) := by
  rw [← Filter.tendsto_add_atTop_iff_nat 8]
  have hb : Filter.Tendsto (fun j : ℕ => 1 / 10 * (9 / 10 : ℝ) ^ j) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 9 / 10)
      (by norm_num)).const_mul (1 / 10 : ℝ)
  refine squeeze_zero_norm (fun j => ?_) hb
  rw [Real.norm_eq_abs, add_comm]
  exact (main_bound j).1

lemma lim_along (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) (c : ℝ)
    (hc : ∀ n, cyc (f n) = c) :
    Filter.Tendsto (fun n => x (f n)) Filter.atTop (nhds c) := by
  have h1 := e_tendsto.comp hf
  have h2 : (fun n => x (f n)) = fun n => c + e (f n) := by
    funext n; simp [e, hc n]
  rw [h2]
  simpa using h1.const_add c

end RRAux_IQCAlg_HeavyBall_heavy_ball_limit_cycle

open RRAux_IQCAlg_HeavyBall_heavy_ball_limit_cycle in
open IQCAlg.HeavyBall in
theorem solution :
    Filter.Tendsto (fun n : ℕ => hbRun gradF (hbAlpha 25 1) (hbBeta 25 1) (33 / 10) (3 * n))
        Filter.atTop (nhds (792 / 1225)) ∧
    Filter.Tendsto (fun n : ℕ => hbRun gradF (hbAlpha 25 1) (hbBeta 25 1) (33 / 10) (3 * n + 1))
        Filter.atTop (nhds (-2208 / 1225)) ∧
    Filter.Tendsto (fun n : ℕ => hbRun gradF (hbAlpha 25 1) (hbBeta 25 1) (33 / 10) (3 * n + 2))
        Filter.atTop (nhds (2592 / 1225)) := by
  rw [alpha_eq, beta_eq]
  have ht : ∀ r : ℕ, Filter.Tendsto (fun n : ℕ => 3 * n + r) Filter.atTop Filter.atTop :=
    fun r => Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · exact lim_along (fun n => 3 * n + 0) (ht 0) _ (fun n => by simp [cyc, pC])
  · exact lim_along (fun n => 3 * n + 1) (ht 1) _ (fun n => by simp [cyc, qC, Nat.add_mod])
  · exact lim_along (fun n => 3 * n + 2) (ht 2) _ (fun n => by simp [cyc, rC, Nat.add_mod])

#print axioms solution
