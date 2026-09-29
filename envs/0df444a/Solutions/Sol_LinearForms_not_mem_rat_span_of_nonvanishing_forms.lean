-- Prove2me | solution 1 for LinearForms.not_mem_rat_span_of_nonvanishing_forms
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T20:46:15.7607+00:00
-- url     : https://prove2.me/submissions/cd51af5e-66d3-43a9-a6ca-22d0c727f608

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Topology

theorem solution (x y : ℝ) (p q r : ℕ → ℤ)
    (h0 : ∀ n, (p n : ℝ) + q n * x + r n * y ≠ 0)
    (h1 : Tendsto (fun n : ℕ => (p n : ℝ) + q n * x + r n * y) atTop (𝓝 0))
    (h2 : Tendsto (fun n : ℕ =>
      |(p n : ℝ) + q n * x + r n * y| * (|(q (n + 1) : ℝ)| + |(r (n + 1) : ℝ)|)
        + |(p (n + 1) : ℝ) + q (n + 1) * x + r (n + 1) * y| * (|(q n : ℝ)| + |(r n : ℝ)|))
      atTop (𝓝 0)) :
    ∀ α β : ℚ, y ≠ α + β * x := by
  intro α β hy
  set d : ℤ := (α.den : ℤ) * β.den with hd_def
  set a : ℤ := α.num * β.den
  set b : ℤ := β.num * α.den
  have hd : 0 < d := by positivity
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdy : (d : ℝ) * y = a + b * x := by
    rw [hy, Rat.cast_def, Rat.cast_def]
    have ha : (α.den : ℝ) ≠ 0 := by positivity
    have hb : (β.den : ℝ) ≠ 0 := by positivity
    simp only [d, a, b]; push_cast
    field_simp
  -- collapsed integer forms
  obtain ⟨m, hm⟩ : ∃ m : ℕ → ℤ, ∀ n, m n = d * p n + a * r n := ⟨_, fun _ => rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ → ℤ, ∀ n, k n = d * q n + b * r n := ⟨_, fun _ => rfl⟩
  have hL : ∀ n, (m n : ℝ) + k n * x = d * ((p n : ℝ) + q n * x + r n * y) := by
    intro n; rw [hm, hk]; push_cast; linear_combination (-(r n : ℝ)) * hdy
  have hv : ∀ n, m n ≠ 0 ∨ k n ≠ 0 := by
    intro n
    by_contra h
    push Not at h
    have := hL n
    rw [h.1, h.2] at this
    have h' : (d : ℝ) * ((p n : ℝ) + q n * x + r n * y) = 0 := by rw [← this]; simp
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact hdR.ne' h''
    · exact h0 n h''
  set c : ℝ := (d : ℝ) + |(b : ℝ)|
  have hkb : ∀ n, |(k n : ℝ)| ≤ c * (|(q n : ℝ)| + |(r n : ℝ)|) := by
    intro n
    rw [hk]; push_cast
    have e1 : |(d : ℝ) * q n| = d * |(q n : ℝ)| := by rw [abs_mul, abs_of_pos hdR]
    have e2 : |(b : ℝ) * r n| = |(b : ℝ)| * |(r n : ℝ)| := abs_mul _ _
    have := abs_add_le ((d : ℝ) * q n) ((b : ℝ) * r n)
    have hb := abs_nonneg (b : ℝ)
    have hq := abs_nonneg (q n : ℝ)
    have hr := abs_nonneg (r n : ℝ)
    simp only [c]; nlinarith
  -- key estimate on the 2x2 determinant
  have hΔ : ∀ n, |((m n * k (n + 1) - m (n + 1) * k n : ℤ) : ℝ)| ≤ d * c *
      (|(p n : ℝ) + q n * x + r n * y| * (|(q (n + 1) : ℝ)| + |(r (n + 1) : ℝ)|)
        + |(p (n + 1) : ℝ) + q (n + 1) * x + r (n + 1) * y| * (|(q n : ℝ)| + |(r n : ℝ)|)) := by
    intro n
    have eq : ((m n * k (n + 1) - m (n + 1) * k n : ℤ) : ℝ)
        = d * (((p n : ℝ) + q n * x + r n * y) * k (n + 1)
          - ((p (n + 1) : ℝ) + q (n + 1) * x + r (n + 1) * y) * k n) := by
      push_cast
      linear_combination (k (n + 1) : ℝ) * hL n - (k n : ℝ) * hL (n + 1)
    rw [eq, abs_mul, abs_of_pos hdR]
    have t := abs_sub (((p n : ℝ) + q n * x + r n * y) * (k (n + 1) : ℝ))
      (((p (n + 1) : ℝ) + q (n + 1) * x + r (n + 1) * y) * (k n : ℝ))
    rw [abs_mul, abs_mul] at t
    have u1 := mul_le_mul_of_nonneg_left (hkb (n + 1))
      (abs_nonneg ((p n : ℝ) + q n * x + r n * y))
    have u2 := mul_le_mul_of_nonneg_left (hkb n)
      (abs_nonneg ((p (n + 1) : ℝ) + q (n + 1) * x + r (n + 1) * y))
    have : |((p n : ℝ) + q n * x + r n * y) * (k (n + 1) : ℝ)
        - ((p (n + 1) : ℝ) + q (n + 1) * x + r (n + 1) * y) * (k n : ℝ)|
        ≤ c * (|(p n : ℝ) + q n * x + r n * y| * (|(q (n + 1) : ℝ)| + |(r (n + 1) : ℝ)|)
          + |(p (n + 1) : ℝ) + q (n + 1) * x + r (n + 1) * y| * (|(q n : ℝ)| + |(r n : ℝ)|)) := by
      nlinarith
    calc (d : ℝ) * |_| ≤ d * (c * _) := mul_le_mul_of_nonneg_left this hdR.le
      _ = _ := by ring
  have hc : 0 < (d : ℝ) * c := by positivity
  have hev := h2.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (d * c) by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hzero : ∀ n, N ≤ n → m n * k (n + 1) - m (n + 1) * k n = 0 := by
    intro n hn
    have h3 := hN n hn
    have h4 := hΔ n
    rw [lt_div_iff₀ hc] at h3
    have h5 : |((m n * k (n + 1) - m (n + 1) * k n : ℤ) : ℝ)| < 1 := by nlinarith
    rw [← Int.cast_abs] at h5
    have h6 : |m n * k (n + 1) - m (n + 1) * k n| < 1 := by exact_mod_cast h5
    have := abs_lt.mp h6; omega
  -- propagation: all later vectors are parallel to v_N
  have hpar : ∀ n, N ≤ n → m N * k n - m n * k N = 0 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => ring
    | succ n hn ih =>
      have hz := hzero n hn
      have e1 : m n * (m N * k (n + 1) - m (n + 1) * k N) = 0 := by
        linear_combination (m (n + 1)) * ih + m N * hz
      have e2 : k n * (m N * k (n + 1) - m (n + 1) * k N) = 0 := by
        linear_combination (k (n + 1)) * ih + k N * hz
      rcases hv n with h | h
      · exact (mul_eq_zero.mp e1).resolve_left h
      · exact (mul_eq_zero.mp e2).resolve_left h
  -- lower bound
  set LN : ℝ := (p N : ℝ) + q N * x + r N * y
  set S : ℝ := |(m N : ℝ)| + |(k N : ℝ)|
  have hS : 0 < S := by
    rcases hv N with h | h
    · have : (0 : ℝ) < |(m N : ℝ)| := by positivity
      positivity
    · have : (0 : ℝ) < |(k N : ℝ)| := by positivity
      positivity
  have hlow : ∀ n, N ≤ n → |LN| ≤ |(p n : ℝ) + q n * x + r n * y| * S := by
    intro n hn
    have hp : (m N : ℝ) * k n - m n * k N = 0 := by exact_mod_cast hpar n hn
    have Em : ((p n : ℝ) + q n * x + r n * y) * m N = m n * LN := by
      apply mul_left_cancel₀ hdR.ne'
      linear_combination -(m N : ℝ) * hL n + (m n : ℝ) * hL N + x * hp
    have Ek : ((p n : ℝ) + q n * x + r n * y) * k N = k n * LN := by
      apply mul_left_cancel₀ hdR.ne'
      linear_combination -(k N : ℝ) * hL n + (k n : ℝ) * hL N - hp
    have hmN := abs_nonneg (m N : ℝ)
    have hkN := abs_nonneg (k N : ℝ)
    have hLn := abs_nonneg ((p n : ℝ) + q n * x + r n * y)
    have hLN := abs_nonneg LN
    rcases hv n with h | h
    · have h1' : (1 : ℝ) ≤ |(m n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
      have := congrArg abs Em
      rw [abs_mul, abs_mul] at this
      nlinarith
    · have h1' : (1 : ℝ) ≤ |(k n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h
      have := congrArg abs Ek
      rw [abs_mul, abs_mul] at this
      nlinarith
  have hLN : 0 < |LN| := abs_pos.mpr (h0 N)
  have hev2 := (tendsto_zero_iff_abs_tendsto_zero _).mp h1 |>.eventually
    (gt_mem_nhds (show (0 : ℝ) < |LN| / S by positivity))
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev2
  have a1 := hM (max M N) (le_max_left _ _)
  have a2 := hlow (max M N) (le_max_right _ _)
  simp only [Function.comp_apply] at a1
  rw [lt_div_iff₀ hS] at a1
  linarith
