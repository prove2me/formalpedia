-- Prove2me | solution 1 for MetodosNumericos.picard_error_bound
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-24T07:17:21.223284+00:00
-- url     : https://prove2.me/submissions/dac4af2f-045d-43cb-b49f-10e9c85b54b0

import Mathlib
import Definitions.Def_MetodosNumericos_edoDefs

open MetodosNumericos

theorem solution : ¬ (∀ (f : ℝ → ℝ → ℝ) (phi : ℝ → ℝ) (x0 y0 a b M N h : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hM : 0 < M) (hN : 0 ≤ N) (hh : h = min a (b / M))
    (hbound : ∀ x ∈ Set.Icc (x0 - a) (x0 + a), ∀ y ∈ Set.Icc (y0 - b) (y0 + b), |f x y| ≤ M)
    (hlip : ∀ x ∈ Set.Icc (x0 - a) (x0 + a), ∀ u ∈ Set.Icc (y0 - b) (y0 + b),
      ∀ v ∈ Set.Icc (y0 - b) (y0 + b), |f x u - f x v| ≤ N * |u - v|)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2)
      (Set.Icc (x0 - a) (x0 + a) ×ˢ Set.Icc (y0 - b) (y0 + b)))
    (hphi0 : phi x0 = y0)
    (hsol : ∀ x ∈ Set.Icc (x0 - h) (x0 + h), HasDerivAt phi (f x (phi x)) x)
    (hrange : ∀ x ∈ Set.Icc (x0 - h) (x0 + h), phi x ∈ Set.Icc (y0 - b) (y0 + b))
    (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : x ∈ Set.Icc (x0 - h) (x0 + h)),
    |phi x - picardSeq f x0 y0 k x| ≤ M * N ^ (k - 1) * h ^ k / (Nat.factorial k : ℝ)) := by
  intro H
  set f : ℝ → ℝ → ℝ := fun t y => max (-1) (min 1 (1 + 4 * (y - t))) with hf
  have hclamp : ∀ p q : ℝ, |max (-1) (min 1 p) - max (-1) (min 1 q)| ≤ |p - q| := by
    intro p q
    refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero]
    refine max_le (abs_nonneg _) ?_
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero]
    exact max_le (abs_nonneg _) le_rfl
  have hcontf : Continuous (fun p : ℝ × ℝ => f p.1 p.2) := by
    simp only [hf]; fun_prop
  have key := H f id 0 0 1 1 1 4 1 one_pos one_pos one_pos (by norm_num) (by norm_num)
    (by
      intro x _ y _
      simp only [hf]
      rw [abs_le]
      exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩)
    (by
      intro x _ u _ v _
      simp only [hf]
      refine (hclamp _ _).trans (le_of_eq ?_)
      rw [show 1 + 4 * (u - x) - (1 + 4 * (v - x)) = 4 * (u - v) by ring, abs_mul]
      norm_num)
    hcontf.continuousOn rfl
    (by
      intro x _
      have : f x (id x) = 1 := by simp [hf]
      rw [this]; exact hasDerivAt_id x)
    (by intro x hx; simpa using hx)
    1 le_rfl 1 (by norm_num)
  -- compute the first Picard iterate at `x = 1`
  have hint : ∫ t in (0 : ℝ)..1, f t (picardSeq f 0 0 0 t) = -1 / 2 := by
    have hc : Continuous (fun t : ℝ => f t (picardSeq f 0 0 0 t)) := by
      simp only [picardSeq, hf]; fun_prop
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have h1 : ∫ t in (0 : ℝ)..(1 / 2), f t (picardSeq f 0 0 0 t) =
        ∫ t in (0 : ℝ)..(1 / 2), (1 - 4 * t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by norm_num)] at ht
      simp only [picardSeq, hf]
      obtain ⟨h0, h1⟩ := ht
      rw [min_eq_right (by linarith), max_eq_right (by linarith)]
      ring
    have h2 : ∫ t in (1 / 2 : ℝ)..1, f t (picardSeq f 0 0 0 t) =
        ∫ t in (1 / 2 : ℝ)..1, (-1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by norm_num)] at ht
      simp only [picardSeq, hf]
      obtain ⟨h0, h1⟩ := ht
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    have e1 : ∫ t in (0 : ℝ)..(1 / 2), (1 - 4 * t) = 0 := by
      have hd : ∀ t ∈ Set.uIcc (0 : ℝ) (1 / 2),
          HasDerivAt (fun t : ℝ => t - 2 * t ^ 2) (1 - 4 * t) t := by
        intro t _
        have := (hasDerivAt_id' t).sub ((hasDerivAt_pow 2 t).const_mul 2)
        exact this.congr_deriv (by push_cast; ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (by apply Continuous.intervalIntegrable; fun_prop)]
      norm_num
    rw [h1, h2, e1, intervalIntegral.integral_const]
    norm_num
  have hp : picardSeq f 0 0 1 1 = -1 / 2 := by
    show 0 + ∫ t in (0 : ℝ)..1, f t (picardSeq f 0 0 0 t) = -1 / 2
    rw [hint]; ring
  rw [hp] at key
  norm_num at key
