-- Prove2me | solution 1 for Kyprianou.Ch04.positiveRootQuotientSecantLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T14:43:29.222015+00:00
-- url     : https://prove2.me/submissions/1de3dd1f-cb14-4eae-a2a8-9f380ce5a21f

import Mathlib
open Filter Set
open scoped Topology
set_option autoImplicit false
theorem solution
    (f : ℝ → ℝ)
    (hf : MonotoneOn (fun x : ℝ => f x / x) (Ioi 0))
    (q r : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (hr : ∀ n, 0 < r n) (hroot : ∀ n, f (r n) = q n)
    (hlim : Tendsto q atTop (𝓝 0)) :
    Tendsto (fun n => q n / r n) atTop
      (𝓝 (max 0 (sInf ((fun x : ℝ => f x / x) '' Ioi 0)))) := by
  let S : Set ℝ := (fun x : ℝ => f x / x) '' Ioi 0
  let m := max 0 (sInf S)
  change Tendsto (fun n => q n / r n) atTop (𝓝 m)
  have hm : 0 ≤ m := le_max_left _ _
  have hlo (n : ℕ) : m ≤ q n / r n := by
    apply max_le (div_nonneg (hq n).le (hr n).le)
    by_cases hb : BddBelow S
    · rw [← hroot n]
      exact csInf_le hb ⟨r n, hr n, rfl⟩
    · rw [Real.sInf_of_not_bddBelow hb]
      exact div_nonneg (hq n).le (hr n).le
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hx : ∃ x : ℝ, 0 < x ∧ f x / x < m + ε := by
    by_contra! h
    have hh : m + ε ≤ sInf S := by
      apply le_csInf
      · exact ⟨f 1 / 1, 1, by norm_num, rfl⟩
      · rintro y ⟨x, hx, rfl⟩
        exact h x hx
    linarith [le_max_right 0 (sInf S)]
  obtain ⟨x, hx, hfx⟩ := hx
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ε * x) (mul_pos hε hx)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hlo n))]
  have hq' := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_pos (hq n)] at hq'
  by_cases h : r n ≤ x
  · have hle := hf (hr n) hx h
    change f (r n) / r n <= f x / x at hle
    rw [hroot n] at hle
    linarith
  · have hlt : q n / r n < ε := by
      apply (div_lt_iff₀ (hr n)).2
      exact hq'.trans_le (mul_le_mul_of_nonneg_left (le_of_not_ge h) hε.le)
    linarith
