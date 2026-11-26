-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_spatial_small_cutoff_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:05:25.457183+00:00
-- url     : https://prove2.me/submissions/de0bfe24-8d4a-4dbf-97ef-816b21845361

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_compact_taylor
open Set
set_option autoImplicit false

/-- On a compact rectangle the sum of small-cutoff Taylor excesses is controlled
by any prescribed positive multiple of the total squared increments. -/
theorem solution (f : ℝ × ℝ → ℝ) (T M : ℝ)
    (hf : ∀ s ∈ Icc 0 T, ContDiff ℝ 2 (fun x : ℝ => f (s,x)))
    (hg : ContinuousOn (fun z : ℝ × ℝ => iteratedDeriv 2 (fun x : ℝ => f (z.1,x)) z.2)
      (Icc 0 T ×ˢ Icc (-M) M)) :
    ∀ e : ℝ, 0 < e → ∃ m : ℕ, ∀ (n : ℕ) (s x y : ℕ → ℝ),
      (∀ k < n, s k ∈ Icc 0 T ∧ x k ∈ Icc (-M) M ∧ y k ∈ Icc (-M) M) →
      let chi : ℝ → ℝ := fun z => min 1 (max 0 (|z| * ((m : ℝ)+1) - 1))
      |∑ k ∈ Finset.range n,
        (f (s k,y k) - f (s k,x k) - deriv (fun z : ℝ => f (s k,z)) (x k) * (y k-x k) -
          iteratedDeriv 2 (fun z : ℝ => f (s k,z)) (x k) * (y k-x k)^2 / 2) *
          (1-chi (y k-x k))| ≤ e * ∑ k ∈ Finset.range n, (y k-x k)^2 := by
  intro e he
  obtain ⟨δ,hδ,hb⟩ := Kyprianou.Ch04.ito43_spatial_compact_taylor f T M hf hg e he
  obtain ⟨m,hm⟩ := exists_nat_gt (2/δ)
  have hm' : 2 < (m : ℝ)*δ := (div_lt_iff₀ hδ).mp hm
  refine ⟨m,?_⟩
  intro n s x y h chi
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro k hk
  obtain ⟨hs,hx,hy⟩ := h k (Finset.mem_range.mp hk)
  by_cases hsmall : |y k-x k| ≤ δ
  · rw [abs_mul]
    have hχ0 : 0 ≤ chi (y k-x k) := le_min (by norm_num) (le_max_left _ _)
    have hχ1 : chi (y k-x k) ≤ 1 := min_le_left _ _
    rw [abs_of_nonneg (sub_nonneg.mpr hχ1)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (by linarith)).trans (hb _ hs _ hx _ hy hsmall)
  · have hlarge : 1 ≤ |y k-x k| * ((m : ℝ)+1) - 1 := by
      have hD := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hsmall))
        (show 0 ≤ (m : ℝ)+1 by positivity)
      nlinarith
    have hχ : chi (y k-x k) = 1 :=
      min_eq_left (hlarge.trans (le_max_right _ _))
    rw [hχ,sub_self,mul_zero,abs_zero]
    positivity
