-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45MaskedGridDifferenceV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:38:17.330481+00:00
-- url     : https://prove2.me/submissions/90017e15-8d31-4419-aad1-a579de68dae3

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Removing the unconstrained time-zero coefficient affects only the first cell. -/
theorem solution (Y H : NNReal → ℝ) (T t : NNReal) (n : ℕ)
    (K : ℝ) (hK : 0 ≤ K) (hb : |H 0| ≤ K) :
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    let G : ℝ := ∑ k ∈ Finset.range n, H (u k) * (Y (v (k+1)) - Y (v k))
    let A : ℝ := ∑ k ∈ Finset.range n, (if u k = 0 then 0 else H (u k)) *
      (Y (v (k+1)) - Y (v k))
    |G-A| ≤ K * |Y (min t (T / (n : NNReal))) - Y 0| := by
  intro u v G A
  by_cases hn : n = 0
  · subst n
    simp [G,A,u,v]
  by_cases hT : T = 0
  · subst T
    simp [G,A,u,v]
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  have hT' : 0 < T := pos_iff_ne_zero.mpr hT
  change |(∑ k ∈ Finset.range n, H (u k) * (Y (v (k+1)) - Y (v k))) -
      (∑ k ∈ Finset.range n, (if u k = 0 then 0 else H (u k)) *
        (Y (v (k+1)) - Y (v k)))| ≤ _
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single 0]
  · simp only [u,v,Nat.cast_zero,Nat.zero_add, mul_zero,zero_div,min_zero,
      Nat.cast_one,mul_one,if_true,zero_mul,sub_zero,abs_mul]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  · intro k hk hk0
    have hk' : 0 < k := Nat.pos_of_ne_zero hk0
    have hu : 0 < u k := by dsimp [u]; positivity
    simp [ne_of_gt hu]
  · intro h
    exact (h (Finset.mem_range.mpr hn')).elim
