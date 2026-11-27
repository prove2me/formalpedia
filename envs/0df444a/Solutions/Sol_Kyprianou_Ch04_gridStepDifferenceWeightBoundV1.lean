-- Prove2me | solution 1 for Kyprianou.Ch04.gridStepDifferenceWeightBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:46:12.65861+00:00
-- url     : https://prove2.me/submissions/0f7fcc5d-3410-4712-811c-9e81a49ebd0a

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_gridStepUniformWeightBoundV1
open MeasureTheory Set
open scoped NNReal
set_option autoImplicit false

/-- The step interpolation operator preserves the sup-norm distance. -/
theorem solution (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ)
    (H L : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ k ∈ Finset.range n, |H k-L k| ≤ C) :
    ∀ s, |(∑ k ∈ Finset.range n, (Ioc (u k) (u (k+1))).indicator
      (fun _ => H k) s) - (∑ k ∈ Finset.range n, (Ioc (u k) (u (k+1))).indicator
      (fun _ => L k) s)| ≤ C := by
  intro s
  rw [← Finset.sum_sub_distrib]
  have he (k : ℕ) :
      (Ioc (u k) (u (k+1))).indicator (fun _ => H k) s -
      (Ioc (u k) (u (k+1))).indicator (fun _ => L k) s =
      (Ioc (u k) (u (k+1))).indicator (fun _ => H k-L k) s := by
    by_cases hs : s ∈ Ioc (u k) (u (k+1)) <;> simp [Set.indicator_apply,hs]
  simp_rw [he]
  exact Kyprianou.Ch04.gridStepUniformWeightBoundV1 u hu n
    (fun k (_ : Unit) => H k-L k) C hC (fun k hk _ => h k hk) s ()
