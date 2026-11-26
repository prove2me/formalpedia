-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_spatial_initial_grid_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:48:11.793695+00:00
-- url     : https://prove2.me/submissions/53e87d3a-47a5-44c6-a8bd-2e90f77dbd7c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_ito43_spatial_slice_derivative
open Set
open scoped NNReal
set_option autoImplicit false

/-- Replacing ambient spatial derivatives by slice derivatives changes only the first cell. -/
theorem solution (X : NNReal → ℝ) (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Ici (0 : ℝ) ×ˢ (univ : Set ℝ)))
    (T t : NNReal) (n : ℕ) (hn : 0 < n) :
    let u : ℕ → NNReal := fun k => T * (k : NNReal) / (n : NNReal)
    let v : ℕ → NNReal := fun k => min t (u k)
    (∑ k ∈ Finset.range n,
      ((f ((v k : ℝ), X (v (k+1))) - f ((v k : ℝ), X (v k))) -
        deriv (fun y : ℝ => f ((u k : ℝ), y)) (X (u k)) * (X (v (k+1)) - X (v k)))) -
    (∑ k ∈ Finset.range n,
      ((f ((v k : ℝ), X (v (k+1))) - f ((v k : ℝ), X (v k))) -
        fderiv ℝ f ((u k : ℝ),X (u k)) (0,1) * (X (v (k+1)) - X (v k)))) =
      (fderiv ℝ f (0,X 0) (0,1) - deriv (fun y : ℝ => f (0,y)) (X 0)) *
        (X (min t (T / (n : NNReal))) - X 0) := by
  intro u v
  by_cases hT : T = 0
  · simp [u,v,hT]
  have hTp : 0 < T := pos_iff_ne_zero.mpr hT
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single 0]
  · simp [u,v]
    ring
  · intro k hk hk0
    have hk' : 0 < k := Nat.pos_of_ne_zero hk0
    have hu : 0 < (u k : ℝ) := by
      dsimp [u]
      positivity
    rw [Kyprianou.Ch04.ito43_spatial_slice_derivative f hf _ _ hu]
    ring
  · intro h
    exact (h (Finset.mem_range.mpr hn)).elim
