-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_stopped_grid_cutoff_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:34:29.49522+00:00
-- url     : https://prove2.me/submissions/3e108d9f-c0c2-45ad-8d34-4a9c7e203510

import Mathlib
open Set
open scoped NNReal
set_option autoImplicit false

/-- On a stopped cell, derivatives at the unclipped time give the same Taylor excess
as derivatives at the clipped time: after the stopping horizon the increment is zero. -/
theorem solution (X : NNReal → ℝ) (f : ℝ × ℝ → ℝ)
    (u : ℕ → NNReal) (hu : Monotone u) (t : NNReal) (k : ℕ) :
    let v : ℕ → NNReal := fun j => min t (u j)
    let d := X (v (k+1))-X (v k)
    (f ((v k : ℝ),X (v (k+1)))-f ((v k : ℝ),X (v k)) -
      deriv (fun x : ℝ => f ((u k : ℝ),x)) (X (u k))*d -
      iteratedDeriv 2 (fun x : ℝ => f ((u k : ℝ),x)) (X (u k))*d^2/2) =
    (f ((v k : ℝ),X (v (k+1)))-f ((v k : ℝ),X (v k)) -
      deriv (fun x : ℝ => f ((v k : ℝ),x)) (X (v k))*d -
      iteratedDeriv 2 (fun x : ℝ => f ((v k : ℝ),x)) (X (v k))*d^2/2) := by
  intro v d
  by_cases h : u k ≤ t
  · have hv : v k = u k := min_eq_right h
    rw [hv]
  · have hv : v k = t := min_eq_left (le_of_not_ge h)
    have hv' : v (k+1) = t :=
      min_eq_left ((le_of_not_ge h).trans (hu (Nat.le_succ k)))
    have hd : d = 0 := by dsimp [d]; rw [hv,hv',sub_self]
    rw [hd]
    simp
