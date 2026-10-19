-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.conditional_concavity_nonnegative_sum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:23:15.905138+00:00
-- url     : https://prove2.me/submissions/85307d1d-7c25-42eb-aba1-32c8eece44ca

import Mathlib
set_option autoImplicit false

theorem solution {u v : ℝ → ℝ} {s : Set ℝ}
    (hu : ConcaveOn ℝ s u) (hv : ConcaveOn ℝ s v)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ConcaveOn ℝ s (fun x => a * u x + b * v x) := by
  refine ⟨hu.1, fun x hx y hy p q hp hq hpq => ?_⟩
  have h1 := hu.2 hx hy hp hq hpq
  have h2 := hv.2 hx hy hp hq hpq
  simp only [smul_eq_mul] at h1 h2 ⊢
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
