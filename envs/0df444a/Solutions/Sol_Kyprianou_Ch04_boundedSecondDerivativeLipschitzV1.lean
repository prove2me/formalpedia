-- Prove2me | solution 1 for Kyprianou.Ch04.boundedSecondDerivativeLipschitzV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:42:55.264165+00:00
-- url     : https://prove2.me/submissions/919961ef-0f59-4fe6-a9c5-08aa915a8fb9

import Mathlib
open Set
set_option autoImplicit false

/-- Bounded second derivative gives a Lipschitz first derivative. -/
theorem solution (f : ℝ → ℝ) (K x u : ℝ)
    (h : ContDiff ℝ 2 f) (hbound : ∀ v, |deriv (deriv f) v| ≤ K) :
    |deriv f u - deriv f x| ≤ K * |u - x| := by
  have hg := h.differentiable_deriv_two
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun v _ => hg v)
      (fun v _ => by simpa only [Real.norm_eq_abs] using hbound v)
      (Set.mem_univ x) (Set.mem_univ u)
