-- Prove2me | solution 1 for Kyprianou.Ch04.spatialRemainderFromDerivativeBudgetV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:42:56.057901+00:00
-- url     : https://prove2.me/submissions/9535764b-4ab4-4f6f-aa2e-4f7b720a0b25

import Mathlib
open Set
set_option autoImplicit false

/-- Segment mean-value bound for the linear residual. -/
theorem solution (f : ℝ → ℝ) (K x z : ℝ)
    (hK : 0 ≤ K)
    (hLip : ∀ u, |deriv f u - deriv f x| ≤ K * |u - x|)
    (hD : ∀ u, HasDerivAt (fun v => f v - v * deriv f x)
      (deriv f u - deriv f x) u) :
    |f (x + z) - f x - z * deriv f x| ≤ K * z ^ 2 := by
  let g : ℝ → ℝ := fun u => f u - u * deriv f x
  have hx : x ∈ Icc (x - |z|) (x + |z|) := by
    constructor <;> linarith [abs_nonneg z]
  have hxz : x + z ∈ Icc (x - |z|) (x + |z|) := by
    constructor
    · linarith [neg_abs_le z]
    · linarith [le_abs_self z]
  have hG (u : ℝ) (hu : u ∈ Icc (x - |z|) (x + |z|)) :
      ‖deriv g u‖ ≤ K * |z| := by
    rw [(hD u).deriv, Real.norm_eq_abs]
    have hu' : |u - x| ≤ |z| := abs_le.mpr
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    exact (hLip u).trans (mul_le_mul_of_nonneg_left hu' hK)
  have hR := (convex_Icc (x - |z|) (x + |z|)).norm_image_sub_le_of_norm_deriv_le
    (fun u _ => (hD u).differentiableAt) hG hx hxz
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hR
  have heq : g (x + z) - g x = f (x + z) - f x - z * deriv f x := by
    dsimp [g]
    ring
  rw [heq, show x + z - x = z by ring, mul_assoc, ← pow_two, sq_abs] at hR
  exact hR
