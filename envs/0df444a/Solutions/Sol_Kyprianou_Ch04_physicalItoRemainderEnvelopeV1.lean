-- Prove2me | solution 1 for Kyprianou.Ch04.physicalItoRemainderEnvelopeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:21:56.348848+00:00
-- url     : https://prove2.me/submissions/08389ca8-28a4-4527-9a61-7c5f37215a4b

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_spatialQuadraticJumpRemainderV1
open Filter Set Topology
set_option autoImplicit false

/-- Bounded smooth coefficients give a quadratic small-mark and linear large-mark envelope. -/
theorem solution (f fSpace fSpace2 : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hSpace : ∀ s x, fSpace s x = deriv (fun u : ℝ => f s u) x)
    (hSpace2 : ∀ s x, fSpace2 s x = deriv (fun u : ℝ => fSpace s u) x)
    (hSmooth : ∀ s, ContDiff ℝ 2 (fun x => f s x))
    (hBound : ∀ s x, 0 ≤ s → |f s x| ≤ K ∧ |fSpace s x| ≤ K ∧ |fSpace2 s x| ≤ K) :
    ∀ s x z, 0 ≤ s →
      |f s (x+z) - f s x - z*fSpace s x| ≤
        K * min 1 (z^2) + (if 1 ≤ |z| then K*(2+|z|) else 0) := by
  intro s x z hs
  by_cases hz : 1 ≤ |z|
  · have hf := (hBound s (x+z) hs).1
    have hx := (hBound s x hs).1
    have hg := (hBound s x hs).2.1
    have h := (abs_sub (f s (x+z) - f s x) (z*fSpace s x)).trans
      (add_le_add_left (abs_sub (f s (x+z)) (f s x)) _)
    rw [abs_mul] at h
    have hh := h.trans (add_le_add (add_le_add hf hx) (mul_le_mul_of_nonneg_left hg (abs_nonneg z)))
    have hmin : 0 ≤ K * min 1 (z^2) := mul_nonneg hK (le_min zero_le_one (sq_nonneg z))
    rw [if_pos hz]
    nlinarith
  · have hder : deriv (fun u : ℝ => f s u) = fSpace s := funext fun u => (hSpace s u).symm
    have hb : ∀ u, |deriv (deriv (fun x => f s x)) u| ≤ K := by
      intro u
      rw [hder,← hSpace2 s u]
      exact (hBound s u hs).2.2
    have h := Kyprianou.Ch04.spatialQuadraticJumpRemainderV1 (fun x => f s x) K x z
      (hSmooth s) hK hb
    rw [if_neg hz,add_zero,min_eq_right (by
      have hlt := lt_of_not_ge hz
      rw [← sq_abs z]
      nlinarith [abs_nonneg z])]
    rwa [← hSpace s x] at h
