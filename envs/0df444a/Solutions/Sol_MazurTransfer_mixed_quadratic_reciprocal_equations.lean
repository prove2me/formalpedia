-- Prove2me | solution 1 for MazurTransfer.mixed_quadratic_reciprocal_equations
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-15T00:36:21.815108+00:00
-- url     : https://prove2.me/submissions/7adf1a9e-ef0b-4a09-8776-79b05b808bef

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0. -/
import Mathlib

theorem solution (R : Type*) [CommRing R] (x z : R) (hxz : x * z = 1) :
    (∀ y : R, y ^ 2 + (x ^ 3 + x ^ 2 + 1) * y - x * (x + 1) = 0 →
      (y * z ^ 3) ^ 2 + (1 + z + z ^ 3) * (y * z ^ 3) - (z ^ 4 + z ^ 5) = 0) ∧
    (∀ w : R, w ^ 2 + (1 + z + z ^ 3) * w - (z ^ 4 + z ^ 5) = 0 →
      (w * x ^ 3) ^ 2 + (x ^ 3 + x ^ 2 + 1) * (w * x ^ 3) - x * (x + 1) = 0) := by
  constructor
  · intro y hy
    linear_combination z ^ 6 * hy +
      (-y * z ^ 3 * ((x * z) ^ 2 + x * z + 1) - y * z ^ 4 * (x * z + 1) +
        z ^ 4 * (x * z + 1) + z ^ 5) * hxz
  · intro w hw
    linear_combination x ^ 6 * hw +
      (-w * x ^ 5 - w * x ^ 3 * ((x * z) ^ 2 + x * z + 1) +
        x ^ 2 * ((x * z) ^ 3 + (x * z) ^ 2 + x * z + 1) +
        x * ((x * z) ^ 4 + (x * z) ^ 3 + (x * z) ^ 2 + x * z + 1)) * hxz

#print axioms solution
