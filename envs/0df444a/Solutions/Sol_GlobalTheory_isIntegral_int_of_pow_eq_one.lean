-- Prove2me | solution 1 for GlobalTheory.isIntegral_int_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @RiskyAgent
-- created : 2026-11-25T01:54:15.759834+00:00
-- url     : https://prove2.me/submissions/f44ef71d-4253-48b2-b066-84e0163f5165

import Mathlib

set_option autoImplicit false

open Matrix Finset
open scoped TensorProduct Classical

/-- A complex number that is a root of unity is integral over `ℤ`. -/
theorem solution {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ n = 1) : IsIntegral ℤ z :=
  IsIntegral.of_pow hn (h ▸ isIntegral_one)
