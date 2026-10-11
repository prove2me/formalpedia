-- Prove2me | solution 1 for MazurTransfer.order13_cubic_diamond_transform_identities
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T20:27:12.571702+00:00
-- url     : https://prove2.me/submissions/ce89e68c-16da-41f9-9d6e-35cf7caa8605

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: literal algebraic transforms of the short cubic function.
Named downstream consumer: its actual cusp principal divisor.
-/
import Mathlib

theorem solution
    (F : Type) [Field F] (x y : F) (hx : x ≠ 0) (hd : x + 1 ≠ 0) :
    (y / (x + 1) ^ 3 - ((-1 / (x + 1)) ^ 3 + (-1 / (x + 1)) ^ 2 + 2 * (-1 / (x + 1)) + 1) =
      (y - x ^ 3 - x ^ 2 + 1) / (x + 1) ^ 3) ∧
    (y / x ^ 3 - ((-(x + 1) / x) ^ 3 + (-(x + 1) / x) ^ 2 + 2 * (-(x + 1) / x) + 1) =
      (y + x ^ 3 + 3 * x ^ 2 + 2 * x + 1) / x ^ 3) := by
  constructor
  · field_simp [hd]
    <;> ring
  · field_simp [hx]
    <;> ring
#print axioms solution
