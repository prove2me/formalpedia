-- Prove2me | solution 1 for Kyprianou.Ch07.kestenGeometricRecursion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:17:05.892499+00:00
-- url     : https://prove2.me/submissions/045e753a-733b-456e-bd89-a097589c4f5e

import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Filter

/-- A nonnegative affine error term in Kesten's convolution-tail recurrence
is absorbed into a geometric majorant. -/
theorem solution
    (epsilon A B : Real)
    (hEpsilon : 0 < epsilon)
    (xi : Nat → Real)
    (hBase : xi 0 ≤ B)
    (hStep : ∀ n : Nat,
      xi (n + 1) ≤ A + (1 + epsilon) * xi n) :
    ∀ n : Nat,
      xi n + A / epsilon ≤
        (B + A / epsilon) * (1 + epsilon) ^ n := by
  have heps : epsilon ≠ 0 := ne_of_gt hEpsilon
  have hq : 0 ≤ (1 : Real) + epsilon := by linarith
  intro n
  induction n with
  | zero =>
      simp only [pow_zero, mul_one]
      linarith only [hBase]
  | succ n ih =>
      have hid :
          A + (1 + epsilon) * xi n + A / epsilon =
            (1 + epsilon) * (xi n + A / epsilon) := by
        field_simp
        ring
      calc
        xi (n + 1) + A / epsilon ≤
            A + (1 + epsilon) * xi n + A / epsilon :=
          by linarith only [hStep n]
        _ = (1 + epsilon) * (xi n + A / epsilon) := hid
        _ ≤ (1 + epsilon) * ((B + A / epsilon) *
              (1 + epsilon) ^ n) :=
          mul_le_mul_of_nonneg_left ih hq
        _ = (B + A / epsilon) * (1 + epsilon) ^ (n + 1) := by
          rw [pow_succ]
          ring
