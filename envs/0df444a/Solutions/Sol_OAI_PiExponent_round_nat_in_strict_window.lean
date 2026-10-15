-- Prove2me | solution 1 for OAI.PiExponent.round_nat_in_strict_window
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-15T05:10:26.187914+00:00
-- url     : https://prove2.me/submissions/6d75bf1a-cb61-4d0f-b257-2d6b5de7ad6c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring

theorem solution
    (x q : Real) (hx : 0 < x) (hq : 0 < q)
    (hbound : (x + 1) ^ 2 * q < 1) :
    Exists fun K : Nat => And (0 < K)
      (And ((K : Real) ^ 2 * q < 1) (x < (K : Real))) := by
  let K : Nat := Nat.floor x + 1
  have hxK : x < (K : Real) := by
    dsimp [K]
    rw [Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one x
  have hKpos : 0 < K := by
    simp [K]
  have hKle : (K : Real) <= x + 1 := by
    dsimp [K]
    rw [Nat.cast_add, Nat.cast_one]
    exact add_le_add_left (Nat.floor_le hx.le) 1
  have hKnonneg : 0 <= (K : Real) := Nat.cast_nonneg K
  have hBnonneg : 0 <= x + 1 := by linarith
  have hsq : (K : Real) ^ 2 <= (x + 1) ^ 2 := by
    have hd : 0 <= (x + 1) - (K : Real) := sub_nonneg.mpr hKle
    have hs : 0 <= (x + 1) + (K : Real) := add_nonneg hBnonneg hKnonneg
    nlinarith [mul_nonneg hd hs]
  refine Exists.intro K (And.intro hKpos (And.intro ?_ hxK))
  calc
    (K : Real) ^ 2 * q <= (x + 1) ^ 2 * q :=
      mul_le_mul_of_nonneg_right hsq hq.le
    _ < 1 := hbound