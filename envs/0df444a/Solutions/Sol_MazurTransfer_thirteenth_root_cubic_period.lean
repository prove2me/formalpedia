-- Prove2me | solution 1 for MazurTransfer.thirteenth_root_cubic_period
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-14T22:39:07.434769+00:00
-- url     : https://prove2.me/submissions/a3e600bd-554c-42e8-91c0-69bdb4a7c4df

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a literal primitive-thirteenth-root period satisfies the
cubic for the actual curve reflection. Named downstream consumer:
Order13CyclotomicReflectionCoefficients.cubicPeriod_root.
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Ring

noncomputable section
theorem solution
    (K : Type*) [Field K] (z : K) (hz : IsPrimitiveRoot z 13) :
    let t := z + z ^ 5 + z ^ 8 + z ^ 12 - 1
    t ^ 3 + 4 * t ^ 2 + t - 1 = 0 := by
  let t := z + z ^ 5 + z ^ 8 + z ^ 12 - 1
  have hsum : 1 + z + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 + z ^ 6 + z ^ 7 + z ^ 8 + z ^ 9 + z ^ 10 + z ^ 11 + z ^ 12 = 0 := by
    have h := hz.geom_sum_eq_zero (by decide : 1 < 13)
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] using h
  have h : t ^ 3 + 4 * t ^ 2 + t - 1 =
    (z ^ 24 - z ^ 23 + 3 * z ^ 20 - 3 * z ^ 19 + 3 * z ^ 17 - 3 * z ^ 15 +
      9 * z ^ 13 - 7 * z ^ 12 - z ^ 11 + 2 * z ^ 10 + 6 * z ^ 9 - 7 * z ^ 8 +
      z ^ 7 + 6 * z ^ 6 - 4 * z ^ 5 - z ^ 4 + 5 * z ^ 2 - 5 * z + 1) * (1 + z + z ^ 2 + z ^ 3 + z ^ 4 + z ^ 5 + z ^ 6 + z ^ 7 + z ^ 8 + z ^ 9 + z ^ 10 + z ^ 11 + z ^ 12) := by
    dsimp [t]
    ring
  rw [hsum, mul_zero] at h
  exact h

#print axioms solution
