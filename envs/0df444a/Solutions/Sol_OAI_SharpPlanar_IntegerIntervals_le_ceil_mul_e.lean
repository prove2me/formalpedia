-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.le_ceil_mul_e
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T14:54:42.076434+00:00
-- url     : https://prove2.me/submissions/1c6abe0c-bc77-4a8d-ae20-badc4f7bc363

import Mathlib

theorem solution (x : ℤ) {n : ℤ} (hn : 0 < n) : x ≤ -((-x) / n) * n := by
  have h := Int.ediv_mul_le (-x) (ne_of_gt hn)
  nlinarith
