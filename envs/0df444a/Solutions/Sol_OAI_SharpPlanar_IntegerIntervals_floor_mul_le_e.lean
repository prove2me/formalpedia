-- Prove2me | solution 1 for OAI.SharpPlanar.IntegerIntervals.floor_mul_le_e
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T14:53:38.874237+00:00
-- url     : https://prove2.me/submissions/d29792d7-94f5-420b-a559-0e588679c548

import Mathlib

theorem solution (x : ℤ) {n : ℤ} (hn : 0 < n) : x / n * n ≤ x := by
  exact Int.ediv_mul_le x (ne_of_gt hn)
