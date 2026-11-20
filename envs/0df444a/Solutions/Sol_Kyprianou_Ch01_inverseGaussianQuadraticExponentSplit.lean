-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianQuadraticExponentSplit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:04:05.960697+00:00
-- url     : https://prove2.me/submissions/808ee5aa-c5d4-4757-87e5-dd807ad45d1f

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Real
set_option autoImplicit false

theorem solution
    (s b q x : ℝ) (hx : 0 < x) :
    -((s - b * x) ^ 2 / (2 * x)) - q * x =
      s * b - s ^ 2 / (2 * x) - (b ^ 2 / 2 + q) * x := by
  field_simp [ne_of_gt hx]
  ring
