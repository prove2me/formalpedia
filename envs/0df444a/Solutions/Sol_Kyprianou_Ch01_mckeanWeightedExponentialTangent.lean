-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanWeightedExponentialTangent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:38:45.236798+00:00
-- url     : https://prove2.me/submissions/13a91afb-eda4-4715-868a-7248a200730d

import Mathlib.Analysis.Complex.Exponential
open Real
set_option autoImplicit false

/-- The weighted sum of exponentials is bounded below by its common tangent. -/
theorem solution (phi v : ℝ) (hphi : 0 < phi) :
    1 + phi ≤ phi * Real.exp v + Real.exp (-phi * v) := by
  have h1 : phi * (v + 1) ≤ phi * Real.exp v :=
    mul_le_mul_of_nonneg_left (Real.add_one_le_exp v) hphi.le
  have h2 : -phi * v + 1 ≤ Real.exp (-phi * v) :=
    Real.add_one_le_exp (-phi * v)
  nlinarith [h1, h2]
