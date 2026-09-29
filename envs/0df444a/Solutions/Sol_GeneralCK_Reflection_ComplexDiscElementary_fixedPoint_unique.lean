-- Prove2me | solution 1 for GeneralCK.Reflection.ComplexDiscElementary.fixedPoint_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T21:03:23.007126+00:00
-- url     : https://prove2.me/submissions/a59bc81f-cad0-4096-af85-691a4565a8f2

import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Exact elementary constants for the small-bias complex contraction

This file isolates the algebraic and metric-space part of the proposed
complex-disc construction.  The analytic estimates on the complex entropy
remain premises here: once they give the bounds `1103 / 1000` and `7 / 5`,
the results below prove that multiplication by a parameter of norm at most
`7 / 10` maps the closed `4 / 5` disc to itself and has Lipschitz constant
`49 / 50`.

No complex logarithm, fixed-point existence, or holomorphic dependence is
asserted by this module.
-/

namespace GeneralCK.Reflection.ComplexDiscElementary

open Set























end GeneralCK.Reflection.ComplexDiscElementary

open Set
theorem solution
    {f : ℂ → ℂ} {c d : ℂ}
    (hf : LipschitzOnWith (49 / 50 : NNReal) f
      (Metric.closedBall 0 (4 / 5 : ℝ)))
    (hc : c ∈ Metric.closedBall (0 : ℂ) (4 / 5 : ℝ))
    (hd : d ∈ Metric.closedBall (0 : ℂ) (4 / 5 : ℝ))
    (hfc : f c = c) (hfd : f d = d) : c = d := by
  by_contra hcd
  have hpos : 0 < dist c d := dist_pos.mpr hcd
  have hcontract := hf.dist_le_mul c hc d hd
  rw [hfc, hfd] at hcontract
  norm_num at hcontract
  nlinarith
