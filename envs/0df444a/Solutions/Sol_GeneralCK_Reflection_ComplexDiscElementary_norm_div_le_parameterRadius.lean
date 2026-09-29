-- Prove2me | solution 1 for GeneralCK.Reflection.ComplexDiscElementary.norm_div_le_parameterRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T21:03:58.164294+00:00
-- url     : https://prove2.me/submissions/b6982410-d57a-413f-aed3-e30bc002e65e

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
    {a e : ℂ} (ha : ‖a‖ ≤ (21 / 50 : ℝ))
    (he : (3 / 5 : ℝ) ≤ ‖e‖) :
    ‖a / e‖ ≤ (7 / 10 : ℝ) := by
  rw [Complex.norm_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num) he)]
  nlinarith
