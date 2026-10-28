-- Prove2me | solution 1 for MazurProof.N13SpecialInfinityGraphDivisor.curveEquationAtRoot
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:21:48.023506+00:00
-- url     : https://prove2.me/submissions/e46e9cbd-968e-4b11-be75-cc99f8262e20

import Mathlib
import Definitions.Def_MazurN13_L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13SpecialInfinityGraphDivisor
open Polynomial
open scoped Sym2
attribute [local instance] MazurProof.N13SpecialInfinityGraphDivisor.instFactPrimeOfNatNat_fLT
theorem solution (D : SemiMumford) {a : K} (ha : D.u.IsRoot a) : N13GoodModelTwo.InfinityChartEquation a (D.v.eval a) := by
  have h := congrArg (Polynomial.eval a) D.curve_eq
  have hu : D.u.eval a = 0 := ha
  simp only [N13SpecialInfinityChart.hPoly, N13SpecialInfinityChart.rhsPoly, eval_add, eval_sub,
    eval_mul, eval_pow, eval_one, eval_X, hu, zero_mul] at h
  unfold N13GoodModelTwo.InfinityChartEquation
  linear_combination h
