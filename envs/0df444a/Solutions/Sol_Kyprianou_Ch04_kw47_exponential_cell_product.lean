-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_exponential_cell_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T10:08:56.77764+00:00
-- url     : https://prove2.me/submissions/73ad22f0-df50-4279-aaec-33c76e6d236a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.SetSemiring
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (alpha psi xa xb ua ub a b : Real) :
    Real.exp (alpha * xb - psi * b) *
        (Real.exp (-alpha * ub + psi * b) - Real.exp (-alpha * ua + psi * a)) =
      Real.exp (-alpha * (ub - xb)) *
        (1 - Real.exp (alpha * (ub - ua) - psi * (b - a))) := by 
  simp only [mul_sub, mul_one, ← Real.exp_add]
  congr 1 <;> congr 1 <;> ring
