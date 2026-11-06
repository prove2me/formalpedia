-- Prove2me | solution 1 for OAI.SevenEighths.Continuation.polynomialGaussian_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:10:29.005982+00:00
-- url     : https://prove2.me/submissions/6ed03c1b-f0fd-4ab2-b136-9d69190faced

import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationContour
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationPolynomialContour
set_option autoImplicit false
open OAI
noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
open OAI.SevenEighths OAI.SevenEighths.Continuation

theorem solution (n : ℕ) (y : ℝ) : 0 ≤ polynomialGaussian n y := by
  exact mul_nonneg (add_nonneg zero_le_one (pow_nonneg (abs_nonneg y) n))
    (Real.exp_nonneg (-(y ^ 2)))
