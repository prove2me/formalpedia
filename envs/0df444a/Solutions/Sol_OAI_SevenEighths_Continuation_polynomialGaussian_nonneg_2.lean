-- Prove2me | solution 2 for OAI.SevenEighths.Continuation.polynomialGaussian_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:14:01.556905+00:00
-- url     : https://prove2.me/submissions/590afbce-7186-45c9-930b-92994e88a044

import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationContour
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationPolynomialContour

set_option autoImplicit false
open OAI
noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
open OAI.SevenEighths OAI.SevenEighths.Continuation
namespace OAI.SevenEighths.Continuation
theorem _root_.solution (n : ℕ) (y : ℝ) : 0 ≤ polynomialGaussian n y := by
  unfold polynomialGaussian
  positivity
end OAI.SevenEighths.Continuation
