-- Prove2me | solution 1 for OAI.SevenEighths.Continuation.polynomialGaussian_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:52:20.991903+00:00
-- url     : https://prove2.me/submissions/ac804939-a656-49d6-b797-7c4e6cfe2d9f

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
theorem _root_.solution (n : ℕ) (y : ℝ) :
    polynomialGaussian n (-y) = polynomialGaussian n y := by
  simp [polynomialGaussian]
end OAI.SevenEighths.Continuation
