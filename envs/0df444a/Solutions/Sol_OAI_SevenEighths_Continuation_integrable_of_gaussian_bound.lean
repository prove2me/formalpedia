-- Prove2me | solution 1 for OAI.SevenEighths.Continuation.integrable_of_gaussian_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:52:10.920962+00:00
-- url     : https://prove2.me/submissions/ada03181-985d-47cd-b303-0b5bff287419

import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationInversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Definitions.Def_OAI_NumberTheory_DirichletL_ContinuationContour

set_option autoImplicit false
open OAI
noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology
open OAI.SevenEighths OAI.SevenEighths.Continuation
namespace OAI.SevenEighths.Continuation
theorem _root_.solution (f : ℝ → ℂ) (C : ℝ)
    (hmeas : AEStronglyMeasurable f) (hbound : ∀ y, ‖f y‖ ≤ C * Real.exp (-(y ^ 2))) :
    Integrable f := by
  have hg : Integrable (fun y : ℝ => C * Real.exp (-(y ^ 2))) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul C
  exact hg.mono' hmeas (ae_of_all _ hbound)
end OAI.SevenEighths.Continuation
