-- Prove2me | solution 1 for OAI.SevenEighths.Continuation.norm_gaussianContourIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:13:58.862252+00:00
-- url     : https://prove2.me/submissions/34340227-10d4-41ac-a91b-cb317f503229

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
theorem _root_.solution (G : ℂ → ℂ) (c x y : ℝ) {Z : ℝ}
    (hZ : 0 < Z) :
    ‖gaussianContourIntegrand G c Z ((x : ℂ) + y * I)‖ =
      Z ^ (x + c) * Real.exp ((x - 5 / 6) ^ 2) *
        ‖G ((x : ℂ) + y * I)‖ * Real.exp (-(y ^ 2)) := by
  unfold gaussianContourIntegrand
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hZ, Complex.norm_exp]
  have hre : ((((x : ℂ) + y * I) - 5 / 6) ^ 2).re = (x - 5 / 6) ^ 2 - y ^ 2 := by
    simp [pow_two]
  rw [hre, Real.exp_sub]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, mul_zero, zero_mul, sub_self,
    add_zero, Real.exp_neg]
  ring
end OAI.SevenEighths.Continuation
