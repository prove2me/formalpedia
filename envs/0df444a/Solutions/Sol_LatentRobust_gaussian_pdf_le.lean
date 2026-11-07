-- Prove2me | solution 1 for LatentRobust.gaussian_pdf_le
-- status  : ACCEPTED   (prove)
-- author  : @刘柄含
-- created : 2026-11-06T06:33:21.740013+00:00
-- url     : https://prove2.me/submissions/27b740b9-89af-4237-a5a9-1645c961258a

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.Positivity

/-!
The Gaussian density bound used in Appendix A.3 of Javanmard and Mehrabi,
https://arxiv.org/pdf/2110.11950v2#page=22.

Target https://prove2.me/theorems/1fb4cb9e-7930-4123-a2b5-d30ac594b6b1
-/

set_option autoImplicit false

open ProbabilityTheory

theorem solution (ν : ℝ) (v : NNReal) (hv : 0 < v) (x : ℝ) :
    gaussianPDFReal ν v x ≤ 1 / Real.sqrt (2 * Real.pi * v) := by
  have hvReal : 0 < (v : ℝ) := by exact_mod_cast hv
  have hexp : Real.exp (-(x - ν) ^ 2 / (2 * v)) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  rw [gaussianPDFReal, one_div]
  exact mul_le_of_le_one_right (by positivity) hexp
