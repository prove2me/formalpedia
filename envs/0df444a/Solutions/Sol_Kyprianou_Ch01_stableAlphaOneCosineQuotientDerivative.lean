-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCosineQuotientDerivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T09:07:46.263498+00:00
-- url     : https://prove2.me/submissions/6a0c696f-d170-47b9-a04b-9d75b802623a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Real
set_option autoImplicit false
/-! Differentiate the stable-index-one cosine quotient off the origin. -/
theorem solution
    (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun x : ℝ => (1 - Real.cos x) / x)
      (Real.sin r / r - (1 - Real.cos r) / r ^ 2) r := by
  have hn : DifferentiableAt ℝ (fun x : ℝ => 1 - Real.cos x) r :=
    ((Real.hasDerivAt_cos r).const_sub 1).differentiableAt
  have hd : DifferentiableAt ℝ (fun x : ℝ => x) r :=
    differentiableAt_id
  have hdiff : DifferentiableAt ℝ (fun x : ℝ => (1 - Real.cos x) / x) r :=
    hn.div hd hr
  have hderiv :
      deriv (fun x : ℝ => (1 - Real.cos x) / x) r =
        Real.sin r / r - (1 - Real.cos r) / r ^ 2 := by
    rw [deriv_fun_div hn hd hr]
    simp only [deriv_const_sub, Real.deriv_cos, deriv_id'', neg_neg, one_mul, id_eq]
    field_simp
  rw [← hderiv]
  exact hdiff.hasDerivAt
