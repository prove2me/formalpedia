-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanAffineUpperContinuationFromBarrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:50:59.420914+00:00
-- url     : https://prove2.me/submissions/b8a578c0-169b-49eb-9cf9-b7f7c974deed

import Mathlib.Analysis.Complex.Exponential
open Real
set_option autoImplicit false

/-- A positive intercept carries an exponential majorant past the barrier. -/
theorem solution
    (K phi b u A B : ℝ) (hphi : 0 < phi) (hA : 0 ≤ A)
    (hAtBarrier :
      K - Real.exp b ≤ A + B * Real.exp (-phi * (b - u))) :
    ∀ z : ℝ, b ≤ z →
      (K - Real.exp b) * Real.exp (-phi * (z - b)) ≤
        A + B * Real.exp (-phi * (z - u)) := by
  intro z hzb
  let d : ℝ := Real.exp (-phi * (z - b))
  have hdpos : 0 ≤ d := Real.exp_nonneg _
  have harg : -phi * (z - b) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hphi.le)
      (sub_nonneg.mpr hzb)
  have hdle : d ≤ 1 := by
    simpa [d] using (Real.exp_le_exp.mpr harg :
      Real.exp (-phi * (z - b)) ≤ Real.exp 0)
  have hExpSplit :
      Real.exp (-phi * (z - u)) = Real.exp (-phi * (b - u)) * d := by
    dsimp [d]
    rw [← Real.exp_add]
    congr 1
    ring
  have hMult := mul_le_mul_of_nonneg_right hAtBarrier hdpos
  have hAmono : A * d ≤ A := by
    have hh := mul_le_mul_of_nonneg_left hdle hA
    simpa only [mul_one] using hh
  change (K - Real.exp b) * d ≤ A + B * Real.exp (-phi * (z - u))
  rw [hExpSplit]
  nlinarith [hMult, hAmono]
