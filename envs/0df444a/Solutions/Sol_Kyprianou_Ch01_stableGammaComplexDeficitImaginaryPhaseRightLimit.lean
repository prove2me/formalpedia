-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaComplexDeficitImaginaryPhaseRightLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:23:19.959236+00:00
-- url     : https://prove2.me/submissions/b13a7272-6427-4728-8606-f3aaa9ffb3fa

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Principal complex logarithm phase remains continuous at nonzero imaginary w. -/
theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re = 0) (hwim : w.im ≠ 0) :
    Tendsto
      (fun epsilon : ℝ =>
        Complex.exp ((alpha : ℂ) *
          Complex.log (-(w - (epsilon : ℂ)))))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (Complex.exp ((alpha : ℂ) * Complex.log (-w)))) := by
  have hslit : -w ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simpa using (neg_ne_zero.mpr hwim)
  have harg : ContinuousAt
      (fun epsilon : ℝ => -(w - (epsilon : ℂ)))
      (0 : ℝ) := by fun_prop
  have hslit0 : -(w - (((0 : ℝ) : ℂ))) ∈ Complex.slitPlane := by
    simpa using hslit
  have hlog : ContinuousAt
      (fun epsilon : ℝ =>
        Complex.log (-(w - (epsilon : ℂ)))) (0 : ℝ) := by
    have ht : Tendsto
        (fun epsilon : ℝ => -(w - (epsilon : ℂ)))
        (nhds (0 : ℝ)) (nhds (-w)) := by
      simpa using harg.tendsto
    simpa [ContinuousAt] using ht.clog hslit
  have hphase : ContinuousAt
      (fun epsilon : ℝ =>
        Complex.exp ((alpha : ℂ) *
          Complex.log (-(w - (epsilon : ℂ)))))
      (0 : ℝ) := by fun_prop
  convert hphase.tendsto.mono_left nhdsWithin_le_nhds using 1 <;> simp
