-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaComplexDeficitValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:59:33.162547+00:00
-- url     : https://prove2.me/submissions/d5cff55c-4d94-4785-9384-0f10303680cf

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValueRealAxis
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValueNonReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Filter
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re ≤ 0) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (w * (r : ℂ)) - 1) *
        (((r ^ (-alpha - 1) : ℝ)) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) * Complex.log (-w)) := by
  by_cases him : w.im = 0
  · have hneg : w.re < 0 := by
      rcases lt_or_eq_of_le hwre with hlt | heq
      · exact hlt
      · exfalso
        apply hw
        apply Complex.ext <;> simp [heq, him]
    let u : ℝ := -w.re
    have hu : 0 < u := neg_pos.mpr hneg
    have hwu : w = -(u : ℂ) := by
      apply Complex.ext <;> simp [u, him]
    rw [hwu]
    simpa only [neg_neg] using
      Kyprianou.Ch01.stableGammaComplexDeficitValueRealAxis
        alpha u h0 h1 hu
  · exact Kyprianou.Ch01.stableGammaComplexDeficitValueNonReal
      alpha h0 h1 w hw hwre him
