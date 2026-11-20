-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaComplexDeficitValueImaginary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:54:30.702645+00:00
-- url     : https://prove2.me/submissions/d3b6cfd0-1b13-4b1d-aad4-c98f62b31a77

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValueStrictLeft
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitImaginaryIntegralRightLimit
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitImaginaryPhaseRightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re = 0) (hwim : w.im ≠ 0) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (w * (r : ℂ)) - 1) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) * Complex.log (-w)) := by
  let L : ℝ → ℂ := fun epsilon =>
    ∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp ((w - (epsilon : ℂ)) * (r : ℂ)) - 1) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume
  let R : ℝ → ℂ := fun epsilon =>
    ((Real.Gamma (-alpha) : ℝ) : ℂ) *
      Complex.exp ((alpha : ℂ) *
        Complex.log (-(w - (epsilon : ℂ))))
  have hleft : L =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] R := by
    filter_upwards [self_mem_nhdsWithin] with epsilon heps
    have hre : (w - (epsilon : ℂ)).re < 0 := by
      simp only [Complex.sub_re, Complex.ofReal_re, hwre,
        zero_sub]
      exact neg_lt_zero.mpr heps
    have hnonzero : w - (epsilon : ℂ) ≠ 0 := by
      intro he
      have hz : (w - (epsilon : ℂ)).re = 0 := by
        rw [he]
        simp
      linarith
    exact Kyprianou.Ch01.stableGammaComplexDeficitValueStrictLeft
      alpha h0 h1 (w - (epsilon : ℂ)) hnonzero hre
  have hl := Kyprianou.Ch01.stableGammaComplexDeficitImaginaryIntegralRightLimit
    alpha h0 h1 w hw hwre hwim
  have hr := Kyprianou.Ch01.stableGammaComplexDeficitImaginaryPhaseRightLimit
    alpha h0 h1 w hw hwre hwim
  have hr' : Tendsto R (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) * Complex.log (-w)))) :=
    hr.const_mul _
  exact tendsto_nhds_unique (by simpa [L] using hl)
    (by apply hr'.congr' hleft.symm)
