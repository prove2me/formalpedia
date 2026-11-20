-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneComplexProductIBP
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:25:17.14948+00:00
-- url     : https://prove2.me/submissions/47c8ace7-89b6-4189-b3b9-c1ec0c9ad1a5

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableCompensatedFourierNumeratorDerivative
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneNegativePowerAntiderivative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex Real Filter
set_option autoImplicit false

/-- Compact-interval complex integration by parts with the exact stable numerator. -/
theorem solution
    (alpha a c : ℝ) (ha : 1 < alpha) (hb : alpha < 2)
    (hapos : 0 < a) (hac : a < c) :
    (∫ r in a..c,
      (Complex.exp (Complex.I * (r : ℂ)) - 1 -
        Complex.I * (r : ℂ)) *
        (((r ^ (-(alpha + 1)) : ℝ)) : ℂ)) =
      (Complex.exp (Complex.I * (c : ℂ)) - 1 -
        Complex.I * (c : ℂ)) *
        (((c ^ (-alpha) / (-alpha) : ℝ)) : ℂ) -
      (Complex.exp (Complex.I * (a : ℂ)) - 1 -
        Complex.I * (a : ℂ)) *
        (((a ^ (-alpha) / (-alpha) : ℝ)) : ℂ) -
      (∫ r in a..c,
        (Complex.I * (Complex.exp (Complex.I * (r : ℂ)) - 1)) *
          (((r ^ (-alpha) / (-alpha) : ℝ)) : ℂ)) := by
  let u : ℝ → ℂ := fun r =>
    Complex.exp (Complex.I * (r : ℂ)) - 1 -
      Complex.I * (r : ℂ)
  let v : ℝ → ℂ := fun r => ((r ^ (-alpha) / (-alpha) : ℝ) : ℂ)
  let u' : ℝ → ℂ := fun r =>
    Complex.I * (Complex.exp (Complex.I * (r : ℂ)) - 1)
  let v' : ℝ → ℂ := fun r => ((r ^ (-(alpha + 1)) : ℝ) : ℂ)
  have hpos : ∀ r ∈ uIcc a c, 0 < r := by
    intro r hr
    rw [uIcc_of_le hac.le] at hr
    exact lt_of_lt_of_le hapos hr.1
  have hu : ∀ r ∈ uIcc a c, HasDerivAt u (u' r) r := by
    intro r hr
    exact Kyprianou.Ch01.stableCompensatedFourierNumeratorDerivative r
  have hv : ∀ r ∈ uIcc a c, HasDerivAt v (v' r) r := by
    intro r hr
    exact (Kyprianou.Ch01.stableAlphaAboveOneNegativePowerAntiderivative
      alpha r ha hb (hpos r hr)).ofReal_comp
  have hucont : Continuous u := by
    dsimp [u]
    fun_prop
  have hu'cont : Continuous u' := by
    dsimp [u']
    fun_prop
  have hvi : IntervalIntegrable v' volume a c := by
    have hcont : ContinuousOn v' (uIcc a c) := by
      intro r hr
      have h : ContinuousAt (fun t : ℝ => t ^ (-(alpha + 1))) r :=
        continuousAt_id.rpow_const (Or.inl (hpos r hr).ne')
      exact (continuous_ofReal.continuousAt.comp_continuousWithinAt
        h.continuousWithinAt)
    exact hcont.intervalIntegrable
  have hui : IntervalIntegrable u' volume a c :=
    hu'cont.continuousOn.intervalIntegrable
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := u) (v := v) (u' := u') (v' := v')
    hu hv hui hvi
  simpa only [u, v, u', v'] using hparts
