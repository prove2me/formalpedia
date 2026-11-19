-- Prove2me | solution 1 for Kyprianou.Ch01.sineCosineFiniteIntervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:26:34.716364+00:00
-- url     : https://prove2.me/submissions/3a656ddb-17c1-40b8-aaca-10e80437ff7b

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Real
open scoped Topology Interval
set_option autoImplicit false

theorem solution (R : ℝ) (hR : 0 < R) :
    IntervalIntegrable (fun x : ℝ => Real.sin x / x) volume 0 R ∧
    IntervalIntegrable
      (fun x : ℝ => (1 - Real.cos x) / x ^ 2) volume 0 R := by
  have hSin :
      IntervalIntegrable (fun x : ℝ => Real.sin x / x) volume 0 R := by
    have hsinc : IntervalIntegrable Real.sinc volume 0 R :=
      Real.continuous_sinc.intervalIntegrable 0 R
    apply hsinc.congr_ae
    apply MeasureTheory.ae_restrict_of_ae
    filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with x hx
    exact Real.sinc_of_ne_zero hx
  have hCos :
      IntegrableOn (fun x : ℝ => (1 - Real.cos x) / x ^ 2)
        (Set.Ioc (0 : ℝ) R) volume := by
    exact Kyprianou.Ch01.stableAlphaOneCosineIntegral.1.mono_set
      (by intro x hx; exact hx.1)
  exact ⟨hSin,
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hR)).2 hCos⟩
