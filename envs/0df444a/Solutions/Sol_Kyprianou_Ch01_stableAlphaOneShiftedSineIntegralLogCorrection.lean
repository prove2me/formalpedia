-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneShiftedSineIntegralLogCorrection
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:30:00.406588+00:00
-- url     : https://prove2.me/submissions/ff22dd01-72cb-4e1d-be7c-000e19b76755

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneShiftedSineIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneShiftedCutoffDifference
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffLogIntegralAllPositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! The compensated sine Lévy integral acquires log z from the cutoff displacement. -/
theorem solution
    (z : ℝ) (hz : 0 < z) :
    (∫ u in Set.Ioi (0 : ℝ), ((u * (if u < z then (1 : ℝ) else 0) - Real.sin u) / u ^ 2) ∂volume) =
      (∫ u in Set.Ioi (0 : ℝ), ((u * (if u < 1 then (1 : ℝ) else 0) - Real.sin u) / u ^ 2) ∂volume) +
        Real.log z := by
  have hzInt := Kyprianou.Ch01.stableAlphaOneShiftedSineIntegrable z hz
  have h1Int := Kyprianou.Ch01.stableAlphaOneShiftedSineIntegrable 1
    (by norm_num : (0 : ℝ) < 1)
  have hdiff :
      (∫ u in Set.Ioi (0 : ℝ), ((u * (if u < z then (1 : ℝ) else 0) - Real.sin u) / u ^ 2) ∂volume) -
        (∫ u in Set.Ioi (0 : ℝ), ((u * (if u < 1 then (1 : ℝ) else 0) - Real.sin u) / u ^ 2) ∂volume) =
      (∫ u in Set.Ioi (0 : ℝ), ((if u < z then (1 : ℝ) else 0) -
        (if u < 1 then (1 : ℝ) else 0)) / u ∂volume) := by
    rw [← integral_sub hzInt h1Int]
    apply integral_congr_ae
    filter_upwards [] with u
    exact Kyprianou.Ch01.stableAlphaOneShiftedCutoffDifference z u
  have hcut :=
    Kyprianou.Ch01.stableAlphaOneCutoffLogIntegralAllPositive z hz
  linarith
