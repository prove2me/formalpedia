-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCutoffHighIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:06:42.84352+00:00
-- url     : https://prove2.me/submissions/bd556fcb-4cd7-4425-93d9-663e539d15cd

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffDifferenceHighFrequency
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffLogIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! High-frequency alpha-one cutoff correction integrates to log z on [1,z). -/
theorem solution
    (z : ℝ) (hz : 1 ≤ z) :
    (∫ u in Set.Ioi (0 : ℝ),
      ((if u < z then (1 : ℝ) else 0) -
        (if u < 1 then (1 : ℝ) else 0)) / u ∂volume) =
      Real.log z := by
  have hs : Set.Ioi (0 : ℝ) ∩ Set.Ico (1 : ℝ) z =
      Set.Ico (1 : ℝ) z := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ico]
    constructor
    · exact And.right
    · intro hu
      exact ⟨lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hu.1, hu⟩
  calc
    (∫ u in Set.Ioi (0 : ℝ),
      ((if u < z then (1 : ℝ) else 0) -
        (if u < 1 then (1 : ℝ) else 0)) / u ∂volume) =
        ∫ u in Set.Ioi (0 : ℝ),
          (Set.Ico (1 : ℝ) z).indicator (fun x : ℝ => x⁻¹) u ∂volume := by
            apply integral_congr_ae
            filter_upwards [] with u
            exact Kyprianou.Ch01.stableAlphaOneCutoffDifferenceHighFrequency z u hz
    _ = ∫ u in Set.Ioi (0 : ℝ) ∩ Set.Ico (1 : ℝ) z, u⁻¹ ∂volume :=
      setIntegral_indicator measurableSet_Ico
    _ = ∫ u in Set.Ioc (1 : ℝ) z, u⁻¹ ∂volume := by
      rw [hs, integral_Ico_eq_integral_Ioc]
    _ = ∫ u in (1 : ℝ)..z, u⁻¹ ∂volume := by
      rw [intervalIntegral.integral_of_le hz]
    _ = Real.log z :=
      Kyprianou.Ch01.stableAlphaOneCutoffLogIntegral z
        (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hz)
