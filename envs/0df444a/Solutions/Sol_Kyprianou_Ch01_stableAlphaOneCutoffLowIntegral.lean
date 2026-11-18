-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCutoffLowIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:08:54.8602+00:00
-- url     : https://prove2.me/submissions/981ce68d-ecc3-46d5-a005-9798208ab2ba

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffDifferenceLowFrequency
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCutoffLogIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! Low-frequency stable compensation correction integrates to the signed logarithm. -/
theorem solution
    (z : ℝ) (hz0 : 0 < z) (hz1 : z ≤ 1) :
    (∫ u in Set.Ioi (0 : ℝ),
      ((if u < z then (1 : ℝ) else 0) -
        (if u < 1 then (1 : ℝ) else 0)) / u ∂volume) =
      Real.log z := by
  have hs : Set.Ioi (0 : ℝ) ∩ Set.Ico z (1 : ℝ) =
      Set.Ico z (1 : ℝ) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ico]
    constructor
    · exact And.right
    · intro hu
      exact ⟨lt_of_lt_of_le hz0 hu.1, hu⟩
  calc
    (∫ u in Set.Ioi (0 : ℝ),
      ((if u < z then (1 : ℝ) else 0) -
        (if u < 1 then (1 : ℝ) else 0)) / u ∂volume) =
        ∫ u in Set.Ioi (0 : ℝ),
          -((Set.Ico z (1 : ℝ)).indicator (fun x : ℝ => x⁻¹) u) ∂volume := by
            apply integral_congr_ae
            filter_upwards [] with u
            exact Kyprianou.Ch01.stableAlphaOneCutoffDifferenceLowFrequency z u hz0 hz1
    _ = -(∫ u in Set.Ioi (0 : ℝ),
          (Set.Ico z (1 : ℝ)).indicator (fun x : ℝ => x⁻¹) u ∂volume) := by
      rw [integral_neg]
    _ = -(∫ u in Set.Ioi (0 : ℝ) ∩ Set.Ico z (1 : ℝ), u⁻¹ ∂volume) := by
      rw [setIntegral_indicator measurableSet_Ico]
    _ = -(∫ u in Set.Ioc z (1 : ℝ), u⁻¹ ∂volume) := by
      rw [hs, integral_Ico_eq_integral_Ioc]
    _ = -(∫ u in z..(1 : ℝ), u⁻¹ ∂volume) := by
      rw [intervalIntegral.integral_of_le hz1]
    _ = ∫ u in (1 : ℝ)..z, u⁻¹ ∂volume := by
      rw [intervalIntegral.integral_symm]
      simp
    _ = Real.log z := Kyprianou.Ch01.stableAlphaOneCutoffLogIntegral z hz0
