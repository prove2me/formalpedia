-- Prove2me | solution 1 for Kyprianou.Ch01.stableAboveOneTailComplexMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:43:01.628203+00:00
-- url     : https://prove2.me/submissions/9a0e3320-86d0-4da1-987d-00a8ba8e0c2b

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaAboveOneLargeJumpPowerIntegral
open MeasureTheory Set Real Complex
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    (∫ r in Set.Ioi (0 : ℝ),
      (if r < 1 then (0 : ℂ) else (((r ^ (-alpha) : ℝ) : ℂ))) ∂volume) =
      (((1 / (alpha - 1) : ℝ) : ℂ)) := by
  calc
    (∫ r in Set.Ioi (0 : ℝ),
        (if r < 1 then (0 : ℂ) else (((r ^ (-alpha) : ℝ) : ℂ))) ∂volume) =
      ∫ r in Set.Ioi (0 : ℝ),
        (Set.Ici (1 : ℝ)).indicator
          (fun t : ℝ => (((t ^ (-alpha) : ℝ) : ℂ))) r ∂volume := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        by_cases h : r < 1
        · simp [Set.indicator, h, Set.mem_Ici, le_of_lt h]
        · simp [Set.indicator, h, Set.mem_Ici, le_of_not_gt h]
    _ = (∫ r in Set.Ici (1 : ℝ),
          (((r ^ (-alpha) : ℝ) : ℂ)) ∂volume) := by
          rw [setIntegral_indicator measurableSet_Ici]
          have hs : Set.Ici (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) := by
            intro r hr
            exact lt_of_lt_of_le zero_lt_one (show (1 : ℝ) ≤ r from hr)
          rw [Set.inter_eq_right.mpr hs]
    _ = (∫ r in Set.Ioi (1 : ℝ),
          (((r ^ (-alpha) : ℝ) : ℂ)) ∂volume) := by
          exact integral_Ici_eq_integral_Ioi
    _ = (((1 / (alpha - 1) : ℝ) : ℂ)) := by
          change (∫ r : ℝ, (((r ^ (-alpha) : ℝ) : ℂ)) ∂
            (volume.restrict (Set.Ioi (1 : ℝ)))) = _
          exact_mod_cast
            (Kyprianou.Ch01.stableAlphaAboveOneLargeJumpPowerIntegral
              alpha ha1 ha2)
