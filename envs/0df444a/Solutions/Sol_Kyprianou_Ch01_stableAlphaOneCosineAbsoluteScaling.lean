-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCosineAbsoluteScaling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:31:28.581783+00:00
-- url     : https://prove2.me/submissions/9e33e0db-8a84-4fd6-bffa-07ab402eb0f1

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineScaling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! Evenness upgrades the positive-frequency stable Lévy exponent to all real frequencies. -/
theorem solution
    (xi : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ), (1 - Real.cos (xi * r)) / r ^ 2 ∂volume) =
      Real.pi * |xi| / 2 := by
  by_cases hpos : 0 < xi
  · simpa [abs_of_pos hpos] using
      Kyprianou.Ch01.stableAlphaOneCosineScaling xi hpos
  by_cases hneg : xi < 0
  · have hp : 0 < -xi := neg_pos.mpr hneg
    have h := Kyprianou.Ch01.stableAlphaOneCosineScaling (-xi) hp
    have hEq :
        (∫ r in Set.Ioi (0 : ℝ),
          (1 - Real.cos (xi * r)) / r ^ 2 ∂volume) =
        (∫ r in Set.Ioi (0 : ℝ),
          (1 - Real.cos ((-xi) * r)) / r ^ 2 ∂volume) := by
      congr 1
      funext r
      rw [neg_mul, Real.cos_neg]
    rw [hEq]
    simpa [abs_of_neg hneg] using h
  have hx : xi = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
  subst xi
  simp
