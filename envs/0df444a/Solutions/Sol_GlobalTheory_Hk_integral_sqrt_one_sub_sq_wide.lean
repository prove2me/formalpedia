-- Prove2me | solution 1 for GlobalTheory.Hk.integral_sqrt_one_sub_sq_wide
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:35:04.054087+00:00
-- url     : https://prove2.me/submissions/12fc7e17-0394-450b-a887-e4826b8dec5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
theorem _root_.solution (a b : ℝ) (ha : a ≤ -1) (hb : 1 ≤ b) :
    ∫ t in a..b, Real.sqrt (1 - t ^ 2) = Real.pi / 2 := by
  have hc : Continuous (fun t : ℝ => Real.sqrt (1 - t ^ 2)) := by fun_prop
  have hi : ∀ p q : ℝ, IntervalIntegrable (fun t : ℝ => Real.sqrt (1 - t ^ 2))
      MeasureTheory.volume p q := fun p q => hc.intervalIntegrable p q
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi a (-1)) (hi (-1) b),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-1) 1) (hi 1 b), integral_sqrt_one_sub_sq]
  have z1 : ∫ t in a..(-1), Real.sqrt (1 - t ^ 2) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le ha] at ht
      apply Real.sqrt_eq_zero'.mpr
      nlinarith [ht.1, ht.2]
  have z2 : ∫ t in (1:ℝ)..b, Real.sqrt (1 - t ^ 2) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le hb] at ht
      apply Real.sqrt_eq_zero'.mpr
      nlinarith [ht.1, ht.2]
  rw [z1, z2]
  ring
end GlobalTheory.Hk
