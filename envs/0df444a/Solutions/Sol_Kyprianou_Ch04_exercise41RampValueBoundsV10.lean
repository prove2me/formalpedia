-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41RampValueBoundsV10
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:43:32.163607+00:00
-- url     : https://prove2.me/submissions/261d9045-f8cd-41be-9479-bd25454ef95d

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_Kyprianou_Ch04_exercise41RampZeroV10
import Theorems.Thm_Kyprianou_Ch04_exercise41RampPositiveBoundsV10
import Theorems.Thm_Kyprianou_Ch04_exercise41RampLowerBoundV10
open Kyprianou.Ch04
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false
theorem solution
    (ε : ℝ) (he : 0 < ε) (x : ℝ) :
    let r : ℝ → ℝ := fun u => min 1 (max 0 (u / ε))
    let p : ℝ → ℝ := fun y => ∫ u in (0 : ℝ)..y, r u
    (x ≤ 0 → p x = 0) ∧
      0 ≤ p x ∧ p x ≤ max 0 x ∧ max 0 x - ε ≤ p x := by
  let r : ℝ → ℝ := fun u => min 1 (max 0 (u / ε))
  let p : ℝ → ℝ := fun y => ∫ u in (0 : ℝ)..y, r u
  have hz (hx : x ≤ 0) : p x = 0 := exercise41RampZeroV10 ε he x hx
  change (x ≤ 0 → p x = 0) ∧ 0 ≤ p x ∧ p x ≤ max 0 x ∧ max 0 x - ε ≤ p x
  refine ⟨hz, ?_⟩
  by_cases hx : x ≤ 0
  · rw [hz hx, max_eq_left hx]
    exact ⟨le_rfl,le_rfl,by linarith⟩
  have hxp : 0 ≤ x := le_of_lt (lt_of_not_ge hx)
  obtain ⟨h0,h1⟩ := exercise41RampPositiveBoundsV10 ε x hxp
  change 0 ≤ p x at h0
  change p x ≤ x at h1
  rw [max_eq_right hxp]
  refine ⟨h0,h1,?_⟩
  by_cases he' : x ≤ ε
  · linarith
  exact exercise41RampLowerBoundV10 ε he x (le_of_lt (lt_of_not_ge he'))
