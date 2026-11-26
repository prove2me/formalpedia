-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41RampDerivativeV10
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:39:21.721746+00:00
-- url     : https://prove2.me/submissions/a7d0c53d-b269-4a10-b8e2-085a9003684a

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology Interval
set_option autoImplicit false
theorem solution
    (ε : ℝ) (he : 0 < ε) :
    let r : ℝ → ℝ := fun x => min 1 (max 0 (x / ε))
    let p : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, r u
    ContDiff ℝ 1 p ∧ (∀ x, HasDerivAt p (r x) x) ∧
      LipschitzWith 1 p := by
  let r : ℝ → ℝ := fun x => min 1 (max 0 (x / ε))
  let p : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, r u
  have hr : Continuous r := by
    dsimp [r]
    fun_prop
  have hp (x : ℝ) : HasDerivAt p (r x) x :=
    intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable _ _)
      hr.aestronglyMeasurable.stronglyMeasurableAtFilter hr.continuousAt
  have hd : Differentiable ℝ p := fun x => (hp x).differentiableAt
  have hder : deriv p = r := funext fun x => (hp x).deriv
  refine ⟨contDiff_one_iff_deriv.mpr ⟨hd, by rw [hder]; exact hr⟩, hp, ?_⟩
  apply lipschitzWith_of_nnnorm_deriv_le hd
  intro x
  rw [hder]
  change ‖r x‖₊ ≤ 1
  apply NNReal.coe_le_coe.mp
  change ‖r x‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by norm_num) (le_max_left _ _))]
  exact min_le_left _ _
