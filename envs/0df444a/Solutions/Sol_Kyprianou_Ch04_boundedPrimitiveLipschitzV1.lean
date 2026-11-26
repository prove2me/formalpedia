-- Prove2me | solution 1 for Kyprianou.Ch04.boundedPrimitiveLipschitzV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:26:50.159211+00:00
-- url     : https://prove2.me/submissions/bb4432b3-0b13-49b7-8aef-9a9c2a406741

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A bounded measurable nonnegative-time integrand has a Lipschitz primitive. -/
theorem solution (g : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ s : ℝ, 0 ≤ s → |g s| ≤ C) :
    ∀ u v : NNReal, u ≤ v →
      |(∫ s in Icc (0 : ℝ) (v : ℝ), g s ∂volume) -
        (∫ s in Icc (0 : ℝ) (u : ℝ), g s ∂volume)| ≤
        C * ((v : ℝ) - (u : ℝ)) := by
  intro u v huv
  have huv' : (u : ℝ) ≤ (v : ℝ) := NNReal.coe_le_coe.mpr huv
  have hi (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable g volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    apply Integrable.of_bound hg.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    exact hb x (ha.trans hx.1.le)
  simp only [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le u.coe_nonneg,
    ← intervalIntegral.integral_of_le v.coe_nonneg]
  have h := intervalIntegral.integral_add_adjacent_intervals
    (hi 0 u le_rfl u.coe_nonneg) (hi u v u.coe_nonneg huv')
  rw [← h, add_sub_cancel_left]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := g) (a := (u : ℝ)) (b := (v : ℝ)) (C := C)
    (fun x hx => by
      rw [uIoc_of_le huv'] at hx
      rw [Real.norm_eq_abs]
      exact hb x (u.coe_nonneg.trans hx.1.le))
  simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huv')] using hh
