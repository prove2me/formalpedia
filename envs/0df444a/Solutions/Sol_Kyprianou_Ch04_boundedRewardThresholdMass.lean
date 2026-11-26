-- Prove2me | solution 1 for Kyprianou.Ch04.boundedRewardThresholdMass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:45:31.701677+00:00
-- url     : https://prove2.me/submissions/195832e3-d734-4b61-a40b-44d80494f2a0

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- A bounded measurable nonnegative reward bounds the mass of any event on which it exceeds a constant. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → ℝ) (hm : Measurable g) (h0 : ∀ w, 0 ≤ g w) (h1 : ∀ w, g w ≤ 1)
    (E : Set Ω) (c : ℝ) (hc : 0 ≤ c) (hE : ∀ w ∈ E, c ≤ g w) :
    c * (P E).toReal ≤ ∫ w, g w ∂P := by
  let B := {w : Ω | c ≤ g w}
  have hB : MeasurableSet B := measurableSet_le measurable_const hm
  have hsub : E ⊆ B := hE
  have hmass : (P E).toReal ≤ (P B).toReal :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
  let b : Ω → ℝ := B.indicator (fun _ => c)
  have hbi : Integrable b P := (integrable_const c).indicator hB
  have hgi : Integrable g P :=
    (integrable_const (1 : ℝ)).mono hm.aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 w),Real.norm_eq_abs,abs_one]
        exact h1 w)
  have hle (w : Ω) : b w ≤ g w := by
    by_cases hw : w ∈ B
    · change B.indicator (fun _ => c) w ≤ g w
      rw [indicator_of_mem hw]
      exact hw
    · change B.indicator (fun _ => c) w ≤ g w
      rw [indicator_of_notMem hw]
      exact h0 w
  have h := integral_mono hbi hgi hle
  have hint : (∫ w, b w ∂P) = c * (P B).toReal := by
    rw [show b = B.indicator (fun _ => c) from rfl,integral_indicator hB,integral_const]
    simp [Measure.real,mul_comm]
  rw [hint] at h
  exact (mul_le_mul_of_nonneg_left hmass hc).trans h
