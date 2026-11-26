-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_bounded_nonnegative_variance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:58:11.825602+00:00
-- url     : https://prove2.me/submissions/18272575-25f4-4af1-a392-57f16b71dc06

import Mathlib
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → ℝ) (C : ℝ) (hC : 0 ≤ C) (hm : AEMeasurable F P)
    (hb : ∀ᵐ w ∂P, 0 ≤ F w ∧ F w ≤ C) :
    MemLp F 2 P ∧ variance F P ≤ C*(∫ w, F w ∂P) := by
  have hL : MemLp F 2 P := MemLp.of_bound hm.aestronglyMeasurable C (by
    filter_upwards [hb] with w hw
    rw [Real.norm_of_nonneg hw.1]
    exact hw.2)
  have hi := hL.integrable (by norm_num)
  have hs : Integrable (fun w => (F w)^2) P := hL.integrable_sq
  refine ⟨hL,(variance_le_expectation_sq hm.aestronglyMeasurable).trans ?_⟩
  rw [← integral_const_mul]
  apply integral_mono_ae hs (hi.const_mul C)
  filter_upwards [hb] with w hw
  nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2)]
