-- Prove2me | solution 1 for MeasureTheory.isProbabilityMeasure_mixture
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T15:10:36.92265+00:00
-- url     : https://prove2.me/submissions/5c94de8a-f1cd-4b1d-95de-b02ff24d2aa7

import Mathlib

-- carved verbatim out of submission 505563a3-50a1-4701-87c6-32f58db20f14, lines 96-106

section
set_option autoImplicit false
open scoped BigOperators
open MeasureTheory

theorem solution {Z : Type*} [MeasurableSpace Z]
    (π ρ : Measure Z) (hπ : IsProbabilityMeasure π) (hρ : IsProbabilityMeasure ρ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IsProbabilityMeasure (ENNReal.ofReal a • π + ENNReal.ofReal b • ρ) := by
  letI := hπ
  letI := hρ
  constructor
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add ha hb, hab]
  norm_num

end
