-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianDensityLaplaceWithDensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:59:57.236373+00:00
-- url     : https://prove2.me/submissions/accd9619-2e95-4c47-a62a-be2554caa079

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory Set Kyprianou.Ch01
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (s b : ℝ) (hs : 0 < s) (hb : 0 < b) (q : ℝ) :
    (∫ x, Real.exp (-q * x) ∂
      ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-((s - b * x) ^ 2 / (2 * x))))))) =
      ∫ x in Set.Ioi (0 : ℝ),
        ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
        Real.exp (-((s - b * x) ^ 2 / (2 * x)))) • Real.exp (-q * x) ∂volume := by
  let mu : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let f : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
      Real.exp (-((s - b * x) ^ 2 / (2 * x))))
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hfin : ∀ᵐ x ∂mu, f x < ∞ := by
    filter_upwards [] with x
    exact ENNReal.ofReal_lt_top
  change (∫ x, Real.exp (-q * x) ∂mu.withDensity f) = _
  rw [integral_withDensity_eq_integral_toReal_smul hf hfin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hp : 0 ≤ (s / Real.sqrt (2 * Real.pi * x ^ 3)) *
      Real.exp (-((s - b * x) ^ 2 / (2 * x))) := by positivity
  simp only [f, ENNReal.toReal_ofReal hp]
