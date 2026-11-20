-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianFourierWithDensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:49:48.259083+00:00
-- url     : https://prove2.me/submissions/540d5e69-3e7c-4fd7-b93a-1889908150fe

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution (b : ℝ) (hb : 0 < b) (theta : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ), ((1 : ℂ) -
        Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂
      ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ => ENNReal.ofReal
          ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
                Real.exp (-(b ^ 2 * x / 2)))))) =
    (∫ x in Set.Ioi (0 : ℝ), ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
                Real.exp (-(b ^ 2 * x / 2))) • ((1 : ℂ) -
        Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))) ∂volume) := by
  let S : Set ℝ := Set.Ioi (0 : ℝ)
  let f : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
      Real.exp (-(b ^ 2 * x / 2)))
  let g : ℝ → ℂ := fun x => (1 : ℂ) -
    Complex.exp (Complex.I * ((theta * x : ℝ) : ℂ))
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hfin : ∀ᵐ x ∂volume.restrict S, f x < ∞ := by
    filter_upwards [] with x
    exact ENNReal.ofReal_lt_top
  have hrw : (∫ x in S, g x ∂(volume.restrict S).withDensity f) =
      ∫ x in S, (f x).toReal • g x ∂volume := by
    rw [← restrict_withDensity measurableSet_Ioi f]
    rw [Measure.restrict_restrict_of_subset (Set.Subset.rfl)]
    exact setIntegral_withDensity_eq_setIntegral_toReal_smul
      hf hfin g measurableSet_Ioi
  change (∫ x in S, g x ∂(volume.restrict S).withDensity f) = _
  rw [hrw]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hd : 0 ≤ (1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
      Real.exp (-(b ^ 2 * x / 2)) := by positivity
  simp only [f, g, ENNReal.toReal_ofReal hd]
