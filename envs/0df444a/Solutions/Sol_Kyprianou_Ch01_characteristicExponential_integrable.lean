-- Prove2me | solution 1 for Kyprianou.Ch01.characteristicExponential_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:10:16.198448+00:00
-- url     : https://prove2.me/submissions/3dfdbead-e6d4-4570-8108-f8df352a5f8f

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Complex characteristic exponentials have a deterministic modulus. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hmeas : ∀ t : ℝ≥0, Measurable (X t))
    (theta : ℝ) (Psi : ℂ) (t : ℝ≥0) :
    Integrable
      (fun ω => Complex.exp
        (Complex.I * (theta : ℂ) * (X t ω : ℂ) +
          ((t : ℝ) : ℂ) * Psi)) P := by
  have hm : Measurable (fun ω => Complex.exp
      (Complex.I * (theta : ℂ) * (X t ω : ℂ) +
        ((t : ℝ) : ℂ) * Psi)) := by
    fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable
    (Real.exp ((t : ℝ) * Psi.re))
  filter_upwards [] with ω
  simp [Complex.norm_exp, Complex.add_re, Complex.mul_re]
