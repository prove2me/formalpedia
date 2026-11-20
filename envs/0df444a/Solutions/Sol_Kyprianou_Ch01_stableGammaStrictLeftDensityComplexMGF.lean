-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftDensityComplexMGF
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:41:03.642641+00:00
-- url     : https://prove2.me/submissions/fafd5b9e-dcb0-4c36-8c44-47bfdf012991

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter ProbabilityTheory Kyprianou.Ch01
open scoped ENNReal
set_option autoImplicit false

/-- Exact weighted density conversion to the complex MGF. -/
theorem solution (alpha : ℝ) (w : ℂ) :
    ProbabilityTheory.complexMGF (fun r : ℝ => r)
      ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (r ^ (-alpha)))) w =
    (∫ r in Set.Ioi (0 : ℝ),
      Complex.exp (w * (r : ℂ)) *
        ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) := by
  let f : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r ^ (-alpha))
  let mu : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hfinite : ∀ᵐ r ∂mu, f r < ∞ := by
    filter_upwards [] with r
    exact ENNReal.ofReal_lt_top
  have h := integral_withDensity_eq_integral_toReal_smul
    (μ := mu) (f := f) hf hfinite
    (fun r : ℝ => Complex.exp (w * (r : ℂ)))
  change (∫ r, Complex.exp (w * (r : ℂ)) ∂mu.withDensity f) = _
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hp : 0 ≤ r ^ (-alpha) := Real.rpow_nonneg hr.le _
  simp only [f, ENNReal.toReal_ofReal hp, Complex.real_smul]
  ring
