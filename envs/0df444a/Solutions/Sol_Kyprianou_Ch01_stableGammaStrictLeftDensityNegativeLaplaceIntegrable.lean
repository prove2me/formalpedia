-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftDensityNegativeLaplaceIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:37:00.442718+00:00
-- url     : https://prove2.me/submissions/56a98367-beba-4dc8-93c6-a2a3982e257f

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftRealExpWeightedIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter ProbabilityTheory Kyprianou.Ch01
open scoped ENNReal
set_option autoImplicit false

/-- Gamma density has finite exponential moments at all negative rates. -/
theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (t : ℝ) (ht : t < 0) :
    Integrable (fun r : ℝ => Real.exp (t * r))
      ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun r : ℝ => ENNReal.ofReal (r ^ (-alpha)))) := by
  let f : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r ^ (-alpha))
  let mu : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hfinite : ∀ᵐ r ∂mu, f r < ∞ := by
    filter_upwards [] with r
    exact ENNReal.ofReal_lt_top
  change Integrable (fun r : ℝ => Real.exp (t * r)) (mu.withDensity f)
  rw [integrable_withDensity_iff (μ := mu) hf hfinite]
  have hreal : IntegrableOn (fun r : ℝ => Real.exp (t * r) * r ^ (-alpha))
      (Set.Ioi (0 : ℝ)) :=
    Kyprianou.Ch01.stableGammaStrictLeftRealExpWeightedIntegrable alpha h0 h1 t ht
  apply hreal.congr_fun
  · intro r hr
    have hp : 0 ≤ r ^ (-alpha) := Real.rpow_nonneg hr.le _
    simp [f, ENNReal.toReal_ofReal hp]
  · exact measurableSet_Ioi
