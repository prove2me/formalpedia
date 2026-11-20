-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianJumpCompensatorIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:16:24.515352+00:00
-- url     : https://prove2.me/submissions/405e39fa-4652-4fcb-8ef6-3bf19f172626

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianJumpWeightedVolumeIntegrable
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (b : ℝ) (hb : 0 < b) :
    let Pi : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))))
    ∀ theta : ℝ,
      IntegrableOn
        (fun x : ℝ => (1 - Complex.exp
            (Complex.I * ((theta * x : ℝ) : ℂ))))
        (Set.Ioi (0 : ℝ)) Pi := by
  intro Pi theta
  have hden : Measurable (fun x : ℝ =>
      ENNReal.ofReal
        ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
          Real.exp (-(b ^ 2 * x / 2)))) := by fun_prop
  have hfinite : ∀ᵐ x ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ENNReal.ofReal
        ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
          Real.exp (-(b ^ 2 * x / 2))) < ⊤ :=
    Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  have hweighted :=
    Kyprianou.Ch01.inverseGaussianJumpWeightedVolumeIntegrable
      b hb theta
  have hwhole : Integrable
      (fun x : ℝ => (1 - Complex.exp
        (Complex.I * ((theta * x : ℝ) : ℂ))))
      ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-(b ^ 2 * x / 2))))) :=
    (integrable_withDensity_iff_integrable_smul' hden hfinite).2
      hweighted
  exact hwhole.integrableOn
