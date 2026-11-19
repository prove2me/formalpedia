-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianLevyMeasureZeroAtom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:53:19.904734+00:00
-- url     : https://prove2.me/submissions/9cf2952f-46ee-4002-9323-2891162a07bc

import Mathlib
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
    Pi {(0 : ℝ)} = 0 := by
  change ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun x : ℝ =>
      ENNReal.ofReal
        ((1 / Real.sqrt (2 * Real.pi * x ^ 3)) *
          Real.exp (-(b ^ 2 * x / 2))))) {(0 : ℝ)} = 0
  rw [withDensity_apply _ (measurableSet_singleton (0 : ℝ))]
  apply setLIntegral_measure_zero
  rw [Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
  simp
