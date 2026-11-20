-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianLevyMeasureSourceExact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:42:11.82008+00:00
-- url     : https://prove2.me/submissions/a5267460-479b-4aec-ac91-1eb9d9d1823b

import Mathlib
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_isLevyMeasure_iff
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianLevyMeasureZeroAtom
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianLevyMeasureTruncatedMomentFinite
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
    IsLevyMeasure Pi := by
  apply (ProbabilityTheory.IsLevyMeasure.isLevyMeasure_iff).2
  exact ⟨Kyprianou.Ch01.inverseGaussianLevyMeasureZeroAtom b hb,
    Kyprianou.Ch01.inverseGaussianLevyMeasureTruncatedMomentFinite b hb⟩
