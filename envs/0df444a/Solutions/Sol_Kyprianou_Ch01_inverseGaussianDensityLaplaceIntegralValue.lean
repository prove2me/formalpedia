-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianDensityLaplaceIntegralValue
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:02:13.281655+00:00
-- url     : https://prove2.me/submissions/87743bfd-d640-44a9-b715-5372a446fb51
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityLaplaceWithDensity
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianDensityLaplaceWeightedValue
open MeasureTheory Set Kyprianou.Ch01
open scoped ENNReal
set_option autoImplicit false

theorem solution
    (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    let IG : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-((s - b * x) ^ 2 / (2 * x)))))
    ∀ q : ℝ, 0 ≤ q →
      (∫ x, Real.exp (-q * x) ∂IG) =
        Real.exp (-s * (Real.sqrt (b ^ 2 + 2 * q) - b)) := by
  intro IG q hq
  have hD := Kyprianou.Ch01.inverseGaussianDensityLaplaceWithDensity
    s b hs hb q
  have hV := Kyprianou.Ch01.inverseGaussianDensityLaplaceWeightedValue
    s b hs hb q hq
  simpa only [IG] using hD.trans hV
