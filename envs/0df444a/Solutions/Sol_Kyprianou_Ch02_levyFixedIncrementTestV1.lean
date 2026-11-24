-- Prove2me | solution 1 for Kyprianou.Ch02.levyFixedIncrementTestV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:01:14.726696+00:00
-- url     : https://prove2.me/submissions/dbf47306-1ca0-48c9-b8b9-6c877f1904be

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P)
    (a b : ℝ≥0) (hab : a ≤ b)
    (H : ℝ → ℂ) (hH : Measurable H) :
    (∫ ω, H (X b ω - X a ω) ∂P) =
      ∫ ω, H (X (((b : ℝ) - (a : ℝ)).toNNReal) ω) ∂P := by
  have he : a + (b - a) = b := add_tsub_cancel_of_le hab
  have hlag : ((b : ℝ) - (a : ℝ)).toNNReal = b - a := by
    rw [← NNReal.coe_sub hab, Real.toNNReal_coe]
  simpa [hlag, increment, he, hX.start_zero, Function.comp_def] using
    ((hX.stationary_increments a (b - a)).comp hH).integral_eq
