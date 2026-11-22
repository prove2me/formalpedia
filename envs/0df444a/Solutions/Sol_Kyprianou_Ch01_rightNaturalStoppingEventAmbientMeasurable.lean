-- Prove2me | solution 1 for Kyprianou.Ch01.rightNaturalStoppingEventAmbientMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:55:26.047216+00:00
-- url     : https://prove2.me/submissions/0f7be86d-2f32-41bb-9956-457f43c82814

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_le_ambient

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsNaturalRightStoppingTime X τ)
    (t : ℝ≥0) :
    MeasurableSet {ω : Ω | τ ω ≤ (t : WithTop ℝ≥0)} := by
  exact (MeasurableSpace.le_def.mp
    (Kyprianou.Ch01.naturalSigmaRight_le_ambient X hXmeas t))
      _ (hτ t)
