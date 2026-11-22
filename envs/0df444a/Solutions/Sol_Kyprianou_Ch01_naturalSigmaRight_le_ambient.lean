-- Prove2me | solution 1 for Kyprianou.Ch01.naturalSigmaRight_le_ambient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T16:48:45.576243+00:00
-- url     : https://prove2.me/submissions/03d28d52-e51e-489f-845d-28e8018e6703

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_le_ambient

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (t : ℝ≥0) :
    naturalSigmaRight X t ≤ (inferInstance : MeasurableSpace Ω) := by
  have ht : t < t + 1 := lt_add_one t
  calc
    naturalSigmaRight X t ≤ naturalSigma X (t + 1) := by
      unfold naturalSigmaRight
      exact (iInf_le _ (t + 1)).trans (iInf_le _ ht)
    _ ≤ (inferInstance : MeasurableSpace Ω) :=
      Kyprianou.Ch01.naturalSigma_le_ambient X hXmeas (t + 1)
