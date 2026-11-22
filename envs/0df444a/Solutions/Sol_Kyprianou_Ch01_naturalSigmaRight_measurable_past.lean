-- Prove2me | solution 1 for Kyprianou.Ch01.naturalSigmaRight_measurable_past
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:04:43.945512+00:00
-- url     : https://prove2.me/submissions/8ca75c71-285a-4e9c-adca-1cf0a6cf889d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_le_naturalSigmaRight
import Theorems.Thm_Kyprianou_Ch01_naturalSigma_measurable_past

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (u t : ℝ≥0) (hut : u ≤ t) :
    @Measurable Ω ℝ (naturalSigmaRight X t) inferInstance (X u) := by
  exact (Kyprianou.Ch01.naturalSigma_measurable_past X u t hut).mono
    (Kyprianou.Ch01.naturalSigma_le_naturalSigmaRight X t) le_rfl
