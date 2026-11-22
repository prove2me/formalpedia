-- Prove2me | solution 1 for Kyprianou.Ch01.rightNaturalStoppingTime_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:09:29.162642+00:00
-- url     : https://prove2.me/submissions/5099ebc8-bd19-4c70-8b29-758be1a3a725

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_monotone
import Theorems.Thm_Kyprianou_Ch01_naturalSigmaRight_le_ambient

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (tau : Ω → WithTop ℝ≥0)
    (hTau : IsNaturalRightStoppingTime X tau) :
    Measurable tau := by
  let 𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) := {
    seq := naturalSigmaRight X
    mono' := by
      intro s t hst
      exact Kyprianou.Ch01.naturalSigmaRight_monotone X hst
    le' := by
      intro t
      exact Kyprianou.Ch01.naturalSigmaRight_le_ambient X hXmeas t
  }
  have hs : IsStoppingTime 𝓕 tau := by
    intro t
    exact hTau t
  exact hs.measurable'
