-- Prove2me | solution 1 for Kyprianou.Ch01.zeroBoundaryPassageClockMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T15:23:06.813912+00:00
-- url     : https://prove2.me/submissions/55f752d7-18ee-44ed-abaf-97e775d4d7b8

import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageMeasurableOfContinuousPublic
open MeasureTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ≥0) :
    Measurable
      (fun ω =>
        if s = 0 then (0 : ℝ)
        else (match firstUpperPassage X (s : ℝ) ω with
        | none => (0 : ℝ)
        | some t => (t : ℝ))) := by
  by_cases hs : s = 0
  · simpa [hs] using (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))
  · simp only [if_neg hs]
    have hPass : Measurable (firstUpperPassage X (s : ℝ)) :=
      firstUpperPassageMeasurableOfContinuousPublic X hMeas hContinuous (s : ℝ)
    have hUn : Measurable (fun ω => WithTop.untopD (0 : ℝ≥0) (firstUpperPassage X (s : ℝ) ω)) :=
      hPass.untopD (0 : ℝ≥0)
    have hReal : Measurable (fun ω =>
        ((WithTop.untopD (0 : ℝ≥0) (firstUpperPassage X (s : ℝ) ω) : ℝ≥0) : ℝ)) :=
      hUn.coe_nnreal_real
    have hEq :
        (fun ω : Ω =>
          ((WithTop.untopD (0 : ℝ≥0) (firstUpperPassage X (s : ℝ) ω) : ℝ≥0) : ℝ)) =
        (fun ω : Ω =>
          match firstUpperPassage X (s : ℝ) ω with
          | none => (0 : ℝ)
          | some t => (t : ℝ)) := by
      funext ω
      cases hT : firstUpperPassage X (s : ℝ) ω with
      | top => rfl
      | coe t => rfl
    rw [← hEq]
    exact hReal
