-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_levy_joint_version
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:35:55.619999+00:00
-- url     : https://prove2.me/submissions/36e86fbc-fc8a-4aa1-b532-564caf6ccb57

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- An a.s. cadlag Levy process has a jointly measurable, everywhere right-continuous version
indistinguishable from the original process. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P) :
    ∃ Y : NNReal → Ω → ℝ, Measurable (fun z : NNReal × Ω => Y z.1 z.2) ∧
      (∀ᵐ w ∂P, ∀ t, Y t w = X t w) ∧ ∀ w, IsCadlag (fun t => Y t w) := by
  classical
  have hp := Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 P X hX
  let Z := hp.mk (fun w => fun t => X t w)
  let B : Set Ω := {w | ¬ (Z w = (fun t => X t w) ∧ IsCadlag (fun t => X t w))}
  have hgood : ∀ᵐ w ∂P, Z w = (fun t => X t w) ∧ IsCadlag (fun t => X t w) :=
    hp.ae_eq_mk.symm.and hX.cadlag_ae
  obtain ⟨N,hBN,hNm,hN0⟩ := exists_measurable_superset_of_null (μ := P)
    (show P B = 0 from ae_iff.mp hgood)
  let Y : NNReal → Ω → ℝ := fun t w => if w ∈ N then 0 else Z w t
  have hY (w : Ω) (hw : w ∉ N) : Z w = (fun t => X t w) ∧
      IsCadlag (fun t => X t w) := by
    by_contra hbad
    exact hw (hBN hbad)
  have hcad (w : Ω) : IsCadlag (fun t => Y t w) := by
    by_cases hw : w ∈ N
    · simp only [Y,if_pos hw]
      intro t
      exact ⟨continuousWithinAt_const, ⟨0,tendsto_const_nhds⟩⟩
    · simpa only [Y,if_neg hw,(hY w hw).1] using (hY w hw).2
  refine ⟨Y, ?_, ?_, hcad⟩
  · apply AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
    · intro t
      exact measurable_const.piecewise hNm ((measurable_pi_apply t).comp hp.measurable_mk)
    · exact fun w t => (hcad w t).1
  · have hN : ∀ᵐ w ∂P, w ∉ N := ae_iff.mpr (by simpa using hN0)
    filter_upwards [hN] with w hw
    intro t
    simp only [Y,if_neg hw,(hY w hw).1]
