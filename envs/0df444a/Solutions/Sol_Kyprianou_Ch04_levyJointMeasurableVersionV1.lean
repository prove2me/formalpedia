-- Prove2me | solution 1 for Kyprianou.Ch04.levyJointMeasurableVersionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:37:39.303313+00:00
-- url     : https://prove2.me/submissions/46171414-fbff-43c3-8eda-fc77f8d50e6f

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Jointly measurable version of a Levy process, agreeing at all times almost surely. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P) :
    ∃ Z : ℝ≥0 → Ω → ℝ,
      Measurable (fun z : ℝ≥0 × Ω => Z z.1 z.2) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Z t ω = X t ω) := by
  classical
  have hA := Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 P X hX
  let A := hA.mk (fun ω : Ω => fun t : ℝ≥0 => X t ω)
  let B : Set Ω := {ω | ¬ (IsCadlag (fun t => X t ω) ∧
    (fun t => X t ω) = A ω)}
  have hb : P B = 0 := (ae_iff).mp (hX.cadlag_ae.and hA.ae_eq_mk)
  obtain ⟨N, hBN, hNm, hN0⟩ := exists_measurable_superset_of_null hb
  let G := Nᶜ
  have hG : ∀ ω ∈ G, IsCadlag (fun t => X t ω) ∧ (fun t => X t ω) = A ω := by
    intro ω hω
    by_contra h
    exact hω (hBN h)
  let Z : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ G then A ω t else 0
  have hZm (t : ℝ≥0) : Measurable (Z t) :=
    Measurable.ite hNm.compl ((measurable_pi_apply t).comp hA.measurable_mk) measurable_const
  have hZr (ω : Ω) (t : ℝ≥0) :
      ContinuousWithinAt (fun s : ℝ≥0 => Z s ω) (Ici t) t := by
    by_cases hω : ω ∈ G
    · have he : (fun s => Z s ω) = (fun s => X s ω) := by
        funext s
        simp [Z, hω, congrFun (hG ω hω).2 s]
      rw [he]
      exact ((hG ω hω).1 t).1
    · have he : (fun s => Z s ω) = fun _ : ℝ≥0 => (0 : ℝ) := by
        funext s
        simp [Z, hω]
      rw [he]
      exact continuousWithinAt_const
  refine ⟨Z, AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation Z hZm hZr, ?_⟩
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    simpa [G] using hN0
  filter_upwards [hGae] with ω hω
  intro t
  simpa [Z, hω] using (congrFun (hG ω hω).2 t).symm
