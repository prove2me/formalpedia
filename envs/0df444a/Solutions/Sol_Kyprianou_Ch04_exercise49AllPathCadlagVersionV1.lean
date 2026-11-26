-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49AllPathCadlagVersionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:55:52.326851+00:00
-- url     : https://prove2.me/submissions/dab10470-e0f4-45a7-84e0-cf5afc7ec526

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_levyCommonMeasurableVersionV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyIsLevyProcessOfAEEqV1
import Theorems.Thm_ProbabilityTheory_isCadlag_const
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- A measurable all-path cadlag Levy version with indistinguishable paths. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P) :
    ∃ Y : NNReal → Ω → ℝ, IsLevyProcess Y P ∧
      (∀ t, Measurable (Y t)) ∧ (∀ ω, IsCadlag (fun t => Y t ω)) ∧
      (∀ᵐ ω ∂P, ∀ t, Y t ω = X t ω) := by
  classical
  obtain ⟨Z, hZ, hm, he⟩ := Kyprianou.Ch03.levyCommonMeasurableVersionV1 P X hX
  let B : Set Ω := {ω | ¬ IsCadlag (fun t => Z t ω)}
  have hb : P B = 0 := (ae_iff).mp hZ.cadlag_ae
  obtain ⟨N, hBN, hNm, hN0⟩ := exists_measurable_superset_of_null hb
  let Y : NNReal → Ω → ℝ := fun t ω => if ω ∈ N then 0 else Z t ω
  have hg : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hN0
  have hYeq : ∀ᵐ ω ∂P, ∀ t, Z t ω = Y t ω := by
    filter_upwards [hg] with ω hw
    intro t
    simp [Y, hw]
  have hY0 : Y 0 = fun _ => 0 := by
    funext ω
    simp [Y, congrFun hZ.start_zero ω]
  refine ⟨Y, Kyprianou.Ch02.bvLevyIsLevyProcessOfAEEqV1 P Z Y hZ hY0 hYeq,
    fun t => Measurable.ite hNm measurable_const (hm t), ?_, ?_⟩
  · intro ω
    by_cases hw : ω ∈ N
    · intro t
      simpa [Y, hw] using (ProbabilityTheory.isCadlag_const (c := (0 : ℝ)) t)
    · have hcad : IsCadlag (fun t => Z t ω) := by
        by_contra h
        exact hw (hBN h)
      simpa [Y, hw] using hcad
  · filter_upwards [hg, he] with ω hw hEq
    intro t
    simp [Y, hw, hEq]
