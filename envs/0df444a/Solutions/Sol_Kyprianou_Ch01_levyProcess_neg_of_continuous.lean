-- Prove2me | solution 1 for Kyprianou.Ch01.levyProcess_neg_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T20:55:29.41645+00:00
-- url     : https://prove2.me/submissions/0de46006-499e-4d92-908c-e1f66fcf47f9

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Continuous_isCadlag
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Negation preserves the four defining Lévy properties for continuous paths. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X t ω)) :
    ProbabilityTheory.IsLevyProcess (fun t ω => -X t ω) P := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext ω
    simp [hX.start_zero]
  · intro n t ht
    have h := hX.indep_increments n t ht
    have hh := h.comp (fun _ => fun z : ℝ => -z)
      (fun _ => measurable_neg)
    change iIndepFun (fun k : Fin n => fun ω =>
      (-X (t k.succ) ω) - (-X (t k.castSucc) ω)) P
    convert hh using 1 <;> (funext k ω; simp [increment]; ring)
  · intro s h
    have hd := (hX.stationary_increments s h).comp measurable_neg
    change IdentDistrib
      (fun ω => -(X (s + h) ω - X s ω))
      (fun ω => -(X h ω - X 0 ω)) P P at hd
    convert hd using 1 <;> (funext ω; simp [increment]; ring)
  · filter_upwards [hcont] with ω hc
    exact hc.neg.isCadlag
