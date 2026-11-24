-- Prove2me | solution 1 for Kyprianou.Ch03.measurableLeftEvaluationOnCadlagV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:13:59.654156+00:00
-- url     : https://prove2.me/submissions/5156fa51-0d71-43c1-b5ff-b3ba806cb742

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    : ∃ L : NNReal → (NNReal → Real) → Real,
      (∀ u, Measurable (L u)) ∧
      ∀ (f : NNReal → Real), IsCadlag f → ∀ u, 0 < u →
        L u f = Function.leftLim f u := by
  classical
  have hseq (u : NNReal) (hu : 0 < u) :
      ∃ q : ℕ → NNReal, Tendsto q atTop (𝓝[<] u) := by
    letI : (𝓝[<] u).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hu⟩
    exact Filter.exists_seq_tendsto _
  let L (u : NNReal) (f : NNReal → ℝ) :=
    if hu : 0 < u then Filter.limsup (fun n => f ((hseq u hu).choose n)) atTop else f 0
  refine ⟨L, ?_, ?_⟩
  · intro u
    by_cases hu : 0 < u
    · simp only [L, dif_pos hu]
      exact Measurable.limsup fun n => measurable_pi_apply ((hseq u hu).choose n)
    · simpa only [L, dif_neg hu] using (measurable_pi_apply (0 : NNReal))
  · intro f hf u hu
    simp only [L, dif_pos hu]
    exact ((tendsto_leftLim_of_tendsto ((hf u).2)).comp
      (hseq u hu).choose_spec).limsup_eq
