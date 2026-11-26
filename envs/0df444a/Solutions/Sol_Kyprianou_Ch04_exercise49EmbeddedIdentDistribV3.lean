-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49EmbeddedIdentDistribV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:50:10.720946+00:00
-- url     : https://prove2.me/submissions/43880b9a-55c8-41b0-b7b6-c2247fe868b3

import Mathlib.Probability.IdentDistrib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (j : Ω → E) (hj : MeasurableEmbedding j)
    (f g : E → ℝ) (h : IdentDistrib (f ∘ j) (g ∘ j) P P) :
    IdentDistrib f g (Measure.map j P) (Measure.map j P) := by
  have hf := hj.aemeasurable_map_iff.mpr h.aemeasurable_fst
  have hg := hj.aemeasurable_map_iff.mpr h.aemeasurable_snd
  exact ⟨hf,hg,by
    rw [hf.map_map_of_aemeasurable hj.measurable.aemeasurable,
      hg.map_map_of_aemeasurable hj.measurable.aemeasurable]
    exact h.map_eq⟩
