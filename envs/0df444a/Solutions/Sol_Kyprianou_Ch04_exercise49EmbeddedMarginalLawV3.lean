-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49EmbeddedMarginalLawV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:55:08.963533+00:00
-- url     : https://prove2.me/submissions/2a72d042-b868-447c-8861-6a546d066dd9

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (j : Ω → E) (hj : MeasurableEmbedding j)
    (X : NNReal → Ω → ℝ) (Y : NNReal → E → ℝ)
    (hX : IsLevyProcess X P)
    (hAgree : ∀ t w, Y t (j w) = X t w) (t : NNReal) :
    Measure.map (Y t) (Measure.map j P) = Measure.map (X t) P := by
  have hA : AEMeasurable (X t) P := by
    have H := (hX.stationary_increments 0 t).aemeasurable_snd
    have he : ProbabilityTheory.increment X 0 t = X t := by
      funext w
      unfold ProbabilityTheory.increment
      rw [hX.start_zero]
      exact sub_zero _
    rwa [he] at H
  have hE : Y t ∘ j = X t := funext (hAgree t)
  have hY : AEMeasurable (Y t) (Measure.map j P) :=
    hj.aemeasurable_map_iff.mpr (hE.symm ▸ hA)
  rw [hY.map_map_of_aemeasurable hj.measurable.aemeasurable,hE]
