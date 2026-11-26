-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49EmbeddedAsymptoticsV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:53:12.354294+00:00
-- url     : https://prove2.me/submissions/9aa96012-9bd4-458f-b4d0-a676ffcbd066

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (j : Ω → E) (hj : MeasurableEmbedding j)
    (X : NNReal → Ω → ℝ) (Y : NNReal → E → ℝ)
    (hAgree : ∀ t w, Y t (j w) = X t w)
    (hNotSub : ¬ (∀ᵐ w ∂P, Monotone (fun t : NNReal => X t w)))
    (hInfinity : ∀ᵐ w ∂P, Tendsto (fun t : NNReal => X t w) atTop atTop) :
    (¬ (∀ᵐ w ∂Measure.map j P, Monotone (fun t : NNReal => Y t w))) ∧
    (∀ᵐ w ∂Measure.map j P, Tendsto (fun t : NNReal => Y t w) atTop atTop) := by
  refine ⟨?_,?_⟩
  · intro h
    apply hNotSub
    filter_upwards [hj.ae_map_iff.mp h] with w hw
    simpa only [hAgree] using hw
  · apply hj.ae_map_iff.mpr
    filter_upwards [hInfinity] with w hw
    simpa only [hAgree] using hw
