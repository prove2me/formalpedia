-- Prove2me | solution 1 for LearningBasedRO.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:56:09.17478+00:00
-- url     : https://prove2.me/submissions/c692e140-ef19-4212-bfa0-8c2510b06bde

import Mathlib
import Definitions.Def_LearningBasedRO_Model

open MeasureTheory

open LearningBasedRO in
theorem solution {X E Ω ΩD : Type*} [MeasurableSpace E] [MeasurableSpace ΩD]
    (P : Measure E) (μD : Measure ΩD) (g : X → E → Ω) (A : Set Ω) (ϵ δ : ℝ)
    (U : ΩD → Set E) (hU : SatisfiesReq3 μD P ϵ δ U) :
    ENNReal.ofReal (1 - δ) ≤
      μD {D | ∀ x : X, ROFeasible g A (U D) x → CCPFeasible P g A ϵ x} := by
  refine le_trans hU (measure_mono ?_)
  intro D hD x hx
  unfold IsContentSet at hD
  unfold CCPFeasible
  refine le_trans hD (measure_mono ?_)
  intro ξ hξ
  exact hx ξ hξ
