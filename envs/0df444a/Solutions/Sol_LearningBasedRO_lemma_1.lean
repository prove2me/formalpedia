-- Prove2me | solution 1 for LearningBasedRO.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:13:57.179777+00:00
-- url     : https://prove2.me/submissions/aa60dacf-033c-4477-9991-892d5a622a4a

import Mathlib
import Definitions.Def_LearningBasedRO_Model

open MeasureTheory

open LearningBasedRO in
theorem solution {X E Ω : Type*} [MeasurableSpace E] (P : Measure E) (g : X → E → Ω)
    (A : Set Ω) (ϵ : ℝ) (U : Set E) (hU : IsContentSet P ϵ U) (x : X)
    (hx : ROFeasible g A U x) : CCPFeasible P g A ϵ x :=
  le_trans hU (measure_mono fun ξ hξ => hx ξ hξ)
