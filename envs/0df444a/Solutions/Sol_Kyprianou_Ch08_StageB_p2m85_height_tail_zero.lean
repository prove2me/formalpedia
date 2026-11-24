-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_height_tail_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:30:42.26024+00:00
-- url     : https://prove2.me/submissions/04d89c68-51ca-4bce-82eb-5eeb1b4367c7

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

theorem solution
    (n : Measure ℝ) (hn : n (Ici (1 : ℝ)) < ⊤) :
    Tendsto (fun t : ℝ => (n (Ici t)).toReal) atTop (𝓝 0) := by
  have he : (⋂ t : ℝ, Ici t) = (∅ : Set ℝ) := by
    ext y
    simp only [mem_iInter, mem_Ici, mem_empty_iff_false, iff_false]
    intro h
    linarith [h (y+1)]
  have ht := tendsto_measure_iInter_atTop (μ := n)
    (s := fun t : ℝ => Ici t)
    (fun _ => measurableSet_Ici.nullMeasurableSet)
    (fun _ _ h => Ici_subset_Ici.mpr h) ⟨1, hn.ne⟩
  rw [he, measure_empty] at ht
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
