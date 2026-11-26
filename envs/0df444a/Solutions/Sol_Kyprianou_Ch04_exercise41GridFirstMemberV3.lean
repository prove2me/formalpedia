-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41GridFirstMemberV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:39:41.922482+00:00
-- url     : https://prove2.me/submissions/a5fe9f2b-3947-4037-8bb2-de7adfc050be

import Mathlib
import Definitions.Def_Kyprianou_Ch04_exercise41GridFirstV2
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
open Kyprianou.Ch04

theorem solution
    {Ω : Type} (D : Finset NNReal) (C : NNReal → Set Ω)
    (b : NNReal) (ω : Ω) (hA : ∃ t ∈ D, ω ∈ C t) :
    exercise41GridFirstV2 D C b ω ∈ D ∧
      ω ∈ C (exercise41GridFirstV2 D C b ω) := by
  classical
  let H := D.filter (fun t => ω ∈ C t)
  obtain ⟨t, ht, hc⟩ := hA
  have h : H.Nonempty := ⟨t, Finset.mem_filter.mpr ⟨ht, hc⟩⟩
  have hm := Finset.mem_filter.mp (Finset.min'_mem H h)
  simpa only [exercise41GridFirstV2, H, dif_pos h] using hm
