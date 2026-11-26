-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41LiminfTopV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:32:38.971696+00:00
-- url     : https://prove2.me/submissions/699f81ce-d45d-4ea2-a0e5-bf5dfc97dac3

import Mathlib

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false


theorem solution (N : ℕ → ℝ≥0∞)
    (hN : ∀ k : ℕ, ∃ m : ℕ, ∀ n ≥ m, (k : ℝ≥0∞) ≤ N n) :
    Filter.liminf N atTop = ⊤ := by
  apply top_unique
  rw [← ENNReal.iSup_natCast, Filter.liminf_eq_iSup_iInf_of_nat]
  refine iSup_le fun k => ?_
  obtain ⟨m, hm⟩ := hN k
  exact (le_iInf fun n => le_iInf fun hn => hm n hn).trans
    (le_iSup (fun j : ℕ => ⨅ i ≥ j, N i) m)
