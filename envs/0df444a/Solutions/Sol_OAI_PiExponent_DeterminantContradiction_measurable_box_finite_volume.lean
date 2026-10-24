-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.measurable_box_finite_volume
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T19:49:57.128281+00:00
-- url     : https://prove2.me/submissions/7f833fbe-3ecb-4511-b3da-4569a7fd6645

import Mathlib
open Filter Topology
open scoped BigOperators

theorem solution (m : Nat) (A : Real) (hA : 0 ≤ A) (s : Set (Fin (m + 1) → Real)) (hs : MeasurableSet s) (hbox : s ⊆ {x | ∀ i, x i ∈ Set.Icc (0 : Real) A}) : MeasureTheory.volume s ≠ ⊤ := by
  have hb : Bornology.IsBounded s := by
    apply (Metric.isBounded_Icc (0 : Fin (m + 1) → ℝ) (fun _ => A)).subset
    intro x hx
    exact ⟨fun i => (hbox hx i).1, fun i => (hbox hx i).2⟩
  exact hb.measure_lt_top.ne
