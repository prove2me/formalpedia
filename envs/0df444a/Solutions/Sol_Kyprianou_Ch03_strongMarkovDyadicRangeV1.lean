-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovDyadicRangeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:58:24.759886+00:00
-- url     : https://prove2.me/submissions/916cd439-8a51-48c9-aae3-0b8fb276dbd0

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} (tau : Omega → WithTop NNReal) (finiteTime : Omega → NNReal)
    (n : ℕ) :
    Countable (Set.range (fun w : Omega => if tau w = ⊤ then (0 : NNReal) else
      (Nat.ceil ((finiteTime w : ℝ) * (2 : ℝ)^n) : NNReal) / (2 : NNReal)^n)) := by
  classical
  let g : ℕ → NNReal := fun k => (k : NNReal) / (2 : NNReal)^n
  apply (Set.countable_range g).mono
  rintro s ⟨w, rfl⟩
  by_cases hw : tau w = ⊤
  · exact ⟨0, by simp [g, hw]⟩
  · exact ⟨Nat.ceil ((finiteTime w : ℝ) * (2 : ℝ)^n), by simp [g, hw]⟩
