-- Prove2me | solution 1 for Kyprianou.Ch01.oneAncestorDiagonalSupermultiplicative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:05:26.349163+00:00
-- url     : https://prove2.me/submissions/6664a5b7-7ea1-4fdf-8140-68f8c6b88bfc

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (law : PopulationLaws)
    (hSemi : IsPopulationMarkovSemigroup law)
    (s t : ℝ≥0) :
    (law 1 s 1) * (law 1 t 1) ≤ law 1 (s + t) 1 := by
  have h := congrArg (fun p : PMF ℕ => p 1) (hSemi 1 s t)
  rw [PMF.bind_apply] at h
  calc
    (law 1 s 1) * (law 1 t 1) ≤
        ∑' n : ℕ, (law 1 s n) * (law n t 1) := by
      exact ENNReal.le_tsum 1
    _ = law 1 (s + t) 1 := h.symm
