-- Prove2me | solution 1 for Kyprianou.Ch01.branchingLaplace_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:23:19.691223+00:00
-- url     : https://prove2.me/submissions/f82e8e0e-4827-4379-9150-9bee9dfa158e

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (law : PopulationLaws)
    (hzero : ∀ t : ℝ≥0, law 0 t = PMF.pure 0)
    (t : ℝ≥0) (phi : ℝ) :
    branchingLaplace law 0 t phi = 1 := by
  unfold branchingLaplace
  simp only [hzero t, PMF.pure_apply]
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]
