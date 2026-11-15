-- Prove2me | solution 1 for Kyprianou.Ch01.branchingU_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:39:40.511362+00:00
-- url     : https://prove2.me/submissions/4b8fa47f-8932-478d-af15-69ca97786230

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (law : PopulationLaws)
    (hinit : ∀ y : ℕ, law y 0 = PMF.pure y)
    (q : ℝ) :
    branchingU law 0 q = q := by
  have hL : branchingLaplace law 1 0 q = Real.exp (-q) := by
    unfold branchingLaplace
    simp only [hinit 1, PMF.pure_apply]
    rw [tsum_eq_single 1]
    · simp
    · intro n hn
      simp [hn]
  unfold branchingU
  rw [hL, Real.log_exp]
  ring
