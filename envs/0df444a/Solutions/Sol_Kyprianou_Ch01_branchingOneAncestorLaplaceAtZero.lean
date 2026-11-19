-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOneAncestorLaplaceAtZero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:04:41.138667+00:00
-- url     : https://prove2.me/submissions/1bc831aa-1ac6-4535-aa65-85f63f03ae46

import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory
set_option autoImplicit false

theorem solution
    (law : PopulationLaws) (hinit : law 1 0 = PMF.pure 1) (q : ℝ) :
    branchingLaplace law 1 0 q = Real.exp (-q) := by
  unfold branchingLaplace
  rw [hinit]
  rw [tsum_eq_single 1]
  · simp
  · intro n hn; simp [PMF.pure_apply, hn]
