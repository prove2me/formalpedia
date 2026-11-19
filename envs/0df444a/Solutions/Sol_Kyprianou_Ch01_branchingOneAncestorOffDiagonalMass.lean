-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOneAncestorOffDiagonalMass
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:04:40.257205+00:00
-- url     : https://prove2.me/submissions/6d4bc2f0-3c58-4ea8-8ecd-d0e904056f4e

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory
set_option autoImplicit false

theorem solution
    (law : PopulationLaws) (t : NNReal) :
    (∑' k : ℕ,
      if k = 1 then (0 : ℝ) else ((law 1 t) k).toReal) =
      1 - ((law 1 t) 1).toReal := by
  set p := law 1 t
  have hs : Summable (fun k => (p k).toReal) :=
    ENNReal.summable_toReal (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top)
  have h1 : ∑' k, (p k).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun k => PMF.apply_ne_top p k), PMF.tsum_coe]; simp
  rw [hs.tsum_eq_add_tsum_ite 1] at h1
  linarith
