-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOffDiagonalQuotientSummablePositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:14:57.751232+00:00
-- url     : https://prove2.me/submissions/e5d8d8a6-8806-4345-8202-75713ccd0eb2

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (law : PopulationLaws) (t : ℝ) (ht : 0 < t) :
    (∀ k : ℕ, 0 ≤
      (if k = 1 then (0 : ℝ)
       else ((law 1 (Real.toNNReal t)) k).toReal) / t) ∧
    Summable (fun k : ℕ =>
      (if k = 1 then (0 : ℝ)
       else ((law 1 (Real.toNNReal t)) k).toReal) / t) := by
  have hsum : Summable (fun k : ℕ =>
      ((law 1 (Real.toNNReal t)) k).toReal) :=
    ENNReal.summable_toReal
      ((law 1 (Real.toNNReal t)).tsum_coe_ne_top)
  have hmask : Summable (fun k : ℕ =>
      if k = 1 then (0 : ℝ)
      else ((law 1 (Real.toNNReal t)) k).toReal) :=
    Summable.of_nonneg_of_le
      (fun k => by split_ifs <;> positivity)
      (fun k => by split_ifs <;> simp)
      hsum
  constructor
  · intro k
    apply div_nonneg
    · split_ifs <;> positivity
    · exact ht.le
  · simpa only [div_eq_mul_inv] using hmask.mul_right t⁻¹
