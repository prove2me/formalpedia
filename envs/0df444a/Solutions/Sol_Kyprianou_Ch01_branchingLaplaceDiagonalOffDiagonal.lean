-- Prove2me | solution 1 for Kyprianou.Ch01.branchingLaplaceDiagonalOffDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T09:56:32.998847+00:00
-- url     : https://prove2.me/submissions/d2e3ef1f-2c31-44ff-b132-b1bf617a9fb2

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Tactic.Linarith
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Split the exact source Laplace series at the one-ancestor diagonal. -/
theorem solution
    (law : PopulationLaws) (q : ℝ) (hq : 0 < q) (t : NNReal) :
    branchingLaplace law 1 t q =
      ((law 1 t) 1).toReal * Real.exp (-q) +
      (∑' k : ℕ, if k = 1 then (0 : ℝ)
        else ((law 1 t) k).toReal * Real.exp (-q * (k : ℝ))) := by
  let p : PMF ℕ := law 1 t
  have hbase : Summable (fun k : ℕ => (p k).toReal) :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hw (k : ℕ) :
      Real.exp (-q * (k : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [mul_nonneg hq.le hk]
  have hsum : Summable (fun k : ℕ =>
      (p k).toReal * Real.exp (-q * (k : ℝ))) := by
    apply Summable.of_nonneg_of_le
    · intro k
      exact mul_nonneg ENNReal.toReal_nonneg (Real.exp_nonneg _)
    · intro k
      calc
        (p k).toReal * Real.exp (-q * (k : ℝ)) ≤
            (p k).toReal * 1 :=
          mul_le_mul_of_nonneg_left (hw k) ENNReal.toReal_nonneg
        _ = (p k).toReal := mul_one _
    · exact hbase
  change (∑' k : ℕ, (p k).toReal * Real.exp (-q * (k : ℝ))) = _
  have hsplit := hsum.tsum_eq_add_tsum_ite 1
  simpa only [ite_self, mul_one, Nat.cast_one, mul_one] using hsplit
