-- Prove2me | solution 1 for Kyprianou.Ch01.branchingFiniteLaplaceGenerator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T07:43:44.944386+00:00
-- url     : https://prove2.me/submissions/03ac29fd-da82-4c69-9465-f949143ae54c

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (law : PopulationLaws) (rate : ℝ≥0) (offspring : PMF ℕ)
    (hRates : IsBranchingRateGenerator law rate offspring)
    (N : ℕ) (q : ℝ) :
    HasDerivWithinAt
      (fun t : ℝ => ∑ k ∈ Finset.range N,
        ((law 1 (Real.toNNReal t)) k).toReal *
          Real.exp (-q * (k : ℝ)))
      (∑ k ∈ Finset.range N,
        (if k = 1 then -((rate : ℝ) * (1 : ℝ))
        else if 1 ≤ k + 1 then
          (rate : ℝ) * (1 : ℝ) * (offspring (k + 1 - 1)).toReal
        else 0) * Real.exp (-q * (k : ℝ)))
      (Set.Ici 0) 0 := by
  apply HasDerivWithinAt.fun_sum
  intro k hk
  simpa only [Nat.cast_one, mul_one, Nat.add_sub_cancel_left] using
    (hRates 1 k).mul_const (Real.exp (-q * (k : ℝ)))
