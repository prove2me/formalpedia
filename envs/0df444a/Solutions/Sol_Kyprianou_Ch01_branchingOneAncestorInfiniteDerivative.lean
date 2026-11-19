-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOneAncestorInfiniteDerivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:22:15.266345+00:00
-- url     : https://prove2.me/submissions/c874f3c4-3285-4436-b83c-a5fa72f5c35e

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Tactic.Ring
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorWeightedOffDiagonalDerivativeNoNull
import Theorems.Thm_Kyprianou_Ch01_branchingLaplaceDiagonalOffDiagonal
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorWeightedRateIdentity
import Theorems.Thm_Kyprianou_Ch01_branchingOffspringMechanismMoment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Reduce the full series derivative to its positive off-diagonal limit. -/
theorem solution
    (law : PopulationLaws) (rate : NNReal) (offspring : PMF ℕ)
    (hrate : 0 < rate) (hNoNullJumps : offspring 1 = 0)
    (hinit : law 1 0 = PMF.pure 1)
    (hRates : IsBranchingRateGenerator law rate offspring)
    (q : ℝ) (hq : 0 < q) :
    HasDerivWithinAt
      (fun t : ℝ => branchingLaplace law 1 (Real.toNNReal t) q)
      (∑' k : ℕ,
        (if k = 1 then -(rate : ℝ)
         else (rate : ℝ) * (offspring k).toReal) *
        Real.exp (-q * (k : ℝ)))
      (Set.Ici 0) 0 := by
  have hd : HasDerivWithinAt
      (fun t : ℝ => ((law 1 (Real.toNNReal t)) 1).toReal)
      (-(rate : ℝ)) (Set.Ici 0) 0 := by
    simpa [IsBranchingRateGenerator] using hRates 1 1
  have hw := Kyprianou.Ch01.branchingOneAncestorWeightedOffDiagonalDerivativeNoNull
    law rate offspring hNoNullJumps hinit hRates q hq
  have hsum := (hd.mul_const (Real.exp (-q))).add hw
  have hFn :
      (fun t : ℝ => branchingLaplace law 1 (Real.toNNReal t) q) =
      (fun t : ℝ =>
        ((law 1 (Real.toNNReal t)) 1).toReal * Real.exp (-q) +
        (∑' k : ℕ, if k = 1 then (0 : ℝ)
          else ((law 1 (Real.toNNReal t)) k).toReal *
            Real.exp (-q * (k : ℝ)))) := by
    funext t
    exact Kyprianou.Ch01.branchingLaplaceDiagonalOffDiagonal
      law q hq (Real.toNNReal t)
  have hmoment := Kyprianou.Ch01.branchingOffspringMechanismMoment
    offspring q hq
  have hrateid := Kyprianou.Ch01.branchingOneAncestorWeightedRateIdentity
    rate offspring hNoNullJumps q hq
  have hExp : Real.exp q * Real.exp (-q) = 1 := by
    rw [← Real.exp_add]
    simp
  have hvalue :
      (-(rate : ℝ)) * Real.exp (-q) +
        (rate : ℝ) * (∑' k : ℕ,
          (offspring k).toReal * Real.exp (-q * (k : ℝ))) =
      (∑' k : ℕ,
        (if k = 1 then -(rate : ℝ)
         else (rate : ℝ) * (offspring k).toReal) *
        Real.exp (-q * (k : ℝ))) := by
    rw [hrateid]
    unfold branchingMechanism
    rw [hmoment]
    calc
      (-(rate : ℝ)) * Real.exp (-q) +
        (rate : ℝ) * (∑' k : ℕ,
          (offspring k).toReal * Real.exp (-q * (k : ℝ))) =
        (-(rate : ℝ)) * Real.exp (-q) +
          (rate : ℝ) * (Real.exp q * Real.exp (-q)) *
            (∑' k : ℕ,
              (offspring k).toReal * Real.exp (-q * (k : ℝ))) := by
            rw [hExp]
            ring
      _ = -((rate : ℝ) *
        (1 - Real.exp q *
          (∑' k : ℕ,
            (offspring k).toReal * Real.exp (-q * (k : ℝ))))) *
          Real.exp (-q) := by ring
  rw [hFn, ← hvalue]
  exact hsum
