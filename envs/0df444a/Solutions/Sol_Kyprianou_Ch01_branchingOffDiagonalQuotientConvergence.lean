-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOffDiagonalQuotientConvergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:21:14.070392+00:00
-- url     : https://prove2.me/submissions/2bece90e-926a-48a0-b2dc-48db8d30904d

import Mathlib.Analysis.Calculus.Deriv.Slope
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_branchingOffDiagonalPointwiseSlope
import Theorems.Thm_Kyprianou_Ch01_branchingOffDiagonalTotalSlopeWithInit
import Mathlib.Probability.ProbabilityMassFunction.Monad
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
set_option autoImplicit false

/-- Derive both quotient limits by proved pointwise and total-mass results. -/
theorem solution
    (law : PopulationLaws) (rate : NNReal) (offspring : PMF ℕ)
    (hinit : law 1 0 = PMF.pure 1)
    (hRates : IsBranchingRateGenerator law rate offspring) :
    (∀ k : ℕ, Tendsto
      (fun t : ℝ =>
        (if k = 1 then (0 : ℝ)
         else ((law 1 (Real.toNNReal t)) k).toReal) / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (if k = 1 then (0 : ℝ)
          else (rate : ℝ) * (offspring k).toReal))) ∧
    Tendsto (fun t : ℝ =>
      ∑' k : ℕ, (if k = 1 then (0 : ℝ)
         else ((law 1 (Real.toNNReal t)) k).toReal) / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (rate : ℝ)) := by
  exact ⟨Kyprianou.Ch01.branchingOffDiagonalPointwiseSlope
    law rate offspring hinit hRates,
    Kyprianou.Ch01.branchingOffDiagonalTotalSlopeWithInit
      law rate offspring hinit hRates⟩
