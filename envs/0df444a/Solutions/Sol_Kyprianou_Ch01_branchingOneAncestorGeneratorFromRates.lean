-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOneAncestorGeneratorFromRates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T08:30:42.41768+00:00
-- url     : https://prove2.me/submissions/e73a4ee1-c309-4bcb-9ac6-234e99169d55

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorInfiniteDerivative
import Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorWeightedRateIdentity
import Mathlib.Probability.ProbabilityMassFunction.Monad
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (law : PopulationLaws) (rate : ℝ≥0) (offspring : PMF ℕ)
    (hrate : 0 < rate) (hNoNullJumps : offspring 1 = 0)
    (hinit : law 1 0 = PMF.pure 1)
    (hRates : IsBranchingRateGenerator law rate offspring) :
    ∀ q : ℝ, 0 < q →
      HasDerivWithinAt
        (fun t : ℝ => branchingLaplace law 1 (Real.toNNReal t) q)
        (-(branchingMechanism (rate : ℝ) offspring q) * Real.exp (-q))
        (Set.Ici 0) 0 := by
  intro q hq
  have hd := Kyprianou.Ch01.branchingOneAncestorInfiniteDerivative
    law rate offspring hrate hNoNullJumps hinit hRates q hq
  have hs := Kyprianou.Ch01.branchingOneAncestorWeightedRateIdentity
    rate offspring hNoNullJumps q hq
  rw [hs] at hd
  exact hd
