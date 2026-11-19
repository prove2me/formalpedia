-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOneAncestorExitMassDerivative
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:04:43.85903+00:00
-- url     : https://prove2.me/submissions/a172ca48-9025-4d78-bb9b-cdc920e5b11a

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory Set
set_option autoImplicit false

theorem solution
    (law : PopulationLaws) (rate : NNReal) (offspring : PMF ℕ)
    (hRates : IsBranchingRateGenerator law rate offspring) :
    HasDerivWithinAt
      (fun t : ℝ => 1 - ((law 1 (Real.toNNReal t)) 1).toReal)
      (rate : ℝ) (Set.Ici 0) 0 := by
  have h := (hRates 1 1).const_sub 1
  simpa using h
