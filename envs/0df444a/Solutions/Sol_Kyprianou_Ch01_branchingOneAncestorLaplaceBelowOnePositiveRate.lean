-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOneAncestorLaplaceBelowOnePositiveRate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:00:25.667247+00:00
-- url     : https://prove2.me/submissions/2ef99e0a-304b-4e08-8cde-f3832077bfe9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_pmfLaplaceStrictBelowOneOfPositiveOneAtom
import Theorems.Thm_Kyprianou_Ch01_positiveOneAncestorDiagonalMassAtFiniteTime
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (rate : ℝ≥0) (hrate : 0 < rate) (offspring : PMF ℕ)
    (K : PopulationLaws)
    (hSemi : IsPopulationMarkovSemigroup K)
    (hInit : ∀ y : ℕ, K y 0 = PMF.pure y)
    (hGen : IsBranchingRateGenerator K rate offspring) :
    ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
      branchingLaplace K 1 t q < 1 := by
  intro t q hq
  have hmass :=
    Kyprianou.Ch01.positiveOneAncestorDiagonalMassAtFiniteTime
      rate hrate offspring K hSemi hInit hGen t
  exact Kyprianou.Ch01.pmfLaplaceStrictBelowOneOfPositiveOneAtom
    (K 1 t) q hq hmass
