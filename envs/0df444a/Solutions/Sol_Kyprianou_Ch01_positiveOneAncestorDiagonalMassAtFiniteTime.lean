-- Prove2me | solution 1 for Kyprianou.Ch01.positiveOneAncestorDiagonalMassAtFiniteTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:57:56.993635+00:00
-- url     : https://prove2.me/submissions/e0610a62-c3f9-4868-896e-8048c167c965

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_oneAncestorDiagonalPositiveNearZero
import Theorems.Thm_Kyprianou_Ch01_oneAncestorDiagonalPositiveFromNearZero
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (rate : ℝ≥0) (hrate : 0 < rate) (offspring : PMF ℕ)
    (K : PopulationLaws)
    (hSemi : IsPopulationMarkovSemigroup K)
    (hInit : ∀ y : ℕ, K y 0 = PMF.pure y)
    (hGen : IsBranchingRateGenerator K rate offspring) :
    ∀ t : ℝ≥0, 0 < ((K 1 t) 1).toReal := by
  obtain ⟨δ, hδ, hNear⟩ :=
    Kyprianou.Ch01.oneAncestorDiagonalPositiveNearZero
      rate offspring K (hInit 1) hGen
  exact Kyprianou.Ch01.oneAncestorDiagonalPositiveFromNearZero
    K hSemi (hInit 1) δ hδ hNear
