-- Prove2me | solution 1 for Kyprianou.Ch01.branchingLaplacePower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:39:37.655732+00:00
-- url     : https://prove2.me/submissions/89bab079-3bdd-4164-b3c5-e4dc778379ee

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingLaplace_zero
import Theorems.Thm_Kyprianou_Ch01_branchingLaplace_succ
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hzero : ∀ t : ℝ≥0, law 0 t = PMF.pure 0) :
    ∀ (y : ℕ) (t : ℝ≥0) (phi : ℝ), 0 < phi →
      branchingLaplace law y t phi =
        (branchingLaplace law 1 t phi) ^ y := by
  intro y t phi hphi
  induction y with
  | zero =>
      simpa using Kyprianou.Ch01.branchingLaplace_zero law hzero t phi
  | succ n ih =>
      rw [Kyprianou.Ch01.branchingLaplace_succ law hbranch n t phi hphi,
        ih, pow_succ]
