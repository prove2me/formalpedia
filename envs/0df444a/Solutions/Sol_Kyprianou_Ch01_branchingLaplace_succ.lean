-- Prove2me | solution 1 for Kyprianou.Ch01.branchingLaplace_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:21:44.148552+00:00
-- url     : https://prove2.me/submissions/86fa27b3-e592-4181-b74f-6cb4f63b3919

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_pmfLaplaceConvolution
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (y : ℕ) (t : ℝ≥0) (phi : ℝ) (hphi : 0 < phi) :
    branchingLaplace law (y + 1) t phi =
      branchingLaplace law y t phi *
        branchingLaplace law 1 t phi := by
  unfold branchingLaplace
  rw [hbranch y 1 t]
  exact Kyprianou.Ch01.pmfLaplaceConvolution
    (law y t) (law 1 t) phi hphi
