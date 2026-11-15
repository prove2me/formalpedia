-- Prove2me | solution 1 for Kyprianou.Ch01.branchingU_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:52:12.938802+00:00
-- url     : https://prove2.me/submissions/633e119b-70d2-4414-b288-5f59f0539539

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (law : PopulationLaws)
    (hpositive : ∀ t : ℝ≥0, ∀ q : ℝ, 0 < q →
      0 < branchingLaplace law 1 t q ∧
        branchingLaplace law 1 t q < 1)
    (t : ℝ≥0) (q : ℝ) (hq : 0 < q) :
    0 < branchingU law t q := by
  have hp := (hpositive t q hq).1
  have hlt := (hpositive t q hq).2
  have hlog : Real.log (branchingLaplace law 1 t q) < 0 := by
    have h := Real.log_lt_log hp hlt
    simpa using h
  unfold branchingU
  linarith
