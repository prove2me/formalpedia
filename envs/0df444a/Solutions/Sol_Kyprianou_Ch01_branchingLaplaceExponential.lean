-- Prove2me | solution 1 for Kyprianou.Ch01.branchingLaplaceExponential
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:20:57.574876+00:00
-- url     : https://prove2.me/submissions/870ba642-6fd6-4a04-a395-682cf2508f63

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_branchingLaplacePower
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 MeasureTheory Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hzero : ∀ t : ℝ≥0, law 0 t = PMF.pure 0)
    (hpositive : ∀ t : ℝ≥0, ∀ phi : ℝ, 0 < phi →
      0 < branchingLaplace law 1 t phi) :
    ∀ (y : ℕ) (t : ℝ≥0) (phi : ℝ), 0 < phi →
      branchingLaplace law y t phi =
        Real.exp (-(y : ℝ) * branchingU law t phi) := by
  intro y t phi hphi
  have hpow := Kyprianou.Ch01.branchingLaplacePower
    law hbranch hzero y t phi hphi
  have hpos := hpositive t phi hphi
  calc
    branchingLaplace law y t phi = (branchingLaplace law 1 t phi)^y := hpow
    _ = (Real.exp (Real.log (branchingLaplace law 1 t phi)))^y := by
      rw [Real.exp_log hpos]
    _ = Real.exp ((y : ℝ) * Real.log (branchingLaplace law 1 t phi)) := by
      rw [Real.exp_nat_mul]
    _ = Real.exp (-(y : ℝ) * branchingU law t phi) := by
      simp [branchingU]
