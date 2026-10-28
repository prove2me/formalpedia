-- Prove2me | solution 1 for MarkovProcess.sub_unitDyadicFloorValue_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:06:30.110217+00:00
-- url     : https://prove2.me/submissions/1cebfb5a-606e-4041-8d3b-e815bac23617

import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicFloor
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Dyadic floor approximation and the unit-interval continuous modification

This file merges the following former modules, one section each:

* `DyadicFloorApproximation`: Left dyadic approximations of unit-interval times
* `DyadicFloorPair`: Comparing two dyadic floor approximations
* `DyadicFloorSampleCauchy`: Cauchy control of dyadic floor samples
* `DyadicFloorDenseTime`: Dyadic floor samples at dyadic times
* `DyadicFloorSampleLimit`: Limits of dyadic floor samples
* `DyadicFloorLimitControl`: Uniform control of dyadic floor-sample limits
* `DyadicFloorLimitPath`: The canonical unit-interval dyadic-floor limit path
* `DyadicFloorConvergenceInMeasure`: Convergence in measure of dyadic floor samples
* `DyadicFloorUnitModification`: A continuous modification on the unit interval
-/




noncomputable section










theorem solution (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    t.1 - (unitDyadicFloorValue n t : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ := by
  have hupper := Nat.lt_floor_add_one ((2 ^ n : ℝ) * t.1)
  unfold unitDyadicFloorValue unitDyadicGrid
  simp only [unitDyadicFloorIndex_val]
  push_cast
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  apply le_of_lt
  rw [sub_lt_iff_lt_add, inv_eq_one_div]
  calc
    t.1 = ((2 : ℝ) ^ n * t.1) / (2 : ℝ) ^ n := by field_simp
    _ < (⌊(2 ^ n : ℝ) * t.1⌋₊ + 1) / (2 : ℝ) ^ n :=
      (div_lt_div_iff_of_pos_right hpow).2 hupper
    _ = 1 / (2 : ℝ) ^ n + (⌊(2 ^ n : ℝ) * t.1⌋₊ : ℝ) / (2 : ℝ) ^ n := by
      rw [add_div]
      ring
