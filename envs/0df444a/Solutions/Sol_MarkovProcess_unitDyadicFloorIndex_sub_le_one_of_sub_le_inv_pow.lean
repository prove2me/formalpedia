-- Prove2me | solution 1 for MarkovProcess.unitDyadicFloorIndex_sub_le_one_of_sub_le_inv_pow
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:07:54.651994+00:00
-- url     : https://prove2.me/submissions/ea02c997-6094-4899-8fb5-9430694bb72d

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


















open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


noncomputable section




theorem solution
    (n : ℕ) {s t : Set.Icc (0 : ℝ) 1} (hst : s.1 ≤ t.1)
    (hgap : t.1 - s.1 ≤ ((2 : ℝ) ^ n)⁻¹) :
    (unitDyadicFloorIndex n t).val - (unitDyadicFloorIndex n s).val ≤ 1 := by
  let c : ℝ := (2 : ℝ) ^ n
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hscaled : c * (t.1 - s.1) ≤ 1 := by
    calc
      c * (t.1 - s.1) ≤ c * c⁻¹ :=
        mul_le_mul_of_nonneg_left hgap hc.le
      _ = 1 := mul_inv_cancel₀ hc.ne'
  have hmul : c * t.1 ≤ c * s.1 + 1 := by
    calc
      c * t.1 = c * s.1 + c * (t.1 - s.1) := by ring
      _ ≤ c * s.1 + 1 := add_le_add_right hscaled _
  have hfloor : ⌊c * t.1⌋₊ ≤ ⌊c * s.1⌋₊ + 1 := by
    calc
      ⌊c * t.1⌋₊ ≤ ⌊c * s.1 + 1⌋₊ := Nat.floor_mono hmul
      _ = ⌊c * s.1⌋₊ + 1 := Nat.floor_add_one (mul_nonneg hc.le s.2.1)
  have hmono : ⌊c * s.1⌋₊ ≤ ⌊c * t.1⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left hst hc.le)
  simp only [unitDyadicFloorIndex_val]
  change ⌊c * t.1⌋₊ - ⌊c * s.1⌋₊ ≤ 1
  omega
