-- Prove2me | solution 1 for MarkovProcess.edist_unitDyadicFloorValue_le_of_sub_le_inv_pow_of_adjacent_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:13:14.971662+00:00
-- url     : https://prove2.me/submissions/89568b1d-24af-4c57-bfa6-36eaa57c190e

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
import Theorems.Thm_MarkovProcess_edist_unitDyadicGrid_le_natCast_mul_of_adjacent_le
import Theorems.Thm_MarkovProcess_unitDyadicFloorIndex_sub_le_one_of_sub_le_inv_pow
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

/-- Dyadic floor indices preserve the order of their represented times. -/
theorem MarkovProcess.unitDyadicFloorIndex_mono (n : ℕ) {s t : Set.Icc (0 : ℝ) 1}
    (hst : s.1 ≤ t.1) :
    (unitDyadicFloorIndex n s).val ≤ (unitDyadicFloorIndex n t).val := by
  simp only [unitDyadicFloorIndex_val]
  exact Nat.floor_mono (mul_le_mul_of_nonneg_left hst (by positivity))




theorem solution
    {Ω E : Type*} [PseudoEMetricSpace E] {X : NNRat → Ω → E}
    {n : ℕ} {ε : ℝ≥0∞} {ω : Ω}
    (hadj : ∀ k : Fin (2 ^ n),
      edist (X (unitDyadicGrid n k.castSucc) ω)
          (X (unitDyadicGrid n k.succ) ω) ≤ ε)
    {s t : Set.Icc (0 : ℝ) 1} (hst : s.1 ≤ t.1)
    (hgap : t.1 - s.1 ≤ ((2 : ℝ) ^ n)⁻¹) :
    edist (X (unitDyadicFloorValue n s) ω)
        (X (unitDyadicFloorValue n t) ω) ≤ ε := by
  have hmono := unitDyadicFloorIndex_mono n hst
  have hdiff := unitDyadicFloorIndex_sub_le_one_of_sub_le_inv_pow n hst hgap
  calc
    edist (X (unitDyadicFloorValue n s) ω)
        (X (unitDyadicFloorValue n t) ω) ≤
        ((unitDyadicFloorIndex n t).val - (unitDyadicFloorIndex n s).val : ℕ) * ε := by
      simpa only [unitDyadicFloorValue] using
        edist_unitDyadicGrid_le_natCast_mul_of_adjacent_le hadj
          (unitDyadicFloorIndex n s) (unitDyadicFloorIndex n t) hmono
    _ ≤ (1 : ℝ≥0∞) * ε := by
      have hcast :
          (((unitDyadicFloorIndex n t).val - (unitDyadicFloorIndex n s).val : ℕ) :
            ℝ≥0∞) ≤ 1 := by
        exact_mod_cast hdiff
      exact mul_le_mul_of_nonneg_right hcast bot_le
    _ = ε := one_mul ε
