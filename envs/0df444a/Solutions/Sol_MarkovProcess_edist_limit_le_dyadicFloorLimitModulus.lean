-- Prove2me | solution 1 for MarkovProcess.edist_limit_le_dyadicFloorLimitModulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:01:39.449669+00:00
-- url     : https://prove2.me/submissions/7c1eeaff-2e7d-4909-911b-eec047f15ea8

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












open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]










noncomputable section


















open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E] [T2Space E] [CompleteSpace E]





open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]






theorem solution
    {X : NNRat → Ω → E} {γ : ℝ} {n : ℕ} {ω : Ω}
    {s t : Set.Icc (0 : ℝ) 1} {y z : E}
    (htail : ∀ r (u : Set.Icc (0 : ℝ) 1),
      edist (X (unitDyadicFloorValue (n + r) u) ω)
          (X (unitDyadicFloorValue n u) ω) ≤
        dyadicIncrementThreshold γ (n + 1) *
          (1 - dyadicIncrementThresholdRatio γ)⁻¹)
    (hpair : edist (X (unitDyadicFloorValue n s) ω)
        (X (unitDyadicFloorValue n t) ω) ≤ dyadicIncrementThreshold γ n)
    (hy : Tendsto (fun m : ℕ ↦ X (unitDyadicFloorValue m s) ω) atTop (nhds y))
    (hz : Tendsto (fun m : ℕ ↦ X (unitDyadicFloorValue m t) ω) atTop (nhds z)) :
    edist y z ≤ dyadicFloorLimitModulus γ n := by
  have hy_shift : Tendsto
      (fun r : ℕ ↦ X (unitDyadicFloorValue (n + r) s) ω) atTop (nhds y) :=
    by simpa only [Nat.add_comm] using (tendsto_add_atTop_iff_nat n).mpr hy
  have hz_shift : Tendsto
      (fun r : ℕ ↦ X (unitDyadicFloorValue (n + r) t) ω) atTop (nhds z) :=
    by simpa only [Nat.add_comm] using (tendsto_add_atTop_iff_nat n).mpr hz
  have hy_base : edist y (X (unitDyadicFloorValue n s) ω) ≤
      dyadicIncrementThreshold γ (n + 1) *
        (1 - dyadicIncrementThresholdRatio γ)⁻¹ := by
    rw [edist_comm]
    refine le_of_tendsto (tendsto_const_nhds.edist hy_shift) ?_
    exact Eventually.of_forall fun r ↦ by
      simpa only [edist_comm] using htail r s
  have hz_base : edist (X (unitDyadicFloorValue n t) ω) z ≤
      dyadicIncrementThreshold γ (n + 1) *
        (1 - dyadicIncrementThresholdRatio γ)⁻¹ := by
    refine le_of_tendsto (tendsto_const_nhds.edist hz_shift) ?_
    exact Eventually.of_forall fun r ↦ by
      simpa only [edist_comm] using htail r t
  unfold dyadicFloorLimitModulus
  calc
    edist y z ≤ edist y (X (unitDyadicFloorValue n s) ω) +
        edist (X (unitDyadicFloorValue n s) ω) z :=
      edist_triangle _ _ _
    _ ≤ edist y (X (unitDyadicFloorValue n s) ω) +
        (edist (X (unitDyadicFloorValue n s) ω)
            (X (unitDyadicFloorValue n t) ω) +
          edist (X (unitDyadicFloorValue n t) ω) z) :=
      add_le_add le_rfl (edist_triangle _ _ _)
    _ = (edist y (X (unitDyadicFloorValue n s) ω) +
          edist (X (unitDyadicFloorValue n s) ω)
            (X (unitDyadicFloorValue n t) ω)) +
        edist (X (unitDyadicFloorValue n t) ω) z := by
      rw [add_assoc]
    _ ≤ (dyadicIncrementThreshold γ (n + 1) *
          (1 - dyadicIncrementThresholdRatio γ)⁻¹) +
        dyadicIncrementThreshold γ n +
        (dyadicIncrementThreshold γ (n + 1) *
          (1 - dyadicIncrementThresholdRatio γ)⁻¹) := by
      exact add_le_add (add_le_add hy_base hpair) hz_base
