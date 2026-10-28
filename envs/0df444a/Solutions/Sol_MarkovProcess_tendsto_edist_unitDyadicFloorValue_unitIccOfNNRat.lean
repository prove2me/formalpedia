-- Prove2me | solution 1 for MarkovProcess.tendsto_edist_unitDyadicFloorValue_unitIccOfNNRat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:14:53.310376+00:00
-- url     : https://prove2.me/submissions/d0a19b49-138f-4c72-9924-22750c37bc65

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
import Theorems.Thm_MarkovProcess_sub_unitDyadicFloorValue_le
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







/-- The left dyadic approximation does not exceed the represented real time. -/
theorem MarkovProcess.unitDyadicFloorValue_le (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    (unitDyadicFloorValue n t : ℝ) ≤ t.1 := by
  have hnonneg : 0 ≤ (2 ^ n : ℝ) * t.1 :=
    mul_nonneg (by positivity) t.2.1
  have hfloor := Nat.floor_le hnonneg
  unfold unitDyadicFloorValue unitDyadicGrid
  simp only [unitDyadicFloorIndex_val]
  push_cast
  exact (div_le_iff₀' (by positivity)).2 (by simpa only [mul_comm] using hfloor)










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












open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [PseudoMetricSpace E] [CompleteSpace E]














open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]



@[simp]
theorem MarkovProcess.unitIccOfNNRat_val (t : NNRat) (ht : t ≤ 1) :
    (unitIccOfNNRat t ht).1 = (t : ℝ) :=
  rfl

/-- The dyadic-floor time is within one level-`n` cell of the original nonnegative rational
time. -/
theorem MarkovProcess.edist_unitDyadicFloorValue_unitIccOfNNRat_le
    (n : ℕ) (t : NNRat) (ht : t ≤ 1) :
    edist (unitDyadicFloorValue n (unitIccOfNNRat t ht)) t ≤
      ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) := by
  rw [edist_dist, NNRat.dist_eq, Rat.dist_eq]
  push_cast
  rw [abs_of_nonpos]
  · apply ENNReal.ofReal_le_ofReal
    simpa only [unitIccOfNNRat_val, neg_sub] using
      sub_unitDyadicFloorValue_le n (unitIccOfNNRat t ht)
  · exact sub_nonpos.mpr (by
      simpa only [unitIccOfNNRat_val] using
        unitDyadicFloorValue_le n (unitIccOfNNRat t ht))




theorem solution
    (t : NNRat) (ht : t ≤ 1) :
    Tendsto (fun n ↦ edist (unitDyadicFloorValue n (unitIccOfNNRat t ht)) t)
      atTop (nhds 0) := by
  have hbound : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹))
      atTop (nhds 0) := by
    have hpow : Tendsto (fun n : ℕ ↦ ((2 : ℝ)⁻¹) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
    convert ENNReal.tendsto_ofReal hpow using 1
    · funext n
      rw [inv_pow]
    · simp only [ENNReal.ofReal_zero]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
    (fun _ ↦ zero_le)
    (fun n ↦ edist_unitDyadicFloorValue_unitIccOfNNRat_le n t ht)
