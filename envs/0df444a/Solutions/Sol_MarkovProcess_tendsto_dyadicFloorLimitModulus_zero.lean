-- Prove2me | solution 1 for MarkovProcess.tendsto_dyadicFloorLimitModulus_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:14:21.040583+00:00
-- url     : https://prove2.me/submissions/60a6eeb7-b6a6-4b3a-abe7-bad4e08c1dfc

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
import Theorems.Thm_MarkovProcess_tendsto_dyadicIncrementThreshold_ancestor_tail_zero
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
# Dyadic increment bounds for the Kolmogorov--Chentsov argument

This file merges the following former modules, one section each:

* `DyadicIncrementSummability`: Geometric summability for dyadic increment bounds
* `DyadicBorelCantelli`: Borel--Cantelli for dyadic increment events
* `DyadicIncrementControl`: Almost-sure control of adjacent dyadic increments
* `DyadicThresholdTail`: Geometric tails of dyadic increment thresholds
-/

namespace MarkovProcess

section DyadicIncrementSummability

open scoped ENNReal NNReal










end DyadicIncrementSummability

section DyadicBorelCantelli

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]















end DyadicBorelCantelli

section DyadicIncrementControl

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]





end DyadicIncrementControl

section DyadicThresholdTail

open scoped ENNReal NNReal




/-- The level-`n` threshold is the `n`th power of the one-level decay ratio. -/
theorem dyadicIncrementThreshold_eq_ratio_pow (γ : ℝ) (n : ℕ) :
    dyadicIncrementThreshold γ n = dyadicIncrementThresholdRatio γ ^ n := by
  unfold dyadicIncrementThreshold dyadicIncrementThresholdRatio
  rw [ENNReal.inv_rpow, ← ENNReal.rpow_natCast_mul, ← ENNReal.rpow_neg,
    ← ENNReal.rpow_mul_natCast]
  congr 2
  ring

/-- Positive exponents make the one-level threshold ratio strictly smaller than one. -/
theorem dyadicIncrementThresholdRatio_lt_one {γ : ℝ} (hγ : 0 < γ) :
    dyadicIncrementThresholdRatio γ < 1 := by
  unfold dyadicIncrementThresholdRatio
  exact ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hγ)
end DyadicThresholdTail
end MarkovProcess
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




theorem solution {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (dyadicFloorLimitModulus γ) atTop (nhds 0) := by
  have hratio : dyadicIncrementThresholdRatio γ < 1 :=
    dyadicIncrementThresholdRatio_lt_one hγ
  have hthreshold :
      Tendsto (dyadicIncrementThreshold γ) atTop (nhds 0) := by
    rw [show dyadicIncrementThreshold γ =
        fun n : ℕ ↦ dyadicIncrementThresholdRatio γ ^ n by
      funext n
      exact dyadicIncrementThreshold_eq_ratio_pow γ n]
    exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hratio
  have htail := tendsto_dyadicIncrementThreshold_ancestor_tail_zero hγ
  simpa only [dyadicFloorLimitModulus, zero_add] using!
    (htail.add hthreshold).add htail
