-- Prove2me | solution 1 for MarkovProcess.tendsto_dyadicIncrementThreshold_ancestor_tail_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:06:51.370373+00:00
-- url     : https://prove2.me/submissions/b0185df8-f2ed-4fa5-a237-ef2d09c78f73

import Definitions.Def_MarkovProcess_Continuity_DyadicChaining
import Definitions.Def_MarkovProcess_Continuity_DyadicIncrements
import Definitions.Def_MarkovProcess_Time_FiniteGridIncrement
import Mathlib.Analysis.SpecificLimits.Basic
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
# Chaining across unit dyadic grids

This file merges the following former modules, one section each:

* `DyadicGridChaining`: Same-level chaining on dyadic grids
* `DyadicMultiscale`: Refinement and parent comparison for unit dyadic grids
* `DyadicAncestorChaining`: Finite chains of dyadic ancestors
* `DyadicAncestorTail`: Uniform tail bounds for finite dyadic ancestor chains
-/



open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]







open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]























open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]













open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]






theorem solution
    {γ : ℝ} (hγ : 0 < γ) :
    Tendsto
      (fun n : ℕ ↦ dyadicIncrementThreshold γ (n + 1) *
        (1 - dyadicIncrementThresholdRatio γ)⁻¹)
      atTop (nhds 0) := by
  have hratio : dyadicIncrementThresholdRatio γ < 1 :=
    dyadicIncrementThresholdRatio_lt_one hγ
  have hpow : Tendsto (fun n : ℕ ↦ dyadicIncrementThresholdRatio γ ^ n)
      atTop (nhds 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hratio
  have hpow_succ : Tendsto (fun n : ℕ ↦ dyadicIncrementThresholdRatio γ ^ (n + 1))
      atTop (nhds 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr hpow
  have htail_ne_top : (1 - dyadicIncrementThresholdRatio γ)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hratio).ne'
  simpa only [dyadicIncrementThreshold_eq_ratio_pow, zero_mul] using
    ENNReal.Tendsto.mul_const hpow_succ (Or.inr htail_ne_top)
