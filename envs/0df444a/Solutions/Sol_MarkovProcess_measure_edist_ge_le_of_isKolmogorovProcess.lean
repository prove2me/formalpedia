-- Prove2me | solution 1 for MarkovProcess.measure_edist_ge_le_of_isKolmogorovProcess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:06:07.629623+00:00
-- url     : https://prove2.me/submissions/5e55c715-182a-4fed-b0ce-838310cc4b68

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












open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [PseudoMetricSpace E] [CompleteSpace E]














open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]








theorem solution
    {T : Type*} [PseudoEMetricSpace T] {P : Measure Ω}
    {X : T → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (s t : T) (ε : ℝ≥0∞)
    (hε0 : ε ≠ 0) (hεtop : ε ≠ ∞) :
    P {ω | ε ≤ edist (X s ω) (X t ω)} ≤ M * edist s t ^ q / ε ^ p := by
  calc
    P {ω | ε ≤ edist (X s ω) (X t ω)} =
        P {ω | ε ^ p ≤ edist (X s ω) (X t ω) ^ p} := by
      congr 1
      ext ω
      change (ε ≤ edist (X s ω) (X t ω)) ↔
        (ε ^ p ≤ edist (X s ω) (X t ω) ^ p)
      exact (ENNReal.rpow_le_rpow_iff hX.p_pos).symm
    _ ≤ (∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P) / ε ^ p := by
      apply meas_ge_le_lintegral_div
      · exact (hX.measurable_edist.pow_const p).aemeasurable
      · exact (ENNReal.rpow_eq_zero_iff_of_pos hX.p_pos).not.mpr hε0
      · exact (ENNReal.rpow_eq_top_iff_of_pos hX.p_pos).not.mpr hεtop
    _ ≤ M * edist s t ^ q / ε ^ p := by
      gcongr
      exact hX.kolmogorovCondition s t
