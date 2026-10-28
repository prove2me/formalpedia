-- Prove2me | solution 1 for MarkovProcess.IsKolmogorovProcess.tendstoInMeasure_unitDyadicFloorValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:16:03.039914+00:00
-- url     : https://prove2.me/submissions/272153b3-2cf8-4b48-b82c-8065e6d3af73

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
import Theorems.Thm_MarkovProcess_measure_edist_ge_le_of_isKolmogorovProcess
import Theorems.Thm_MarkovProcess_tendsto_edist_unitDyadicFloorValue_unitIccOfNNRat
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
    {P : Measure Ω} {X : NNRat → Ω → E} {p q : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (t : NNRat) (ht : t ≤ 1) :
    TendstoInMeasure P
      (fun n ↦ X (unitDyadicFloorValue n (unitIccOfNNRat t ht))) atTop (X t) := by
  refine tendstoInMeasure_of_ne_top fun ε hε hεtop ↦ ?_
  have hed := tendsto_edist_unitDyadicFloorValue_unitIccOfNNRat t ht
  have hrpow : Tendsto
      (fun n ↦ edist (unitDyadicFloorValue n (unitIccOfNNRat t ht)) t ^ q)
      atTop (nhds 0) := by
    simpa only [ENNReal.zero_rpow_of_pos hX.q_pos] using hed.ennrpow_const q
  have hrhs : Tendsto
      (fun n ↦ M * edist (unitDyadicFloorValue n (unitIccOfNNRat t ht)) t ^ q / ε ^ p)
      atTop (nhds 0) := by
    have hmul : Tendsto
        (fun n ↦ (M : ℝ≥0∞) *
          edist (unitDyadicFloorValue n (unitIccOfNNRat t ht)) t ^ q)
        atTop (nhds 0) := by
      simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul (a := (M : ℝ≥0∞)) hrpow
          (Or.inr ENNReal.coe_ne_top)
    have hdenom0 : ε ^ p ≠ 0 :=
      (ENNReal.rpow_eq_zero_iff_of_pos hX.p_pos).not.mpr hε.ne'
    have hscaled := ENNReal.Tendsto.const_mul (a := (ε ^ p)⁻¹) hmul
      (Or.inr (ENNReal.inv_ne_top.mpr hdenom0))
    simpa only [mul_zero, div_eq_mul_inv, mul_comm] using hscaled
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
    (fun _ ↦ zero_le) (fun n ↦
      measure_edist_ge_le_of_isKolmogorovProcess hX _ _ ε hε.ne' hεtop)
