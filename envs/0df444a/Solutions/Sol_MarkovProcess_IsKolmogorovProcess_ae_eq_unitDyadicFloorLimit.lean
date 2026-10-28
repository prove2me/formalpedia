-- Prove2me | solution 1 for MarkovProcess.IsKolmogorovProcess.ae_eq_unitDyadicFloorLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:35:25.343272+00:00
-- url     : https://prove2.me/submissions/054acf7f-32ee-4e8b-b68e-6df58700a345

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
import Theorems.Thm_MarkovProcess_IsKolmogorovProcess_ae_cauchySeq_unitDyadicFloorValue
import Theorems.Thm_MarkovProcess_IsKolmogorovProcess_tendstoInMeasure_unitDyadicFloorValue
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





/-- Almost surely, the left dyadic samples converge to the canonical limit simultaneously
at every time in the unit interval. -/
theorem MarkovProcess.IsKolmogorovProcess.ae_tendsto_unitDyadicFloorLimit
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ t : Set.Icc (0 : ℝ) 1,
      Tendsto (fun n : ℕ ↦ X (unitDyadicFloorValue n t) ω) atTop
        (nhds (unitDyadicFloorLimit X ω t)) := by
  filter_upwards
    [IsKolmogorovProcess.ae_cauchySeq_unitDyadicFloorValue hX hγ hγq] with ω hω
  exact fun t ↦ tendsto_unitDyadicFloorLimit_of_cauchySeq (hω t)








open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]















open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]


theorem solution
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) (t : NNRat) (ht : t ≤ 1) :
    X t =ᵐ[P] fun ω ↦ unitDyadicFloorLimit X ω (unitIccOfNNRat t ht) := by
  let samples : ℕ → Ω → E :=
    fun n ↦ X (unitDyadicFloorValue n (unitIccOfNNRat t ht))
  let limit : Ω → E := fun ω ↦ unitDyadicFloorLimit X ω (unitIccOfNNRat t ht)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ samples n ω) atTop (nhds (limit ω)) := by
    filter_upwards [IsKolmogorovProcess.ae_tendsto_unitDyadicFloorLimit hX hγ hγq]
      with ω hω
    exact hω (unitIccOfNNRat t ht)
  have hsamples : ∀ n, AEStronglyMeasurable (samples n) P := by
    intro n
    exact (hX.measurable (unitDyadicFloorValue n (unitIccOfNNRat t ht))).aestronglyMeasurable
  have htendsto_limit : TendstoInMeasure P samples atTop limit :=
    tendstoInMeasure_of_tendsto_ae hsamples hlim
  have htendsto_original : TendstoInMeasure P samples atTop (X t) :=
    IsKolmogorovProcess.tendstoInMeasure_unitDyadicFloorValue hX t ht
  exact tendstoInMeasure_ae_unique htendsto_original htendsto_limit
