-- Prove2me | solution 1 for MarkovProcess.unitDyadicFloorIndex_sub_refineIndex_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:31:26.628281+00:00
-- url     : https://prove2.me/submissions/96b8033c-b839-48c1-8c48-a28bcc4dce12

import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicChaining_a582e42e
import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicFloor_a02de258
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov

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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

namespace MarkovProcess

section DyadicFloorApproximation


noncomputable section















end

end DyadicFloorApproximation

section DyadicFloorPair

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


noncomputable section









end

end DyadicFloorPair

section DyadicFloorSampleCauchy

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]







end DyadicFloorSampleCauchy

section DyadicFloorDenseTime


noncomputable section















end

end DyadicFloorDenseTime

section DyadicFloorSampleLimit

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E] [T2Space E] [CompleteSpace E]



end DyadicFloorSampleLimit

section DyadicFloorLimitControl

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]









end

end DyadicFloorLimitControl

section DyadicFloorLimitPath

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [PseudoMetricSpace E] [CompleteSpace E]











end

end DyadicFloorLimitPath

section DyadicFloorConvergenceInMeasure

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]













end DyadicFloorConvergenceInMeasure

section DyadicFloorUnitModification

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]









end

end DyadicFloorUnitModification

end MarkovProcess


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

















namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    (unitDyadicFloorIndex (n + 1) t).val -
        (unitDyadicRefineIndex n (unitDyadicFloorIndex n t)).val ≤ 1 := by
  rw [← unitDyadicParentIndex_floorIndex n t]
  exact unitDyadic_child_sub_refineIndex_parent_le_one n (unitDyadicFloorIndex (n + 1) t)
