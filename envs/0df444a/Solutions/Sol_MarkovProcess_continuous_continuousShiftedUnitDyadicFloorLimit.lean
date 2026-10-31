-- Prove2me | solution 1 for MarkovProcess.continuous_continuousShiftedUnitDyadicFloorLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:27:30.657993+00:00
-- url     : https://prove2.me/submissions/e523098b-1e85-45e9-bf8f-8087e01787e8

import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicFloor_a02de258
import Definitions.Def_MarkovProcess_V3H_Continuity_KolmogorovTimeShift_b20f4218
import Definitions.Def_MarkovProcess_V3H_Continuity_ShiftedUnitModification_dfb22f1c
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





omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The totalized unit-interval path is continuous for every sample. -/
theorem continuous_continuousUnitDyadicFloorLimit
    (X : NNRat → Ω → E) (ω : Ω) :
    Continuous (continuousUnitDyadicFloorLimit X ω) := by
  by_cases h : Continuous (unitDyadicFloorLimit X ω)
  · simpa only [continuousUnitDyadicFloorLimit, if_pos h] using h
  · simp only [continuousUnitDyadicFloorLimit, if_neg h]
    exact continuous_const



end

end DyadicFloorUnitModification

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuous modifications on shifted unit intervals

This file applies the unit-interval totalization to a nonnegative-rational time shift.  It also
identifies the endpoints of the underlying canonical limit exactly, for every sample, using the
eventual constancy of dyadic approximations at dyadic grid times.

No global path is glued here, and no path-space measurability, law, or Hunt-process property is
asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

noncomputable section

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]













end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuous modifications on shifted unit intervals

This file applies the unit-interval totalization to a nonnegative-rational time shift.  It also
identifies the endpoints of the underlying canonical limit exactly, for every sample, using the
eventual constancy of dyadic approximations at dyadic grid times.

No global path is glued here, and no path-space measurability, law, or Hunt-process property is
asserted.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal



variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [MetricSpace E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]



namespace MarkovProcess
end MarkovProcess
open MarkovProcess
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in

theorem solution
    (k : NNRat) (X : NNRat → Ω → E) (ω : Ω) :
    Continuous (continuousShiftedUnitDyadicFloorLimit k X ω) := by
  exact continuous_continuousUnitDyadicFloorLimit (timeShift k X) ω
