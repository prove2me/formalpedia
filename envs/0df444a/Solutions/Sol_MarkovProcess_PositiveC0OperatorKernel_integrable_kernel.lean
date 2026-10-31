-- Prove2me | solution 1 for MarkovProcess.PositiveC0OperatorKernel.integrable_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:09:10.238656+00:00
-- url     : https://prove2.me/submissions/5b509d7f-9078-4be1-b27d-d4ab02293dcc

import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Definitions.Def_MarkovProcess_V3H_Kernel_MeasurableRadonFamily_620ec0ca
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorKernel_13678038
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0OperatorMass_48f724bb
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Kernels represented by positive operators on `C₀`

A positive contraction on real continuous functions vanishing at infinity determines a
sub-Markov kernel.  Its values are the pointwise Riesz measures of the evaluation functionals.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open CompactlySupported Filter MeasureTheory ProbabilityTheory Set
open scoped ZeroAtInfty

namespace MarkovProcess.PositiveC0OperatorKernel

variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]

variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ))
  (hT : PositiveC0OperatorMeasure.IsPositive T)















end MarkovProcess.PositiveC0OperatorKernel


open MarkovProcess
open MarkovProcess.PositiveC0OperatorKernel
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Kernels represented by positive operators on `C₀`

A positive contraction on real continuous functions vanishing at infinity determines a
sub-Markov kernel.  Its values are the pointwise Riesz measures of the evaluation functionals.
-/

open CompactlySupported Filter MeasureTheory ProbabilityTheory Set
open scoped ZeroAtInfty


variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]

variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ))
  (hT : PositiveC0OperatorMeasure.IsPositive T)











namespace MarkovProcess.PositiveC0OperatorKernel

end MarkovProcess.PositiveC0OperatorKernel
open MarkovProcess.PositiveC0OperatorKernel
theorem solution (hT_norm : ‖T‖ ≤ 1) (x : α) (f : C₀(α, ℝ)) :
    Integrable f (kernel T hT hT_norm x) := by
  let : IsFiniteMeasure (kernel T hT hT_norm x) :=
    PositiveC0OperatorMeasure.isFiniteMeasure_measure T hT hT_norm x
  exact f.toBCF.integrable _
