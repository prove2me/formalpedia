-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservativeAE.isConservative_of_continuous_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:33:55.724881+00:00
-- url     : https://prove2.me/submissions/895ccbea-84d3-4851-a066-f5539c0b4f77

import Definitions.Def_MarkovProcess_V3H_Kernel_ConservativityAE_4ed86db4
import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conservativity from preservation of constants

This file extracts the measure-theoretic conservativity consequence of an
associated `L∞` operator that preserves the constant-one class.  The conclusion
is initially almost everywhere in the starting point.  Continuity of the
transition mass and positivity of the reference measure on nonempty open sets
upgrade it to pointwise conservativity.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]





namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)











end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conservativity from preservation of constants

This file extracts the measure-theoretic conservativity consequence of an
associated `L∞` operator that preserves the constant-one class.  The conclusion
is initially almost everywhere in the starting point.  Continuity of the
transition mass and positivity of the reference measure on nonempty open sets
upgrade it to pointwise conservativity.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α]






variable (P : SubMarkovKernelSemigroup α)









namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservativeAE

end MarkovProcess.SubMarkovKernelSemigroup.IsConservativeAE
open MarkovProcess.SubMarkovKernelSemigroup.IsConservativeAE
theorem solution
    {μ : Measure α} [TopologicalSpace α] [Measure.IsOpenPosMeasure μ]
    (hAE : P.IsConservativeAE μ)
    (hcont : ∀ t, Continuous fun x => P t x Set.univ) :
    P.IsConservative := by
  intro t x
  exact congrFun (Measure.eq_of_ae_eq (hAE t) (hcont t) continuous_const) x
