-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsAssociatedTop.isConservativeAE_of_preservesOne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:18:57.618695+00:00
-- url     : https://prove2.me/submissions/a5e1ae62-657c-4955-89b5-707d6c38acfb

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



/-- The `L∞` constant-one class is represented by the constant-one function. -/
theorem coeFn_oneLpTop (μ : Measure α) :
    oneLpTop μ =ᵐ[μ] fun _ : α => (1 : ℝ) :=
  (memLp_top_const (μ := μ) (1 : ℝ)).coeFn_toLp

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





namespace MarkovProcess.SubMarkovKernelSemigroup.IsAssociatedTop

end MarkovProcess.SubMarkovKernelSemigroup.IsAssociatedTop
open MarkovProcess.SubMarkovKernelSemigroup.IsAssociatedTop
theorem solution
    {μ : Measure α} {T : NNReal → Lp ℝ ∞ μ →L[ℝ] Lp ℝ ∞ μ}
    (hμ : P.IsSubInvariant μ) (hAssoc : P.IsAssociatedTop μ T)
    (hOne : PreservesOneTop μ T) : P.IsConservativeAE μ := by
  intro t
  have hPres : T t (oneLpTop μ) =ᵐ[μ] oneLpTop μ :=
    Filter.Eventually.of_forall fun x => congrArg (fun f : Lp ℝ ∞ μ => f x) (hOne t)
  have hKernel := kernelIntegral_congr_ae (hμ t) (coeFn_oneLpTop μ)
  filter_upwards [hAssoc t (oneLpTop μ), hPres, coeFn_oneLpTop μ, hKernel] with
    x hAssocX hPresX hOneX hKernelX
  have hIntegral : kernelIntegral (P t) (fun _ : α => (1 : ℝ)) x = 1 := by
    calc
      kernelIntegral (P t) (fun _ : α => (1 : ℝ)) x =
          kernelIntegral (P t) (oneLpTop μ) x := hKernelX.symm
      _ = T t (oneLpTop μ) x := hAssocX.symm
      _ = oneLpTop μ x := hPresX
      _ = 1 := hOneX
  have hReal : (P t x Set.univ).toReal = 1 := by
    simpa only [kernelIntegral, integral_const, Measure.real_def, smul_eq_mul, mul_one]
      using hIntegral
  exact (ENNReal.toReal_eq_one_iff _).mp hReal
