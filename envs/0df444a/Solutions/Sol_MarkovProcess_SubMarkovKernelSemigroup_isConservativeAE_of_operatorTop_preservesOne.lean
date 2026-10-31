-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.isConservativeAE_of_operatorTop_preservesOne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:39:08.7989+00:00
-- url     : https://prove2.me/submissions/5b3a9b2f-890e-47bb-8e70-3916bd5d8c23

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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsAssociatedTop_isConservativeAE_of_preservesOne

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Kernel integral operators on real `Lᵖ`

This file packages the raw kernel integral as continuous linear contractions on
finite-exponent and infinite-exponent real `Lᵖ` spaces.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]



/- Head-class caches for the `Lᵖ` carrier.  Without them every normed-group
class search on `↥(Lp ℝ p μ)` first tries `AddSubgroup.seminormedAddCommGroup`
and burns a failing search for `SeminormedAddCommGroup (α →ₘ[μ] ℝ)`. -/
























/-- The infinite-exponent operator is represented by the raw kernel integral. -/
theorem coeFn_kernelLpTop (μ : Measure α) (κ : Kernel α α)
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) (f : Lp ℝ ∞ μ) :
    kernelLpTop μ κ hκ hκμ f =ᵐ[μ] kernelIntegral κ f := by
  rw [kernelLpTop, LinearMap.mkContinuous_apply]
  exact MemLp.coeFn_toLp (MemLp.kernelIntegral_top hκ hκμ (Lp.memLp f))





end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Operators associated with a sub-Markov kernel semigroup

This file constructs the jointly measurable time-space kernel and the
canonical contractive operator families on real `Lᵖ`.  It deliberately makes
no claim here about the operator semigroup laws or strong continuity.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)























/-- The canonical infinite-exponent family is associated with `P`. -/
theorem isAssociatedTop_operatorTop (μ : Measure α) (hμ : P.IsSubInvariant μ) :
    P.IsAssociatedTop μ (P.operatorTop μ hμ) := by
  intro t f
  exact coeFn_kernelLpTop μ (P t) (P.isSubMarkovKernel t) (hμ t) f





end SubMarkovKernelSemigroup

end MarkovProcess


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







namespace MarkovProcess.SubMarkovKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
theorem solution
    {μ : Measure α} (hμ : P.IsSubInvariant μ)
    (hOne : PreservesOneTop μ (P.operatorTop μ hμ)) :
    P.IsConservativeAE μ :=
  IsAssociatedTop.isConservativeAE_of_preservesOne
    (P := P) hμ (P.isAssociatedTop_operatorTop μ hμ) hOne
