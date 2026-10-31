-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.operatorTop_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:46:11.953665+00:00
-- url     : https://prove2.me/submissions/f112fe8a-7019-4c67-b42d-5c8d5ae81fa1

import Definitions.Def_MarkovProcess_V3H_Kernel_OperatorSemigroup_081c0d2f
import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
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
# Semigroup laws for the canonical kernel operators

This file proves only the algebraic zero- and add-time laws for the canonical
real `Lᵖ` operator families.  It makes no strong-continuity claim.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]

namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup α)



private theorem kernelIntegral_id_ae {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    kernelIntegral Kernel.id f =ᵐ[μ] f := by
  let g := hf.mk f
  have hfg : kernelIntegral Kernel.id f =ᵐ[μ] kernelIntegral Kernel.id g :=
    kernelIntegral_congr_ae (by rw [Measure.id_comp]) hf.ae_eq_mk
  refine hfg.trans ?_
  filter_upwards [hf.ae_eq_mk] with x hx
  rw [kernelIntegral, Kernel.id_apply, integral_dirac' g x hf.stronglyMeasurable_mk]
  exact hx.symm

















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
# Semigroup laws for the canonical kernel operators

This file proves only the algebraic zero- and add-time laws for the canonical
real `Lᵖ` operator families.  It makes no strong-continuity claim.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α]


variable (P : SubMarkovKernelSemigroup α)

















namespace MarkovProcess.SubMarkovKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
theorem solution (μ : Measure α) (hμ : P.IsSubInvariant μ) :
    P.operatorTop μ hμ 0 = ContinuousLinearMap.id ℝ (Lp ℝ ∞ μ) := by
  ext f
  refine (P.isAssociatedTop_operatorTop μ hμ 0 f).trans ?_
  rw [P.zero]
  exact (kernelIntegral_id_ae (Lp.aestronglyMeasurable f)).trans
    Filter.EventuallyEq.rfl
