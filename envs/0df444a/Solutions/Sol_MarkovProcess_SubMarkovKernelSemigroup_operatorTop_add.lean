-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.operatorTop_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:46:03.55123+00:00
-- url     : https://prove2.me/submissions/a0a4e1da-69c1-4142-9511-af06bed18249

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







private theorem ae_integrable_kernel_top {μ : Measure α} {κ : Kernel α α}
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ)
    (f : Lp ℝ ∞ μ) : ∀ᵐ x ∂μ, Integrable f (κ x) := by
  have hCtop : eLpNormEssSup f μ ≠ ∞ := by
    rw [← eLpNorm_exponent_top]
    exact (Lp.memLp f).2.ne
  have hCcoe : ((eLpNormEssSup f μ).toNNReal : ℝ≥0∞) = eLpNormEssSup f μ :=
    ENNReal.coe_toNNReal hCtop
  have hFiberEq : ∀ᵐ x ∂μ, f =ᵐ[κ x] (Lp.aestronglyMeasurable f).mk f :=
    ae_ae_kernel_of_comp_le hκμ (Lp.aestronglyMeasurable f).ae_eq_mk
  have hBound := ae_ae_kernel_of_comp_le hκμ (enorm_ae_le_eLpNormEssSup f μ)
  let : IsFiniteKernel κ := hκ.isFiniteKernel
  filter_upwards [hFiberEq, hBound] with x hxEq hxBound
  have hxAS : AEStronglyMeasurable f (κ x) :=
    (Lp.aestronglyMeasurable f).stronglyMeasurable_mk.aestronglyMeasurable.congr hxEq.symm
  apply MemLp.integrable (q := ∞) le_top
  apply memLp_top_of_bound_enorm hxAS (eLpNormEssSup f μ).toNNReal
  simpa only [hCcoe] using hxBound



private theorem kernelIntegral_add_ae_top {μ : Measure α}
    (hμ : P.IsSubInvariant μ) (s t : NNReal) (f : Lp ℝ ∞ μ) :
    kernelIntegral (P (s + t)) f =ᵐ[μ]
      kernelIntegral (P s) (kernelIntegral (P t) f) := by
  filter_upwards
    [ae_integrable_kernel_top (P.isSubMarkovKernel (s + t)) (hμ (s + t)) f] with x hx
  have hx' : Integrable f ((P t ∘ₖ P s) x) := by
    rw [← P.add]
    exact hx
  rw [kernelIntegral, P.add]
  exact Kernel.integral_comp hx'









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
theorem solution (μ : Measure α) (hμ : P.IsSubInvariant μ)
    (s t : NNReal) :
    P.operatorTop μ hμ (s + t) =
      (P.operatorTop μ hμ s).comp (P.operatorTop μ hμ t) := by
  ext f
  refine (P.isAssociatedTop_operatorTop μ hμ (s + t) f).trans ?_
  refine (kernelIntegral_add_ae_top P hμ s t f).trans ?_
  refine (kernelIntegral_congr_ae (hμ s)
    (P.isAssociatedTop_operatorTop μ hμ t f).symm).trans ?_
  exact (P.isAssociatedTop_operatorTop μ hμ s (P.operatorTop μ hμ t f)).symm
