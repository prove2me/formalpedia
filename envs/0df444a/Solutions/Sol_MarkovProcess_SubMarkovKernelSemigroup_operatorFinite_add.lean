-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.operatorFinite_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:45:47.129897+00:00
-- url     : https://prove2.me/submissions/195d6545-f8d1-4483-a9d2-b56fa1cd2d26

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
















/-- The finite-exponent operator is represented by the raw kernel integral. -/
theorem coeFn_kernelLpFinite (μ : Measure α) (κ : Kernel α α)
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) (p : NNReal)
    [Fact (1 ≤ p)] (f : Lp ℝ (p : ℝ≥0∞) μ) :
    kernelLpFinite μ κ hκ hκμ p f =ᵐ[μ] kernelIntegral κ f := by
  rw [kernelLpFinite, LinearMap.mkContinuous_apply]
  exact MemLp.coeFn_toLp
    (MemLp.kernelIntegral hκ hκμ Fact.out (Lp.memLp f))













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





















/-- The canonical finite-exponent family is associated with `P`. -/
theorem isAssociatedFinite_operatorFinite (μ : Measure α) (hμ : P.IsSubInvariant μ)
    (p : NNReal) [Fact (1 ≤ p)] :
    P.IsAssociatedFinite μ p (P.operatorFinite μ hμ p) := by
  intro t f
  exact coeFn_kernelLpFinite μ (P t) (P.isSubMarkovKernel t) (hμ t) p f







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





private theorem ae_integrable_kernel_finite {μ : Measure α} {κ : Kernel α α}
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) {p : NNReal}
    (hp : 1 ≤ p) (f : Lp ℝ (p : ℝ≥0∞) μ) : ∀ᵐ x ∂μ, Integrable f (κ x) := by
  let : IsFiniteKernel κ := hκ.isFiniteKernel
  have hfComp : MemLp f p (κ ∘ₘ μ) := (Lp.memLp f).mono_measure hκμ
  have hFiberEq := Measure.ae_ae_of_ae_comp hfComp.1.ae_eq_mk
  have hp0 : (p : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast ne_of_gt (zero_lt_one.trans_le hp)
  have hpowInt := hfComp.integrable_norm_rpow hp0 ENNReal.coe_ne_top
  have hFiberInt := Measure.ae_integrable_of_integrable_comp hpowInt
  filter_upwards [hFiberEq, hFiberInt] with x hxEq hxInt
  have hxEq' : f =ᵐ[κ x] hfComp.1.mk f := hxEq
  have hxMeas : AEStronglyMeasurable f (κ x) :=
    hfComp.1.stronglyMeasurable_mk.aestronglyMeasurable.congr hxEq'.symm
  have hxMemLp : MemLp f p (κ x) :=
    (integrable_norm_rpow_iff hxMeas hp0 ENNReal.coe_ne_top).mp hxInt
  exact hxMemLp.integrable (by exact_mod_cast hp)



private theorem kernelIntegral_add_ae_finite {μ : Measure α}
    (hμ : P.IsSubInvariant μ) (p : NNReal) [Fact (1 ≤ p)]
    (s t : NNReal) (f : Lp ℝ (p : ℝ≥0∞) μ) :
    kernelIntegral (P (s + t)) f =ᵐ[μ]
      kernelIntegral (P s) (kernelIntegral (P t) f) := by
  filter_upwards
    [ae_integrable_kernel_finite (P.isSubMarkovKernel (s + t)) (hμ (s + t)) Fact.out f]
      with x hx
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
    (p : NNReal) [Fact (1 ≤ p)] (s t : NNReal) :
    P.operatorFinite μ hμ p (s + t) =
      (P.operatorFinite μ hμ p s).comp (P.operatorFinite μ hμ p t) := by
  ext f
  refine (P.isAssociatedFinite_operatorFinite μ hμ p (s + t) f).trans ?_
  refine (kernelIntegral_add_ae_finite P hμ p s t f).trans ?_
  refine (kernelIntegral_congr_ae (hμ s)
    (P.isAssociatedFinite_operatorFinite μ hμ p t f).symm).trans ?_
  exact (P.isAssociatedFinite_operatorFinite μ hμ p s (P.operatorFinite μ hμ p t f)).symm
