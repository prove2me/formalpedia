-- Prove2me | solution 1 for MarkovProcess.kernelLpFinite_consistent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:29:02.745715+00:00
-- url     : https://prove2.me/submissions/755916f1-5c6e-48bb-bca7-e5be29104934

import Definitions.Def_MarkovProcess_V3H_Kernel_Lp_4fe2b873
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
# Cross-exponent consistency of kernel integral operators

The finite- and infinite-exponent operators are packages of the same raw
kernel integral.  Consequently their representatives agree almost everywhere
whenever their inputs do, even when the inputs and outputs inhabit different
`Lp` types.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace MarkovProcess

variable {α : Type*} [MeasurableSpace α]







end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Cross-exponent consistency of kernel integral operators

The finite- and infinite-exponent operators are packages of the same raw
kernel integral.  Consequently their representatives agree almost everywhere
whenever their inputs do, even when the inputs and outputs inhabit different
`Lp` types.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal ProbabilityTheory


variable {α : Type*} [MeasurableSpace α]

namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution
    (μ : Measure α) (κ : Kernel α α) (hκ : IsSubMarkovKernel κ)
    (hκμ : κ ∘ₘ μ ≤ μ) (p q : NNReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : Lp ℝ (p : ℝ≥0∞) μ) (g : Lp ℝ (q : ℝ≥0∞) μ)
    (hfg : f =ᵐ[μ] g) :
    kernelLpFinite μ κ hκ hκμ p f =ᵐ[μ]
      kernelLpFinite μ κ hκ hκμ q g := by
  exact (coeFn_kernelLpFinite μ κ hκ hκμ p f).trans
    ((kernelIntegral_congr_ae hκμ hfg).trans
      (coeFn_kernelLpFinite μ κ hκ hκμ q g).symm)
