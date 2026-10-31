-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.norm_operatorFinite_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:45:06.13869+00:00
-- url     : https://prove2.me/submissions/537cdb2b-5d23-456b-b49c-e48210aa6629

import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_Lp_4fe2b873
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


















/-- The finite-exponent operator contracts the norm of every input. -/
theorem norm_kernelLpFinite_apply_le (μ : Measure α) (κ : Kernel α α)
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) (p : NNReal)
    [Fact (1 ≤ p)] (f : Lp ℝ (p : ℝ≥0∞) μ) :
    ‖kernelLpFinite μ κ hκ hκμ p f‖ ≤ ‖f‖ := by
  change ‖(MemLp.kernelIntegral hκ hκμ Fact.out (Lp.memLp f)).toLp
    (kernelIntegral κ f)‖ ≤ ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_kernelIntegral_le hκ hκμ Fact.out (Lp.memLp f))

/-- The finite-exponent kernel operator has operator norm at most one. -/
theorem norm_kernelLpFinite_le (μ : Measure α) (κ : Kernel α α)
    (hκ : IsSubMarkovKernel κ) (hκμ : κ ∘ₘ μ ≤ μ) (p : NNReal)
    [Fact (1 ≤ p)] : ‖kernelLpFinite μ κ hκ hκμ p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using norm_kernelLpFinite_apply_le μ κ hκ hκμ p f









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
# Operators associated with a sub-Markov kernel semigroup

This file constructs the jointly measurable time-space kernel and the
canonical contractive operator families on real `Lᵖ`.  It deliberately makes
no claim here about the operator semigroup laws or strong continuity.
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
    (p : NNReal) [Fact (1 ≤ p)] (t : NNReal) :
    ‖P.operatorFinite μ hμ p t‖ ≤ 1 :=
  norm_kernelLpFinite_le μ (P t) (P.isSubMarkovKernel t) (hμ t) p
