-- Prove2me | solution 1 for MarkovProcess.PositiveC0ContractiveResolvent.integral_kernelSemigroup_le_exp_mul
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T19:13:56.56759+00:00
-- url     : https://prove2.me/submissions/af39a6ec-a1b3-432f-8c58-c24e87389f07

import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0Resolvent_c009f25c
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Metrizable.Urysohn
import Theorems.Thm_MarkovProcess_PositiveC0ContractiveResolvent_generatedSemigroup_apply_le_exp_mul

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Pointwise Riesz measures of positive operators on `C₀`

A positive continuous linear operator on real continuous functions vanishing at infinity gives,
after evaluation at a point, a positive linear functional on compactly supported continuous
functions. The real Riesz--Markov--Kakutani theorem represents this functional by a regular,
locally finite measure.

This file makes only this pointwise construction. It does not prove that the measures depend
measurably on the evaluation point, have bounded total mass, form a kernel, or satisfy any
semigroup or stochastic-process law.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open CompactlySupported MeasureTheory
open scoped ZeroAtInfty

namespace MarkovProcess

variable {α : Type*} [TopologicalSpace α]





namespace PositiveC0OperatorMeasure



/-- A positive operator on `C₀` is monotone for the pointwise order. -/
theorem apply_le_apply_of_isPositive
    (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)
    {f g : C₀(α, ℝ)} (hfg : ∀ x, f x ≤ g x) (x : α) :
    T f x ≤ T g x := by
  have hnonneg : ∀ y, 0 ≤ (g - f) y := fun y ↦ sub_nonneg.mpr (hfg y)
  have h := hT (g - f) hnonneg x
  rw [map_sub] at h
  exact sub_nonneg.mp h





variable (T : C₀(α, ℝ) →L[ℝ] C₀(α, ℝ)) (hT : IsPositive T)





variable [T2Space α] [LocallyCompactSpace α] [MeasurableSpace α] [BorelSpace α]









end PositiveC0OperatorMeasure

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exponential comparison under resolvent generation

A pointwise exponential supersolution estimate for every sufficiently large normalized positive
resolvent passes through the Poisson representation of the Yosida approximants and then through
their strong limit to the generated semigroup.  The represented kernel semigroup inherits the
same comparison for `C₀` observables.

Public declarations:

* `PositiveC0ContractiveResolvent.generatedSemigroup_apply_le_exp_mul`;
* `PositiveC0ContractiveResolvent.integral_kernelSemigroup_le_exp_mul`.

No comparison for indicators of arbitrary measurable sets is asserted.
-/

open Filter Set Topology
open scoped NNReal ZeroAtInfty
open NormedSpace

noncomputable section

namespace MarkovProcess

open _root_.MarkovProcess.Semigroup

namespace PositiveC0ContractiveResolvent

variable {X : Type*} [TopologicalSpace X]











section Kernel

variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]



end Kernel

end PositiveC0ContractiveResolvent

end MarkovProcess


open MarkovProcess
open MarkovProcess.PositiveC0ContractiveResolvent
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exponential comparison under resolvent generation

A pointwise exponential supersolution estimate for every sufficiently large normalized positive
resolvent passes through the Poisson representation of the Yosida approximants and then through
their strong limit to the generated semigroup.  The represented kernel semigroup inherits the
same comparison for `C₀` observables.

Public declarations:

* `PositiveC0ContractiveResolvent.generatedSemigroup_apply_le_exp_mul`;
* `PositiveC0ContractiveResolvent.integral_kernelSemigroup_le_exp_mul`.

No comparison for indicators of arbitrary measurable sets is asserted.
-/

open Filter Set Topology
open scoped NNReal ZeroAtInfty
open NormedSpace



open _root_.MarkovProcess.Semigroup


variable {X : Type*} [TopologicalSpace X]












variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

namespace MarkovProcess.PositiveC0ContractiveResolvent

end MarkovProcess.PositiveC0ContractiveResolvent
open MarkovProcess.PositiveC0ContractiveResolvent
theorem solution
    (R : PositiveC0ContractiveResolvent X) (theta : ℝ) (v : C₀(X, ℝ))
    (hR : ∀ mu : PositiveShift, theta < (mu : ℝ) → ∀ x,
      (mu : ℝ) * R.toContractiveResolvent.operator mu v x ≤
        (mu : ℝ) / ((mu : ℝ) - theta) * v x)
    (f : C₀(X, ℝ)) (hfv : ∀ x, f x ≤ v x) (t : NNReal) (x : X) :
    ∫ y, f y ∂R.kernelSemigroup t x ≤ Real.exp (theta * (t : ℝ)) * v x := by
  rw [R.integral_kernelSemigroup]
  calc
    R.toContractiveResolvent.generatedSemigroup t f x ≤
        R.toContractiveResolvent.generatedSemigroup t v x :=
      PositiveC0OperatorMeasure.apply_le_apply_of_isPositive _
        (R.isPositive_generatedSemigroup t) hfv x
    _ ≤ Real.exp (theta * (t : ℝ)) * v x :=
      R.generatedSemigroup_apply_le_exp_mul theta v hR t x
