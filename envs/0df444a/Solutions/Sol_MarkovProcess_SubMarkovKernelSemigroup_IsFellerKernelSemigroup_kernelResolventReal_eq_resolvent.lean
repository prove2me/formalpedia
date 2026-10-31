-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.kernelResolventReal_eq_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:36:36.124184+00:00
-- url     : https://prove2.me/submissions/47e40ca8-7e2d-42e0-9d9a-3758ebd42759

import Definitions.Def_MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
import Definitions.Def_MarkovProcess_V3H_Feller_Semigroup_2cfe612a
import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0Resolvent_c009f25c
import Definitions.Def_MarkovProcess_V3H_Kernel_Resolvent_f63a7282
import Definitions.Def_MarkovProcess_V3H_Semigroup_ResolventGeneration_96f24647
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Metrizable.Urysohn

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The resolvent of a Feller kernel semigroup

The resolvent of the `C₀` semigroup of a Feller kernel semigroup `P`, evaluated at a point, is
the Laplace transform of the transition integrals,

  `R_μ f (x) = ∫₀^∞ e^{-μ t} (∫ f d(P t x)) dt`   (`IsFellerKernelSemigroup.resolvent_apply_apply`),

and the generator domain of the `C₀` semigroup is the range of this resolvent
(`IsFellerKernelSemigroup.mem_generatorDomain_iff_exists_resolvent`), the kernel-side reading of
`Semigroup/Resolvent.lean`.  The shared bounded evaluation functional `c0EvalCLM` commutes with
Bochner integrals in `C₀(α, ℝ)`.  For the Feller kernel
semigroup represented by a positive contractive resolvent `R` (`Kernel/PositiveC0Resolvent.lean`),
the resolvent of its `C₀` semigroup is `R` itself
(`PositiveC0ContractiveResolvent.resolvent_c0Semigroup_kernelSemigroup`).

Conversely, the kernel semigroup represented by that resolvent is the original one
(`IsFellerKernelSemigroup.kernelSemigroup_positiveC0ContractiveResolvent`).

Main results: `IsFellerKernelSemigroup.resolvent_apply_apply`,
`IsFellerKernelSemigroup.positiveC0ContractiveResolvent`,
`IsFellerKernelSemigroup.kernelResolvent_ofReal_eq_resolvent`,
`IsFellerKernelSemigroup.mem_generatorDomain_iff_exists_resolvent`,
`PositiveC0ContractiveResolvent.resolvent_c0Semigroup_kernelSemigroup`.

The bridge to `SubMarkovKernelSemigroup.kernelResolvent` is pointwise on nonnegative observables;
no kernel-valued resolvent is constructed.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal ZeroAtInfty

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [LocallyCompactSpace α] [T2Space α]
variable {P : SubMarkovKernelSemigroup α} (hP : P.IsFellerKernelSemigroup)















end SubMarkovKernelSemigroup

namespace PositiveC0ContractiveResolvent

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (R : PositiveC0ContractiveResolvent X)



end PositiveC0ContractiveResolvent

end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The resolvent of a Feller kernel semigroup

The resolvent of the `C₀` semigroup of a Feller kernel semigroup `P`, evaluated at a point, is
the Laplace transform of the transition integrals,

  `R_μ f (x) = ∫₀^∞ e^{-μ t} (∫ f d(P t x)) dt`   (`IsFellerKernelSemigroup.resolvent_apply_apply`),

and the generator domain of the `C₀` semigroup is the range of this resolvent
(`IsFellerKernelSemigroup.mem_generatorDomain_iff_exists_resolvent`), the kernel-side reading of
`Semigroup/Resolvent.lean`.  The shared bounded evaluation functional `c0EvalCLM` commutes with
Bochner integrals in `C₀(α, ℝ)`.  For the Feller kernel
semigroup represented by a positive contractive resolvent `R` (`Kernel/PositiveC0Resolvent.lean`),
the resolvent of its `C₀` semigroup is `R` itself
(`PositiveC0ContractiveResolvent.resolvent_c0Semigroup_kernelSemigroup`).

Conversely, the kernel semigroup represented by that resolvent is the original one
(`IsFellerKernelSemigroup.kernelSemigroup_positiveC0ContractiveResolvent`).

Main results: `IsFellerKernelSemigroup.resolvent_apply_apply`,
`IsFellerKernelSemigroup.positiveC0ContractiveResolvent`,
`IsFellerKernelSemigroup.kernelResolvent_ofReal_eq_resolvent`,
`IsFellerKernelSemigroup.mem_generatorDomain_iff_exists_resolvent`,
`PositiveC0ContractiveResolvent.resolvent_c0Semigroup_kernelSemigroup`.

The bridge to `SubMarkovKernelSemigroup.kernelResolvent` is pointwise on nonnegative observables;
no kernel-valued resolvent is constructed.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal ZeroAtInfty



variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [LocallyCompactSpace α] [T2Space α]
variable {P : SubMarkovKernelSemigroup α} (hP : P.IsFellerKernelSemigroup)







namespace MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
theorem solution
    (hP : P.IsFellerKernelSemigroup) (μ : Semigroup.PositiveShift)
    (f : C₀(α, ℝ)) (x : α) :
    P.kernelResolventReal (μ : ℝ) (fun y ↦ f y) x =
      hP.c0Semigroup.resolvent μ f x := by
  exact (hP.resolvent_apply_apply μ f x).symm
