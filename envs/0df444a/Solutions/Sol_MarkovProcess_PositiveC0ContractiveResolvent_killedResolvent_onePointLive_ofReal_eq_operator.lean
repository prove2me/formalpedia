-- Prove2me | solution 1 for MarkovProcess.PositiveC0ContractiveResolvent.killedResolvent_onePointLive_ofReal_eq_operator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:51:02.485784+00:00
-- url     : https://prove2.me/submissions/6a0b38cf-3489-4793-b8aa-ae830eb65d93

import Definitions.Def_MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKolmogorov_a805d493
import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Definitions.Def_MarkovProcess_V3H_Killed_Semigroup_8f8ac7bc
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Definitions.Def_MarkovProcess_V3H_Trajectory_ExitLaw_2add356d
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
import Theorems.Thm_MarkovProcess_PositiveC0ContractiveResolvent_killedResolvent_onePointLive_eq_kernelResolvent
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_kernelResolvent_ofReal_eq_resolvent

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Feller property of kernels represented by positive `C₀` semigroups

The kernel semigroup represented by a strongly continuous semigroup of positive contractions
recovers the original operators on `C₀` and therefore satisfies the existing Feller interface.
This file makes no conservativity, stochastic-process, or Hunt-process claim.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ZeroAtInfty

namespace MarkovProcess.PositiveC0SemigroupFeller

open MarkovProcess.Semigroup

variable {α : Type*} [TopologicalSpace α] [T2Space α] [LocallyCompactSpace α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]

variable (S : StronglyContinuousContractionSemigroup C₀(α, ℝ))
  (hS : ∀ t, PositiveC0OperatorMeasure.IsPositive (S t))











/-- Packaging the represented Feller kernel semigroup recovers the original `C₀` semigroup. -/
theorem c0Semigroup_kernelSemigroup :
    (isFellerKernelSemigroup_kernelSemigroup S hS).c0Semigroup = S := by
  apply StronglyContinuousContractionSemigroup.ext
  intro t
  rw [SubMarkovKernelSemigroup.IsFellerKernelSemigroup.c0Semigroup]
  exact kernelSemigroup_c0Operator S hS _ t

end MarkovProcess.PositiveC0SemigroupFeller


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Positive `C₀` resolvents and their Feller kernels

A positive contractive resolvent on `C₀` canonically generates a strongly continuous semigroup
of positive contractions.  The existing pointwise Riesz construction then represents that
semigroup by a sub-Markov kernel semigroup and identifies its `C₀` operators exactly.

The package in this file starts from the resolvent identity, the Hille--Yosida bound, dense range,
and positivity of the actual shifted resolvents.  It assumes neither a semigroup nor a kernel.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ZeroAtInfty

noncomputable section

namespace MarkovProcess

open MarkovProcess.Semigroup

variable (X : Type*) [TopologicalSpace X]



namespace PositiveC0ContractiveResolvent

variable {X : Type*} [TopologicalSpace X]









variable (R : PositiveC0ContractiveResolvent X)





section Kernel

variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]







/-- Repackaging the represented Feller kernels recovers the generated `C₀` semigroup. -/
theorem c0Semigroup_kernelSemigroup :
    R.isFellerKernelSemigroup_kernelSemigroup.c0Semigroup =
      R.toContractiveResolvent.generatedSemigroup :=
  PositiveC0SemigroupFeller.c0Semigroup_kernelSemigroup
    R.toContractiveResolvent.generatedSemigroup R.isPositive_generatedSemigroup

end Kernel

end PositiveC0ContractiveResolvent

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The semigroup generated by the resolvent of a semigroup

The two halves of the Hille–Yosida correspondence close up: the contractive resolvent of a
strongly continuous contraction semigroup `S` (`Semigroup/Resolvent.lean`) generates, through
`Semigroup/Generation.lean`, a semigroup whose generator is the generator of `S`
(`Semigroup/GeneratorResolvent.lean`, `generatorDomain_eq_range_resolvent`), and a strongly
continuous contraction semigroup is determined by its generator
(`Semigroup/GeneratorUniqueness.lean`).  Hence the generated semigroup is `S` itself
(`generatedSemigroup_toContractiveResolvent`).

Conversely the resolvent of the semigroup generated by a contractive resolvent `R` is `R`
(`ContractiveResolvent.resolvent_generatedSemigroup`), because both invert `μ − L` and `μ − L` is
injective.

Main results: `generatorDomain_generatedSemigroup_toContractiveResolvent`,
`generatedSemigroup_toContractiveResolvent`, `ContractiveResolvent.resolvent_generatedSemigroup`,
`ContractiveResolvent.toContractiveResolvent_generatedSemigroup`.

Nothing is asserted about resolvents that do not come from a semigroup; for those, the
generation theorem of `Semigroup/Generation.lean` is the statement.
-/

open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (S : StronglyContinuousContractionSemigroup E)





end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

namespace MarkovProcess.Semigroup.ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The resolvent of the generated semigroup is the given resolvent.** -/
theorem resolvent_generatedSemigroup (R : ContractiveResolvent E) (μ : PositiveShift) :
    R.generatedSemigroup.resolvent μ = R.operator μ := by
  ext y
  apply R.generatedSemigroup.eq_of_smul_sub_generator_eq μ.2
    ⟨R.generatedSemigroup.resolvent μ y, R.generatedSemigroup.resolvent_mem_generatorDomain μ y⟩
    ⟨R.operator μ y, R.operator_mem_generatorDomain μ y⟩
  rw [R.generatedSemigroup.generator_resolvent μ y, R.generator_operator_apply μ y]
  simp only [sub_sub_cancel]



end MarkovProcess.Semigroup.ContractiveResolvent


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

/-- **The resolvent of the represented process is the given resolvent.** -/
theorem resolvent_c0Semigroup_kernelSemigroup (μ : Semigroup.PositiveShift) :
    R.isFellerKernelSemigroup_kernelSemigroup.c0Semigroup.resolvent μ =
      R.toContractiveResolvent.operator μ := by
  rw [R.c0Semigroup_kernelSemigroup, Semigroup.ContractiveResolvent.resolvent_generatedSemigroup]

end PositiveC0ContractiveResolvent

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Killing the one-point process at infinity

This file identifies the continuous process of the one-point extension of a positive
`C₀`-contractive resolvent with the process killed on leaving its live part.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]





variable [LocallyCompactSpace alpha]







end MarkovProcess.SubMarkovKernelSemigroup

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

































end MarkovProcess.PositiveC0ContractiveResolvent


open MarkovProcess
open MarkovProcess.PositiveC0ContractiveResolvent
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Killing the one-point process at infinity

This file identifies the continuous process of the one-point extension of a positive
`C₀`-contractive resolvent with the process killed on leaving its live part.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty




open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]





























namespace MarkovProcess.PositiveC0ContractiveResolvent

end MarkovProcess.PositiveC0ContractiveResolvent
open MarkovProcess.PositiveC0ContractiveResolvent
theorem solution
    (R : PositiveC0ContractiveResolvent X) (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (hK : letI :=
        OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      letI : CompleteSpace (OnePoint X) :=
        completeSpace_of_isComplete_univ isCompact_univ.isComplete
      R.onePointKernelSemigroup.KolmogorovRegular
      R.isConservative_onePointKernelSemigroup)
    (mu : Semigroup.PositiveShift) (f : C₀(X, ℝ)) (hf0 : ∀ y, 0 ≤ f y) (x : X) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint X) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe (mu : ℝ)
        (onePointLiveExtension fun y ↦ ENNReal.ofReal (f y)) (x : OnePoint X) =
      ENNReal.ofReal (R.toContractiveResolvent.operator mu f x) := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let : CompleteSpace (OnePoint X) :=
    completeSpace_of_isComplete_univ isCompact_univ.isComplete
  calc
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe (mu : ℝ)
        (onePointLiveExtension fun y ↦ ENNReal.ofReal (f y)) (x : OnePoint X) =
      R.kernelSemigroup.kernelResolvent (mu : ℝ) (fun y ↦ ENNReal.ofReal (f y)) x :=
        R.killedResolvent_onePointLive_eq_kernelResolvent rho hrho_cont hrho_pos
          hrho_lipschitz hrho_compact hK mu
          (ENNReal.measurable_ofReal.comp f.continuous.measurable) x
    _ = ENNReal.ofReal
        (R.isFellerKernelSemigroup_kernelSemigroup.c0Semigroup.resolvent mu f x) :=
      R.isFellerKernelSemigroup_kernelSemigroup.kernelResolvent_ofReal_eq_resolvent
        mu f hf0 x
    _ = ENNReal.ofReal (R.toContractiveResolvent.operator mu f x) := by
      rw [R.resolvent_c0Semigroup_kernelSemigroup]
