-- Prove2me | solution 1 for MarkovProcess.PositiveC0ContractiveResolvent.kernelResolvent_le_of_partProcess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:50:57.128105+00:00
-- url     : https://prove2.me/submissions/ffb7b0f6-6555-4e49-a337-d19010dd2f9f

import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
import Definitions.Def_MarkovProcess_V3H_Killed_GluingLocal_6bd3d344
import Definitions.Def_MarkovProcess_V3H_Killed_GluingTransfer_c0e8ad8d
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
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_measurable_killedKernel
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_kernelResolvent_ofReal_eq_resolvent
import Theorems.Thm_MarkovProcess_lintegral_extend_eq_of_forall_zeroAtInfty

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
# Exit times along an exhaustion

For an increasing sequence of open sets `U n` covering the state space (an open exhaustion), the
exit time of a continuous path from `U n` tends to infinity: the path restricted to a compact time
interval has compact range, which lies in some `U N`, and the path therefore stays in `U n` on that
interval for every `n ≥ N` (`tendsto_exitTime_atTop`).  Exit times are monotone in the set
(`exitTime_mono`), as are the truncated exit times.

This is the path-space fact behind nonexplosion arguments: no probability law is involved here.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace MarkovProcess.ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- Exit times are monotone in the set: a path leaves a larger set no earlier. -/
theorem exitTime_mono {U V : Set alpha} (hUV : U ⊆ V) (omega : ContinuousPath alpha) :
    exitTime U omega ≤ exitTime V omega := by
  rw [le_exitTime_iff]
  intro v hv
  exact exitTime_le_of_notMem U omega v (fun h ↦ hv (hUV h))















end MarkovProcess.ContinuousPath


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Potential measures

The resolvent of a transition family at a shift `lam` integrates an observable against the
exponentially weighted time average of its transition kernels.  This file realises that average
as a genuine measure, the `lam`-potential measure

  `laplacePotential lam mu = ∫_0^∞ e^{-lam t} (mu t) dt`,

so that both the kernel resolvent of a sub-Markov kernel semigroup and the killed resolvent of an
open set are integrals against a measure on the state space:
`SubMarkovKernelSemigroup.lintegral_resolventPotential` and
`IsConservative.lintegral_killedPotential`.  Potential measures of sub-Markov families are finite
at every positive shift, with total mass at most `1 / lam`.

Two consequences of the measure form are proved here: the killed resolvent is monotone in the
open set and in the observable (`IsConservative.killedResolvent_mono`), and the kernel resolvent
is measurable in the starting point and continuous along monotone limits of observables
(`SubMarkovKernelSemigroup.measurable_kernelResolvent`,
`SubMarkovKernelSemigroup.kernelResolvent_iSup`).  The kernel resolvent is also additive and
homogeneous on measurable observables (`SubMarkovKernelSemigroup.kernelResolvent_add`,
`SubMarkovKernelSemigroup.kernelResolvent_const_mul`).

No resolvent identity and no topology on the state space are used here.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MarkovProcess











variable {alpha : Type*} [MeasurableSpace alpha]







/-- A potential measure of a family of sub-probability measures is finite at a positive shift. -/
theorem isFiniteMeasure_laplacePotential {lam : ℝ} (hlam : 0 < lam) {mu : ℝ → Measure alpha}
    (hmu : Measurable mu) (hmass : ∀ t, mu t univ ≤ 1) :
    IsFiniteMeasure (laplacePotential lam mu) :=
  ⟨lt_of_le_of_lt (laplacePotential_univ_le hlam hmu hmass) ENNReal.ofReal_lt_top⟩

namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup alpha)







/-- The potential measure of a sub-Markov kernel semigroup is finite at a positive shift. -/
theorem isFiniteMeasure_resolventPotential {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    IsFiniteMeasure (P.resolventPotential lam x) :=
  isFiniteMeasure_laplacePotential hlam (P.measurable_toMeasure_toNNReal x)
    fun _t ↦ P.measure_univ_le_one _ x















section Killed

variable [MetricSpace alpha] [CompleteSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

/-- The killed transition kernels are measurable in time. -/
theorem IsConservative.measurable_killedKernel_toNNReal (x : alpha) :
    Measurable fun t : ℝ ↦ IsConservative.killedKernel P hP U hU (Real.toNNReal t) x :=
  (IsConservative.measurable_killedKernel P hP U hU).comp
    (measurable_real_toNNReal.prodMk measurable_const)



/-- The killed resolvent is integration against the killed potential measure. -/
theorem IsConservative.lintegral_killedPotential (lam : ℝ) {f : alpha → ℝ≥0∞}
    (hf : Measurable f) (x : alpha) :
    ∫⁻ y, f y ∂IsConservative.killedPotential P hP U hU lam x =
      IsConservative.killedResolvent P hP U hU lam f x :=
  lintegral_laplacePotential lam (IsConservative.measurable_killedKernel_toNNReal P hP U hU x) hf

/-- The killed potential measure is finite at a positive shift. -/
theorem IsConservative.isFiniteMeasure_killedPotential {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    IsFiniteMeasure (IsConservative.killedPotential P hP U hU lam x) :=
  isFiniteMeasure_laplacePotential hlam
    (IsConservative.measurable_killedKernel_toNNReal P hP U hU x)
    fun _t ↦ (IsConservative.isSubMarkovKernel_killedKernel P hP U hU _) x

/-- **The killed resolvent is monotone in the open set and in the observable.**  A path leaves a
larger set no earlier, so the killed transition kernels increase with the set. -/
theorem IsConservative.killedResolvent_mono {V : Set alpha} (hV : IsOpen V) (hUV : U ⊆ V)
    (lam : ℝ) {f g : alpha → ℝ≥0∞} (hfg : f ≤ g) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam f x ≤
      IsConservative.killedResolvent P hP V hV lam g x := by
  refine setLIntegral_mono' measurableSet_Ioi fun t _ht ↦ ?_
  refine mul_le_mul' le_rfl (lintegral_mono' ?_ hfg)
  refine Measure.le_iff.mpr fun B hB ↦ ?_
  rw [IsConservative.killedKernel_apply P hP U hU _ x hB,
    IsConservative.killedKernel_apply P hP V hV _ x hB]
  refine measure_mono fun omega homega ↦ ?_
  exact ⟨lt_of_lt_of_le homega.1 (ContinuousPath.exitTime_mono hUV omega), homega.2⟩

end Killed

end SubMarkovKernelSemigroup

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Comparing two local resolvents through the part-process identity

Two positive `C₀`-contractive resolvents on nested locally compact state spaces are compared here
through the process of the larger one.  The data are an open embedding `iota : X₀ → X₁`, the
regularity data (`PositiveC0ContractiveResolvent.OnePointRegular`) which the continuous-path
process of the compactification of `X₁` is formed from, and the part-process identity: the
resolvent of the process of `X₁` killed at the exit from the image of `X₀` is the resolvent
supplied on `X₀`.

The conclusion (`PositiveC0ContractiveResolvent.kernelResolvent_le_of_partProcess`) is that the
kernel resolvent of the smaller space is dominated by the kernel resolvent of the larger one: a
path leaves the smaller domain no later, so it accumulates less.  The identity is supplied for
nonnegative continuous observables vanishing at infinity, which is the form an analytic
construction produces, and is upgraded to all nonnegative measurable observables through the
potential measures.

The regularity data are an explicit hypothesis: positivity, contractivity and the resolvent
identity do not by themselves give the compactified semigroup a continuous-path process.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]



namespace OnePointRegular

variable {R : PositiveC0ContractiveResolvent X}











/-- **The killed resolvent of the compactified process is the kernel resolvent.**  Killing the
process of the compactification at the exit from the live space returns the sub-Markov semigroup
originally represented by the resolvent. -/
theorem killedResolvent_live_eq_kernelResolvent (h : R.OnePointRegular) (lam : ℝ)
    {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    letI := h.metricSpace
    letI := h.completeSpace
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe lam
        (onePointLiveExtension f) (x : OnePoint X) =
      R.kernelSemigroup.kernelResolvent lam f x :=
  R.killedResolvent_onePointLive_eq_kernelResolvent h.rho h.continuous_rho h.rho_pos
    h.lipschitz_rho h.isCompact_superlevel h.kolmogorovRegular lam hf x

end OnePointRegular

/-- For a nonnegative observable vanishing at infinity, the kernel resolvent of the represented
semigroup is the analytic resolvent originally supplied. -/
theorem kernelResolvent_ofReal_eq_operator (R : PositiveC0ContractiveResolvent X)
    (mu : Semigroup.PositiveShift) (f : C₀(X, ℝ)) (hf0 : ∀ y, 0 ≤ f y) (x : X) :
    R.kernelSemigroup.kernelResolvent (mu : ℝ) (fun y ↦ ENNReal.ofReal (f y)) x =
      ENNReal.ofReal (R.toContractiveResolvent.operator mu f x) := by
  rw [R.isFellerKernelSemigroup_kernelSemigroup.kernelResolvent_ofReal_eq_resolvent mu f hf0 x,
    R.resolvent_c0Semigroup_kernelSemigroup]

section Embedding

variable {X₀ X₁ : Type*}





/-- The embedding of a smaller live space into the compactification of a larger one is
injective. -/
theorem injective_compactifiedEmbedding {iota : X₀ → X₁} (hiota : Function.Injective iota) :
    Function.Injective (compactifiedEmbedding iota) :=
  OnePoint.coe_injective.comp hiota

/-- The image of the smaller live space is contained in the live part of the compactification. -/
theorem range_compactifiedEmbedding_subset (iota : X₀ → X₁) :
    Set.range (compactifiedEmbedding iota) ⊆ Set.range ((↑) : X₁ → OnePoint X₁) := by
  rintro _ ⟨y, rfl⟩
  exact ⟨iota y, rfl⟩

/-- An observable of the smaller space, extended by zero off its image in the compactification,
is dominated by the observable of the larger space extended by zero at infinity. -/
theorem extend_compactifiedEmbedding_le (iota : X₀ → X₁) (hiota : Function.Injective iota)
    (g : X₁ → ℝ≥0∞) :
    Function.extend (compactifiedEmbedding iota) (fun z ↦ g (iota z)) 0 ≤
      onePointLiveExtension g := by
  intro w
  by_cases hw : w ∈ Set.range (compactifiedEmbedding iota)
  · obtain ⟨z, rfl⟩ := hw
    rw [(injective_compactifiedEmbedding hiota).extend_apply]
    exact le_of_eq rfl
  · rw [Function.extend_apply' _ _ _ fun hmem ↦ hw hmem]
    exact zero_le

end Embedding

section EmbeddingTopology

variable {X₀ X₁ : Type*} [TopologicalSpace X₀] [TopologicalSpace X₁]





end EmbeddingTopology

section Comparison

variable {X₀ X₁ : Type*}
  [MetricSpace X₀] [LocallyCompactSpace X₀] [SecondCountableTopology X₀]
  [MeasurableSpace X₀] [BorelSpace X₀]
  [MetricSpace X₁] [LocallyCompactSpace X₁] [SecondCountableTopology X₁]
  [MeasurableSpace X₁] [BorelSpace X₁]





end Comparison

end MarkovProcess.PositiveC0ContractiveResolvent


open MarkovProcess
open MarkovProcess.PositiveC0ContractiveResolvent
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Comparing two local resolvents through the part-process identity

Two positive `C₀`-contractive resolvents on nested locally compact state spaces are compared here
through the process of the larger one.  The data are an open embedding `iota : X₀ → X₁`, the
regularity data (`PositiveC0ContractiveResolvent.OnePointRegular`) which the continuous-path
process of the compactification of `X₁` is formed from, and the part-process identity: the
resolvent of the process of `X₁` killed at the exit from the image of `X₀` is the resolvent
supplied on `X₀`.

The conclusion (`PositiveC0ContractiveResolvent.kernelResolvent_le_of_partProcess`) is that the
kernel resolvent of the smaller space is dominated by the kernel resolvent of the larger one: a
path leaves the smaller domain no later, so it accumulates less.  The identity is supplied for
nonnegative continuous observables vanishing at infinity, which is the form an analytic
construction produces, and is upgraded to all nonnegative measurable observables through the
potential measures.

The regularity data are an explicit hypothesis: positivity, contractivity and the resolvent
identity do not by themselves give the compactified semigroup a continuous-path process.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty



open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]









variable {X₀ X₁ : Type*}
  [MetricSpace X₀] [LocallyCompactSpace X₀] [SecondCountableTopology X₀]
  [MeasurableSpace X₀] [BorelSpace X₀]
  [MetricSpace X₁] [LocallyCompactSpace X₁] [SecondCountableTopology X₁]
  [MeasurableSpace X₁] [BorelSpace X₁]



namespace MarkovProcess.PositiveC0ContractiveResolvent

end MarkovProcess.PositiveC0ContractiveResolvent
open MarkovProcess.PositiveC0ContractiveResolvent
theorem solution (R₀ : PositiveC0ContractiveResolvent X₀)
    (R₁ : PositiveC0ContractiveResolvent X₁) (h₁ : R₁.OnePointRegular)
    {iota : X₀ → X₁} (hiota : IsOpenEmbedding iota)
    (hcompat : IsPartProcess R₀ R₁ h₁ hiota)
    {lam : ℝ} (hlam : 0 < lam) {g : X₁ → ℝ≥0∞} (hg : Measurable g) (y : X₀) :
    R₀.kernelSemigroup.kernelResolvent lam (fun z ↦ g (iota z)) y ≤
      R₁.kernelSemigroup.kernelResolvent lam g (iota y) := by
  let := h₁.metricSpace
  let := h₁.completeSpace
  have hj : IsOpenEmbedding (compactifiedEmbedding iota) :=
    isOpenEmbedding_compactifiedEmbedding hiota
  have hjm : MeasurableEmbedding (compactifiedEmbedding iota) := hj.measurableEmbedding
  have hjopen : IsOpen (Set.range (compactifiedEmbedding iota)) :=
    isOpen_range_compactifiedEmbedding hiota
  have hgi : Measurable fun z : X₀ ↦ g (iota z) := hg.comp hiota.continuous.measurable
  have := IsConservative.isFiniteMeasure_killedPotential R₁.onePointKernelSemigroup
    R₁.isConservative_onePointKernelSemigroup (Set.range (compactifiedEmbedding iota))
    hjopen hlam (compactifiedEmbedding iota y)
  have := R₀.kernelSemigroup.isFiniteMeasure_resolventPotential hlam y
  have hc0 : ∀ f : C₀(X₀, ℝ), (∀ z, 0 ≤ f z) →
      ∫⁻ w, Function.extend (compactifiedEmbedding iota)
          (fun z ↦ ENNReal.ofReal (f z)) 0 w
        ∂IsConservative.killedPotential R₁.onePointKernelSemigroup
          R₁.isConservative_onePointKernelSemigroup (Set.range (compactifiedEmbedding iota))
          hjopen lam (compactifiedEmbedding iota y) =
      ∫⁻ z, ENNReal.ofReal (f z) ∂R₀.kernelSemigroup.resolventPotential lam y := by
    intro f hf0
    have hfmeas : Measurable fun z : X₀ ↦ ENNReal.ofReal (f z) :=
      ENNReal.measurable_ofReal.comp f.continuous.measurable
    have hextmeas : Measurable (Function.extend (compactifiedEmbedding iota)
        (fun z ↦ ENNReal.ofReal (f z)) (0 : OnePoint X₁ → ℝ≥0∞)) :=
      hjm.measurable_extend hfmeas measurable_const
    rw [IsConservative.lintegral_killedPotential R₁.onePointKernelSemigroup
        R₁.isConservative_onePointKernelSemigroup (Set.range (compactifiedEmbedding iota))
        hjopen lam hextmeas (compactifiedEmbedding iota y),
      R₀.kernelSemigroup.lintegral_resolventPotential lam hfmeas y,
      hcompat ⟨lam, hlam⟩ f hf0 y,
      ← R₀.kernelResolvent_ofReal_eq_operator ⟨lam, hlam⟩ f hf0 y]
  have hgextmeas : Measurable (Function.extend (compactifiedEmbedding iota)
      (fun z ↦ g (iota z)) (0 : OnePoint X₁ → ℝ≥0∞)) :=
    hjm.measurable_extend hgi measurable_const
  have hstep : IsConservative.killedResolvent R₁.onePointKernelSemigroup
      R₁.isConservative_onePointKernelSemigroup (Set.range (compactifiedEmbedding iota))
      hjopen lam
      (Function.extend (compactifiedEmbedding iota) (fun z ↦ g (iota z)) 0)
      (compactifiedEmbedding iota y) =
        R₀.kernelSemigroup.kernelResolvent lam (fun z ↦ g (iota z)) y := by
    have h := lintegral_extend_eq_of_forall_zeroAtInfty hjm
      (IsConservative.killedPotential R₁.onePointKernelSemigroup
        R₁.isConservative_onePointKernelSemigroup (Set.range (compactifiedEmbedding iota))
        hjopen lam (compactifiedEmbedding iota y))
      (R₀.kernelSemigroup.resolventPotential lam y) hc0 hgi
    rwa [IsConservative.lintegral_killedPotential R₁.onePointKernelSemigroup
        R₁.isConservative_onePointKernelSemigroup (Set.range (compactifiedEmbedding iota))
        hjopen lam hgextmeas (compactifiedEmbedding iota y),
      R₀.kernelSemigroup.lintegral_resolventPotential lam hgi y] at h
  rw [← hstep, ← h₁.killedResolvent_live_eq_kernelResolvent lam hg (iota y)]
  exact IsConservative.killedResolvent_mono R₁.onePointKernelSemigroup
    R₁.isConservative_onePointKernelSemigroup (Set.range (compactifiedEmbedding iota))
    hjopen OnePoint.isOpen_range_coe (range_compactifiedEmbedding_subset iota) lam
    (extend_compactifiedEmbedding_le iota hiota.injective g) (compactifiedEmbedding iota y)
