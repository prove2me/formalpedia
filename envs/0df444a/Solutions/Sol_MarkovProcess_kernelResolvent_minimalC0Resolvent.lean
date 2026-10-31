-- Prove2me | solution 1 for MarkovProcess.kernelResolvent_minimalC0Resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:55:52.463829+00:00
-- url     : https://prove2.me/submissions/559eea49-fa4c-4c3c-914e-b8e7805132f5

import Definitions.Def_MarkovProcess_V3H_Kernel_OnePointKilled_a181fa20
import Definitions.Def_MarkovProcess_V3H_Killed_GluingC0_186c1e9f
import Definitions.Def_MarkovProcess_V3H_Killed_GluingLocal_6bd3d344
import Definitions.Def_MarkovProcess_V3H_Killed_GluingMeasure_1a481231
import Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
import Definitions.Def_MarkovProcess_V3H_Killed_GluingRealResolvent_55a9f996
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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_kernelResolvent_ofReal_eq_resolvent
import Theorems.Thm_MarkovProcess_lintegral_extend_eq_of_forall_zeroAtInfty
import Theorems.Thm_MarkovProcess_lintegral_minimalPotential

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


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The potential measure of the supremum resolvent

Additivity and continuity along monotone limits make the supremum resolvent countably additive
on measurable observables (`minimalResolvent_tsum`), so at a positive shift it is the integral
against a finite measure on the state space, the potential measure `minimalPotential`
(`lintegral_minimalPotential`, `isFiniteMeasure_minimalPotential`).

This is the form in which the supremum resolvent is compared with the kernel resolvent of a
transition semigroup: an identity tested on continuous observables vanishing at infinity extends
to all nonnegative measurable observables through the two potential measures.

Monotonicity of the transported resolvents in the index is a bare hypothesis throughout.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MarkovProcess

variable {alpha : Type*} [MeasurableSpace alpha] {X : ℕ → Type*}
  [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)







/-- The potential measure of a measurable set is the supremum resolvent of its indicator. -/
theorem minimalPotential_apply (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) (x : alpha) {S : Set alpha} (hS : MeasurableSet S) :
    minimalPotential R emb hemb hmono hlam x S =
      minimalResolvent R emb lam (S.indicator fun _ ↦ 1) x :=
  Measure.ofMeasurable_apply S hS



/-- The potential measure is finite at a positive shift, with mass at most `1 / lam`. -/
theorem isFiniteMeasure_minimalPotential (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    IsFiniteMeasure (minimalPotential R emb hemb hmono hlam x) := by
  refine ⟨?_⟩
  rw [minimalPotential_apply R emb hemb hmono hlam x MeasurableSet.univ, Set.indicator_univ]
  exact lt_of_le_of_lt
    (minimalResolvent_one_le R emb (fun m ↦ (hemb m).injective) hlam x) ENNReal.ofReal_lt_top

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The supremum resolvent on bounded real observables

The supremum resolvent of `Killed/GluingMinimal.lean` acts on nonnegative extended-real
observables.  On a bounded real observable it acts through the positive and negative parts,

  `R_lam f := (R_lam f⁺).toReal - (R_lam f⁻).toReal`   (`minimalResolventReal`),

which is well defined because a uniform bound `D` for the observable bounds both values by
`D / lam` (`Killed/GluingLinearity.lean`).  The real form is measurable in the starting point
(`measurable_minimalResolventReal`), obeys the same uniform bound
(`abs_minimalResolventReal_le`), is additive and real homogeneous on bounded measurable
observables (`minimalResolventReal_add`, `minimalResolventReal_smul`), satisfies the
resolvent equation (`minimalResolventReal_resolventEquation`), and commutes at two shifts
(`minimalResolventReal_comm`).

Additivity, and with it the resolvent equation, is available exactly when the transported
resolvents are monotone in the index; that monotonicity is a bare hypothesis here.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess

variable {alpha : Type*} [MeasurableSpace alpha] {X : ℕ → Type*}
  [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)



section Bounds








end Bounds

section Elementary




/-- On a bounded nonnegative observable the extended-real value is recovered from the real
form. -/
theorem ofReal_minimalResolventReal (hemb : ∀ m, MeasurableEmbedding (emb m))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} {D : ℝ} (hfD : ∀ y, |f y| ≤ D)
    (hf0 : ∀ y, 0 ≤ f y) (x : alpha) :
    ENNReal.ofReal (minimalResolventReal R emb lam f x) =
      minimalResolvent R emb lam (fun y ↦ ENNReal.ofReal (f y)) x := by
  rw [minimalResolventReal_of_nonneg R emb hemb hlam hf0 x,
    ENNReal.ofReal_toReal (minimalResolvent_ofReal_ne_top R emb hemb hlam hfD x)]













end Elementary

section Additive














end Additive

section ResolventEquation








end ResolventEquation

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The supremum resolvent as a positive `C₀`-contractive resolvent

The supremum resolvent of a family of local resolvents acts on bounded measurable observables.
Two properties of its action on `C₀` are analytic and are hypotheses here: that the value on an
observable vanishing at infinity is again continuous and vanishing at infinity, supplied as a map
`T` together with the identification `hT` of its values, and that the range of `T` is dense.
Additivity, real homogeneity, the operator bound `1 / lam`, positivity and the resolvent identity
are then proved from the extended-real theory, and assemble the supremum resolvent into a
`PositiveC0ContractiveResolvent` (`minimalC0Resolvent`).

The semigroup which that resolvent generates is represented by a sub-Markov kernel semigroup, and
its kernel resolvent is the supremum resolvent again, on every nonnegative measurable observable
(`kernelResolvent_minimalC0Resolvent`): the two potential measures agree on continuous
observables vanishing at infinity, hence everywhere.

If in addition the shift times the supremum resolvent of the constant observable one is one, the
represented semigroup loses no mass (`isConservative_kernelSemigroup_minimalC0Resolvent`), and
the compactified process started at any point almost surely never reaches the added point
(`ae_exitTime_eq_top_minimalC0Resolvent`).  No kernel into the continuous paths of the state
space is produced from that statement.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

namespace MarkovProcess

variable {alpha : Type*} [MetricSpace alpha] [LocallyCompactSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  {X : ℕ → Type*} [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)



section Operator

variable (T : Semigroup.PositiveShift → C₀(alpha, ℝ) → C₀(alpha, ℝ))







omit [LocallyCompactSpace alpha] [SecondCountableTopology alpha] in
/-- The operator of the minimal `C₀` resolvent is the given family, pointwise. -/
@[simp] theorem minimalC0Resolvent_operator_apply (hemb : ∀ m, MeasurableEmbedding (emb m))
    (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
      Monotone fun m ↦ localResolvent R emb m nu h y)
    (hT : ∀ (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) (x : alpha),
      T nu f x = minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x)
    (hdense : ∀ nu, DenseRange (T nu)) (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ))
    (x : alpha) :
    (minimalC0Resolvent R emb T hemb hmono hT hdense).toContractiveResolvent.operator nu f x =
      minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x :=
  hT nu f x

end Operator

section Identification

variable (T : Semigroup.PositiveShift → C₀(alpha, ℝ) → C₀(alpha, ℝ))
  (hemb : ∀ m, MeasurableEmbedding (emb m))
  (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
    Monotone fun m ↦ localResolvent R emb m nu h y)
  (hT : ∀ (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) (x : alpha),
    T nu f x = minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x)
  (hdense : ∀ nu, DenseRange (T nu))

omit [MetricSpace alpha] [LocallyCompactSpace alpha] [SecondCountableTopology alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] in
private theorem extend_id (g : alpha → ℝ≥0∞) :
    Function.extend (id : alpha → alpha) g 0 = g := by
  funext y
  exact Function.Injective.extend_apply Function.injective_id g 0 y



end Identification

section Conservativity

variable (T : Semigroup.PositiveShift → C₀(alpha, ℝ) → C₀(alpha, ℝ))
  (hemb : ∀ m, MeasurableEmbedding (emb m))
  (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
    Monotone fun m ↦ localResolvent R emb m nu h y)
  (hT : ∀ (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) (x : alpha),
    T nu f x = minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x)
  (hdense : ∀ nu, DenseRange (T nu))





end Conservativity

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The supremum resolvent as a positive `C₀`-contractive resolvent

The supremum resolvent of a family of local resolvents acts on bounded measurable observables.
Two properties of its action on `C₀` are analytic and are hypotheses here: that the value on an
observable vanishing at infinity is again continuous and vanishing at infinity, supplied as a map
`T` together with the identification `hT` of its values, and that the range of `T` is dense.
Additivity, real homogeneity, the operator bound `1 / lam`, positivity and the resolvent identity
are then proved from the extended-real theory, and assemble the supremum resolvent into a
`PositiveC0ContractiveResolvent` (`minimalC0Resolvent`).

The semigroup which that resolvent generates is represented by a sub-Markov kernel semigroup, and
its kernel resolvent is the supremum resolvent again, on every nonnegative measurable observable
(`kernelResolvent_minimalC0Resolvent`): the two potential measures agree on continuous
observables vanishing at infinity, hence everywhere.

If in addition the shift times the supremum resolvent of the constant observable one is one, the
represented semigroup loses no mass (`isConservative_kernelSemigroup_minimalC0Resolvent`), and
the compactified process started at any point almost surely never reaches the added point
(`ae_exitTime_eq_top_minimalC0Resolvent`).  No kernel into the continuous paths of the state
space is produced from that statement.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty



variable {alpha : Type*} [MetricSpace alpha] [LocallyCompactSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  {X : ℕ → Type*} [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)] [∀ m, BorelSpace (X m)]

variable (R : ∀ m, PositiveC0ContractiveResolvent (X m)) (emb : ∀ m, X m → alpha)





variable (T : Semigroup.PositiveShift → C₀(alpha, ℝ) → C₀(alpha, ℝ))
  (hemb : ∀ m, MeasurableEmbedding (emb m))
  (hmono : ∀ nu > 0, ∀ {h : alpha → ℝ≥0∞}, Measurable h → ∀ y,
    Monotone fun m ↦ localResolvent R emb m nu h y)
  (hT : ∀ (nu : Semigroup.PositiveShift) (f : C₀(alpha, ℝ)) (x : alpha),
    T nu f x = minimalResolventReal R emb (nu : ℝ) (fun y ↦ f y) x)
  (hdense : ∀ nu, DenseRange (T nu))



namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ≥0∞}
    (hf : Measurable f) (x : alpha) :
    (minimalC0Resolvent R emb T hemb hmono hT hdense).kernelSemigroup.kernelResolvent lam f x =
      minimalResolvent R emb lam f x := by
  have := (minimalC0Resolvent R emb T hemb hmono hT
    hdense).kernelSemigroup.isFiniteMeasure_resolventPotential hlam x
  have := isFiniteMeasure_minimalPotential R emb hemb hmono hlam x
  have hc0 : ∀ g : C₀(alpha, ℝ), (∀ y, 0 ≤ g y) →
      ∫⁻ z, Function.extend (id : alpha → alpha) (fun y ↦ ENNReal.ofReal (g y)) 0 z
          ∂(minimalC0Resolvent R emb T hemb hmono hT hdense).kernelSemigroup.resolventPotential
            lam x =
        ∫⁻ y, ENNReal.ofReal (g y) ∂minimalPotential R emb hemb hmono hlam x := by
    intro g hg0
    have hgmeas : Measurable fun y ↦ ENNReal.ofReal (g y) :=
      ENNReal.measurable_ofReal.comp g.continuous.measurable
    rw [extend_id, (minimalC0Resolvent R emb T hemb hmono hT
        hdense).kernelSemigroup.lintegral_resolventPotential lam hgmeas x,
      lintegral_minimalPotential R emb hemb hmono hlam x hgmeas,
      (minimalC0Resolvent R emb T hemb hmono hT hdense).kernelResolvent_ofReal_eq_operator
        ⟨lam, hlam⟩ g hg0 x,
      minimalC0Resolvent_operator_apply R emb T hemb hmono hT hdense ⟨lam, hlam⟩ g x]
    exact ofReal_minimalResolventReal R emb hemb hlam (abs_le_norm_c0 g) hg0 x
  have hmain := lintegral_extend_eq_of_forall_zeroAtInfty (i := (id : alpha → alpha))
    MeasurableEmbedding.id
    ((minimalC0Resolvent R emb T hemb hmono hT hdense).kernelSemigroup.resolventPotential lam x)
    (minimalPotential R emb hemb hmono hlam x) hc0 hf
  rwa [extend_id, (minimalC0Resolvent R emb T hemb hmono hT
      hdense).kernelSemigroup.lintegral_resolventPotential lam hf x,
    lintegral_minimalPotential R emb hemb hmono hlam x hf] at hmain
