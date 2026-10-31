-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.ofReal_mul_resolventPotential_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:45:37.855161+00:00
-- url     : https://prove2.me/submissions/cb80ace5-b36a-4dd7-b4f2-1fd4546840c8

import Definitions.Def_MarkovProcess_V3H_Kernel_Resolvent_f63a7282
import Definitions.Def_MarkovProcess_V3H_Killed_GluingPotential_fe882cb0
import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
import Definitions.Def_MarkovProcess_V3H_Path_Exhaustion_e03721f1
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
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
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

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

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MarkovProcess











variable {alpha : Type*} [MeasurableSpace alpha]









namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup alpha)























section Killed

variable [MetricSpace alpha] [CompleteSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)











end Killed

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













variable {alpha : Type*} [MeasurableSpace alpha]










variable (P : SubMarkovKernelSemigroup alpha)











namespace MarkovProcess.SubMarkovKernelSemigroup

end MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup
theorem solution {lam : ℝ} (hlam : 0 < lam) (x : alpha)
    (s : Set alpha) :
    ENNReal.ofReal lam * P.resolventPotential lam x s ≤ 1 := by
  have hmass : P.resolventPotential lam x s ≤ ENNReal.ofReal lam⁻¹ :=
    le_trans (measure_mono (Set.subset_univ s))
      (laplacePotential_univ_le hlam (P.measurable_toMeasure_toNNReal x)
        fun _t ↦ P.measure_univ_le_one _ x)
  calc ENNReal.ofReal lam * P.resolventPotential lam x s
      ≤ ENNReal.ofReal lam * ENNReal.ofReal lam⁻¹ := by gcongr
    _ = 1 := by
        rw [← ENNReal.ofReal_mul hlam.le, mul_inv_cancel₀ hlam.ne', ENNReal.ofReal_one]
