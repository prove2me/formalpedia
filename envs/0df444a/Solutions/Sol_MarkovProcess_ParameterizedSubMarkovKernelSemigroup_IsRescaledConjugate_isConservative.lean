-- Prove2me | solution 1 for MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate.isConservative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:01:38.228093+00:00
-- url     : https://prove2.me/submissions/0ab03df3-fa66-4705-af0e-7fd71fddb2eb

import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcess_caf2584d
import Definitions.Def_MarkovProcess_V3H_Parameterized_Equivariance_252d78e3
import Definitions.Def_MarkovProcess_V3H_Trajectory_Equivariance_2a745e86
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
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
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Rescaled conjugation of finite-time kernels

A sub-Markov kernel semigroup `P'` on a state space `beta` is the *rescaled conjugate* of `P` on
`alpha` when it is obtained from `P` by conjugating the state with a homeomorphism `e : alpha ≃ₜ beta`
and speeding time up by a positive factor `c`, that is `P' t x = ((P (c * t)) (e.symm x)).map e`.

This file transfers the finite-dimensional laws across such a relation.  The main result is
`SubMarkovKernelSemigroup.IsRescaledConjugate.finiteTimeKernel_eq`, which computes every
finite-time kernel of `P'` from the finite-time kernel of `P` at the rescaled times.  Supporting
API: the time-scaling operation `FiniteOrderedTimes.rescale`, the coordinatewise state map
`FiniteOrderedTimes.mapPath`, and two composition-product lemmas, `comap_compProd_prodMkLeft` and
`map_compProd_prodMkLeft_conjugate`, which have no direct Mathlib counterpart.

Nothing here mentions path space; the path-space equivariance statement is in
`MarkovProcess/Trajectory/Equivariance.lean`.  When the state map is an isometry, the intrinsic
Kolmogorov moment criterion also transfers, with the constant multiplied by `c ^ q`
(`IsRescaledConjugate.hasKolmogorovMoments`).
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace MarkovProcess

namespace FiniteOrderedTimes





















end FiniteOrderedTimes

namespace SubMarkovKernelSemigroup



section CompProd

variable {X X' Y Y' Z Z' : Type*} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
  [MeasurableSpace Y'] [MeasurableSpace Z] [MeasurableSpace Z']





end CompProd

section RescaledConjugate

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [TopologicalSpace beta] [MeasurableSpace beta] [BorelSpace beta]



namespace IsRescaledConjugate

variable {P : SubMarkovKernelSemigroup alpha} {P' : SubMarkovKernelSemigroup beta} {e : alpha ≃ₜ beta}
  {c : NNReal}



/-- Conservativity transfers across rescaled conjugacy: no mass is lost by conjugating with a
homeomorphism and speeding up time. -/
theorem isConservative (h : IsRescaledConjugate P P' e c) (hP : P.IsConservative) :
    P'.IsConservative := by
  intro t x
  rw [h t x, Measure.map_apply e.measurable MeasurableSet.univ, Set.preimage_univ]
  exact hP (c * t) (e.symm x)





end IsRescaledConjugate

section Moments

variable {alpha beta : Type*} [PseudoEMetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [PseudoEMetricSpace beta] [MeasurableSpace beta] [BorelSpace beta]
variable {P : SubMarkovKernelSemigroup alpha} {P' : SubMarkovKernelSemigroup beta} {e : alpha ≃ₜ beta}
  {c : NNReal}



end Moments

end RescaledConjugate

end SubMarkovKernelSemigroup

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Equivariance of the parameterized continuous-path process

The equivariance theorem of `MarkovProcess/Trajectory/Equivariance.lean`, restated for a measurably
parameterized family of sub-Markov kernel semigroups.  Here the state map `e` and the time factor
`c` are accompanied by a measurable reparameterization `g` of the parameter space, and the
intertwining hypothesis is fibrewise:
`P' theta t x = ((P (g theta) (c * t)) (e.symm x)).map e`.

The conclusion is a single identity of kernels on `Theta × alpha`: the quenched continuous-path
process of `P'` is the quenched process of `P` pulled back along `(theta, x) ↦ (g theta, e.symm x)`
and pushed forward by `ContinuousPath.rescale e c`.  The proof is fibrewise, through the exact
fibre identity `IsConservative.continuousProcess_apply`.

Main results: `ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate` with its fibre form and
its transfers of conservativity and of the Kolmogorov moment criterion;
`IsConservative.continuousProcess_eq_map_rescale`, its pointwise form and its intrinsic form
`continuousProcess_eq_map_rescale_of_hasKolmogorovMoments`; the covariance corollary
`IsConservative.continuousProcess_covariant` for a family that is its own rescaled conjugate, of
which stationarity and re-gauging covariance of a random environment (`g` the environment shift,
`e` the spatial translation, `c = 1`) are instances.

No scaling limit and no ergodic statement is asserted: the environment map `g`, the factor `c`
and both families are given in advance, and nothing is claimed about the law of the environment.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

section Measurability

variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [TopologicalSpace beta] [MeasurableSpace beta]
  [BorelSpace beta]





namespace IsRescaledConjugate

variable {P : ParameterizedSubMarkovKernelSemigroup Theta alpha}
  {P' : ParameterizedSubMarkovKernelSemigroup Theta beta} {g : Theta → Theta}
  {e : alpha ≃ₜ beta} {c : NNReal}

omit [BorelSpace alpha] [BorelSpace beta] in
/-- The fibre form of the relation: at every parameter the corresponding slices of `P` and `P'`
are rescaled conjugates in the sense of `SubMarkovKernelSemigroup.IsRescaledConjugate`. -/
theorem fibre (h : IsRescaledConjugate P P' g e c) (theta : Theta) :
    SubMarkovKernelSemigroup.IsRescaledConjugate (P.toSubMarkovKernelSemigroup (g theta))
      (P'.toSubMarkovKernelSemigroup theta) e c :=
  fun t x ↦ h theta t x



end IsRescaledConjugate

end Measurability

section Moments

variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [PseudoEMetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [PseudoEMetricSpace beta] [MeasurableSpace beta]
  [BorelSpace beta]
variable {P : ParameterizedSubMarkovKernelSemigroup Theta alpha}
  {P' : ParameterizedSubMarkovKernelSemigroup Theta beta} {g : Theta → Theta}
  {e : alpha ≃ₜ beta} {c : NNReal}



end Moments

section ContinuousProcess

variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [MetricSpace alpha]
  [CompleteSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha] [MetricSpace beta] [CompleteSpace beta]
  [MeasurableSpace beta] [BorelSpace beta] [SecondCountableTopology beta] [Nonempty beta]

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
  (P' : ParameterizedSubMarkovKernelSemigroup Theta beta)
  (hP : P.IsConservative) (hP' : P'.IsConservative)









end ContinuousProcess

end

end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


open MarkovProcess
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Equivariance of the parameterized continuous-path process

The equivariance theorem of `MarkovProcess/Trajectory/Equivariance.lean`, restated for a measurably
parameterized family of sub-Markov kernel semigroups.  Here the state map `e` and the time factor
`c` are accompanied by a measurable reparameterization `g` of the parameter space, and the
intertwining hypothesis is fibrewise:
`P' theta t x = ((P (g theta) (c * t)) (e.symm x)).map e`.

The conclusion is a single identity of kernels on `Theta × alpha`: the quenched continuous-path
process of `P'` is the quenched process of `P` pulled back along `(theta, x) ↦ (g theta, e.symm x)`
and pushed forward by `ContinuousPath.rescale e c`.  The proof is fibrewise, through the exact
fibre identity `IsConservative.continuousProcess_apply`.

Main results: `ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate` with its fibre form and
its transfers of conservativity and of the Kolmogorov moment criterion;
`IsConservative.continuousProcess_eq_map_rescale`, its pointwise form and its intrinsic form
`continuousProcess_eq_map_rescale_of_hasKolmogorovMoments`; the covariance corollary
`IsConservative.continuousProcess_covariant` for a family that is its own rescaled conjugate, of
which stationarity and re-gauging covariance of a random environment (`g` the environment shift,
`e` the spatial translation, `c = 1`) are instances.

No scaling limit and no ergodic statement is asserted: the environment map `g`, the factor `c`
and both families are given in advance, and nothing is claimed about the law of the environment.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal




variable {Theta alpha beta : Type*} [MeasurableSpace Theta] [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [TopologicalSpace beta] [MeasurableSpace beta]
  [BorelSpace beta]






variable {P : ParameterizedSubMarkovKernelSemigroup Theta alpha}
  {P' : ParameterizedSubMarkovKernelSemigroup Theta beta} {g : Theta → Theta}
  {e : alpha ≃ₜ beta} {c : NNReal}



namespace MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate

end MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup.IsRescaledConjugate
theorem solution (h : IsRescaledConjugate P P' g e c) (hP : P.IsConservative) :
    P'.IsConservative :=
  fun theta ↦ (h.fibre theta).isConservative (hP (g theta))
