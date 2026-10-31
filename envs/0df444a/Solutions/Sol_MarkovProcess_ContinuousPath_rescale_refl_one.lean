-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.rescale_refl_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:34:36.716038+00:00
-- url     : https://prove2.me/submissions/4999052c-5f11-4d6d-aded-279e2fb49526

import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelEquivariance_10113825
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
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
import Theorems.Thm_MarkovProcess_ContinuousPath_rescale_apply

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Equivariance of the continuous-path process

Let `P` be a conservative Feller sub-Markov kernel semigroup on `alpha` with a Kolmogorov-regular
continuous-path process, let `e : alpha ≃ₜ beta` be a homeomorphism onto a second state space and
`c > 0` a time factor, and let `P'` be the rescaled conjugate of `P` on `beta`, that is
`P' t x = ((P (c * t)) (e.symm x)).map e`.  Then the continuous-path process of `P'` is the
continuous-path process of `P` started at `e.symm x` and pushed forward by the path map
`omega ↦ fun t ↦ e (omega (c * t))`.

The proof goes through the uniqueness theorem of `MarkovProcess/Main.lean`: the pushed-forward
kernel is a Markov kernel whose finite-dimensional distributions are computed from the Feller
marginal theorem for `P` at the rescaled times together with the finite-dimensional transfer
`SubMarkovKernelSemigroup.IsRescaledConjugate.finiteSetKernel_eq`.

Main results: `ContinuousPath.rescale` and its continuity and measurability;
`SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation_ordered`,
the marginal of the continuous-path process at an arbitrary strictly increasing finite family of
times; `SubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_rescale` and its
pointwise form `continuousProcess_apply_rescale`; the intrinsic form
`continuousProcess_eq_map_rescale_of_hasKolmogorovMoments`, whose only regularity hypothesis is a
Kolmogorov moment bound on `P` when `e` is an isometry; and the two degenerate corollaries, pure
time rescaling (`continuousProcess_eq_map_timeRescale`) and pure conjugation
(`continuousProcess_eq_map_conjugate`).

No scaling limit is asserted: `c` is a fixed positive factor and both semigroups are given in
advance.  The two state spaces may coincide; the degenerate corollaries are stated on one space.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

namespace ContinuousPath

section Rescale

variable {alpha beta gamma : Type*} [TopologicalSpace alpha] [TopologicalSpace beta]
  [TopologicalSpace gamma]























end Rescale

end ContinuousPath

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)



section TwoSpaces

variable {beta : Type*} [MetricSpace beta] [CompleteSpace beta]
  [MeasurableSpace beta] [BorelSpace beta] [SecondCountableTopology beta] [Nonempty beta]

variable (P' : SubMarkovKernelSemigroup beta) (hP' : P'.IsConservative)







end TwoSpaces

section OneSpace

variable (P' : SubMarkovKernelSemigroup alpha) (hP' : P'.IsConservative)





end OneSpace

end

end SubMarkovKernelSemigroup

end MarkovProcess


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Equivariance of the continuous-path process

Let `P` be a conservative Feller sub-Markov kernel semigroup on `alpha` with a Kolmogorov-regular
continuous-path process, let `e : alpha ≃ₜ beta` be a homeomorphism onto a second state space and
`c > 0` a time factor, and let `P'` be the rescaled conjugate of `P` on `beta`, that is
`P' t x = ((P (c * t)) (e.symm x)).map e`.  Then the continuous-path process of `P'` is the
continuous-path process of `P` started at `e.symm x` and pushed forward by the path map
`omega ↦ fun t ↦ e (omega (c * t))`.

The proof goes through the uniqueness theorem of `MarkovProcess/Main.lean`: the pushed-forward
kernel is a Markov kernel whose finite-dimensional distributions are computed from the Feller
marginal theorem for `P` at the rescaled times together with the finite-dimensional transfer
`SubMarkovKernelSemigroup.IsRescaledConjugate.finiteSetKernel_eq`.

Main results: `ContinuousPath.rescale` and its continuity and measurability;
`SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_finiteEvaluation_ordered`,
the marginal of the continuous-path process at an arbitrary strictly increasing finite family of
times; `SubMarkovKernelSemigroup.IsConservative.continuousProcess_eq_map_rescale` and its
pointwise form `continuousProcess_apply_rescale`; the intrinsic form
`continuousProcess_eq_map_rescale_of_hasKolmogorovMoments`, whose only regularity hypothesis is a
Kolmogorov moment bound on `P` when `e` is an isometry; and the two degenerate corollaries, pure
time rescaling (`continuousProcess_eq_map_timeRescale`) and pure conjugation
(`continuousProcess_eq_map_conjugate`).

No scaling limit is asserted: `c` is a fixed positive factor and both semigroups are given in
advance.  The two state spaces may coincide; the degenerate corollaries are stated on one space.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal




variable {alpha beta gamma : Type*} [TopologicalSpace alpha] [TopologicalSpace beta]
  [TopologicalSpace gamma]









namespace MarkovProcess.ContinuousPath

end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
@[simp]
theorem solution (omega : ContinuousPath alpha) :
    rescale (Homeomorph.refl alpha) 1 omega = omega := by
  ext t
  simp only [rescale_apply, Homeomorph.refl_apply, id_eq, one_mul]
