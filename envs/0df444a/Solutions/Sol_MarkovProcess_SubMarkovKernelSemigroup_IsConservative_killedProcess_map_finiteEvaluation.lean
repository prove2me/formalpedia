-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.killedProcess_map_finiteEvaluation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:59:53.576678+00:00
-- url     : https://prove2.me/submissions/8978eb9f-7170-4b26-888a-e307333ea315

import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeterySemigroup_149c26e5
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelEquivariance_10113825
import Definitions.Def_MarkovProcess_V3H_Killed_Process_a15f3c27
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
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_killedProcess_map_coordinates_ordered

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

/-- The increasing enumeration of a finite set of times, read at the position of one of its
elements, returns that element. -/
theorem finiteSetTimes_orderIsoOfFin_symm_apply (I : Finset NNReal) (t : I) :
    finiteSetTimes I ((I.orderIsoOfFin rfl).symm t) = (t : NNReal) := by
  show I.orderEmbOfFin rfl ((I.orderIsoOfFin rfl).symm t) = (t : NNReal)
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

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
# The process killed at the exit of an open set, as a law on lifetime paths

For the continuous-path process `Q = continuousProcess P hP` of a conservative semigroup and an
open set `U`, killing each path at its exit time from `U` produces a Markov kernel

  `killedProcess P hP U hU : Kernel U (LifetimePath U)`,

the law of the process started inside `U` and sent to the cemetery when it leaves `U`.  It is the
image of `Q` under `ContinuousPath.killAtExit U`, pulled back to the carrier `U`.

Two marginals are identified here.  The lifetime of the killed process is the exit time
(`killedProcess_map_lifetime`), and its coordinate at a fixed time is the cemetery extension of
the killed transition kernel on `U` (`killedProcess_map_coordinate`): the live part is
`killedKernelOn P hP U hU t x` and the cemetery carries exactly the mass lost by time `t`.

No finite-dimensional distribution of the killed process is identified here, and no Feller or
regularity property of the killed family is claimed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace LifetimePath

/-- Reading a lifetime path at a family of fixed times is measurable. -/
theorem measurable_coordinateFamily {beta : Type*} [TopologicalSpace beta]
    [MeasurableSpace beta] {iota : Type*} (tau : iota → NNReal) :
    Measurable fun omega : LifetimePath beta ↦ fun i ↦ coordinate (tau i) omega :=
  measurable_pi_lambda _ fun i ↦ measurable_coordinate (tau i)

end LifetimePath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

















end SubMarkovKernelSemigroup

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-dimensional distributions of the killed process

For the continuous-path process of a conservative Feller semigroup and an open set `U`, this file
identifies every finite-dimensional distribution of the process killed at the exit of `U`
(`killedProcess P hP U hU` of `Killed/Process.lean`, a law on lifetime paths in the carrier `U`)
with the corresponding finite-dimensional distribution of the **cemetery extension of the killed
semigroup** on `U`:

  `(killedProcess x).map (fun ω ↦ fun i : I ↦ coordinate i ω) =
      finiteSetKernel (cemeterySemigroup (killedSemigroup P hP U hU hFeller hK)) I (alive x)`

(`killedProcess_map_finiteEvaluation`), and, at a strictly increasing family of times, the
corresponding statement for `finiteTimeKernel` (`killedProcess_map_coordinates_ordered`).

The proof is by induction on the number of times, along the recursion of `finiteTimeKernel`.  The
induction step splits the survival event at the first time `t₁`: on `{t₁ < τ_U}` the later
coordinates of the killed path are the coordinates of the killed shifted path
(`coordinate_killAtExit_shift`), and the law of the shifted path is supplied by the restart
statement `continuousProcess_killedEvent_inter_shift` proved here, a form of the Markov property
at `t₁` restricted to the `𝓕_{t₁}`-event `{t₁ < τ_U} ∩ {ω t₁ ∈ B}`; on the complement every
coordinate is the cemetery state, matching the absorbing behaviour of the cemetery
(`finiteTimeKernel_cemeterySemigroup_delta`).  Measures on a finite product are compared on boxes.

No Feller property, strong continuity, or regularity of the killed semigroup is claimed, and no
statement here covers a random time.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

section Dead

variable {beta : Type*} [MeasurableSpace beta] (S : SubMarkovKernelSemigroup beta)



end Dead


section Restart

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)



end Restart


section OrderedMarginals

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)



variable [LocallyCompactSpace alpha]
variable (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)





end OrderedMarginals

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
# Finite-dimensional distributions of the killed process

For the continuous-path process of a conservative Feller semigroup and an open set `U`, this file
identifies every finite-dimensional distribution of the process killed at the exit of `U`
(`killedProcess P hP U hU` of `Killed/Process.lean`, a law on lifetime paths in the carrier `U`)
with the corresponding finite-dimensional distribution of the **cemetery extension of the killed
semigroup** on `U`:

  `(killedProcess x).map (fun ω ↦ fun i : I ↦ coordinate i ω) =
      finiteSetKernel (cemeterySemigroup (killedSemigroup P hP U hU hFeller hK)) I (alive x)`

(`killedProcess_map_finiteEvaluation`), and, at a strictly increasing family of times, the
corresponding statement for `finiteTimeKernel` (`killedProcess_map_coordinates_ordered`).

The proof is by induction on the number of times, along the recursion of `finiteTimeKernel`.  The
induction step splits the survival event at the first time `t₁`: on `{t₁ < τ_U}` the later
coordinates of the killed path are the coordinates of the killed shifted path
(`coordinate_killAtExit_shift`), and the law of the shifted path is supplied by the restart
statement `continuousProcess_killedEvent_inter_shift` proved here, a form of the Markov property
at `t₁` restricted to the `𝓕_{t₁}`-event `{t₁ < τ_U} ∩ {ω t₁ ∈ B}`; on the complement every
coordinate is the cemetery state, matching the absorbing behaviour of the cemetery
(`finiteTimeKernel_cemeterySemigroup_delta`).  Measures on a finite product are compared on boxes.

No Feller property, strong continuity, or regularity of the killed semigroup is claimed, and no
statement here covers a random time.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal








variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)



variable [LocallyCompactSpace alpha]
variable (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)



namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution (I : Finset NNReal) (x : U) :
    (IsConservative.killedProcess P hP U hU x).map
        (fun omega ↦ fun i : I ↦ LifetimePath.coordinate (i : NNReal) omega) =
      finiteSetKernel (cemeterySemigroup (IsConservative.killedSemigroup P hP U hU hFeller hK)) I (Cemetery.alive x) := by
  have hfun : orderedPathToFiniteSet (α := Cemetery U) I ∘
      (fun omega : LifetimePath U ↦ fun j : Fin I.card ↦
        LifetimePath.coordinate (finiteSetTimes I j) omega) =
      fun omega : LifetimePath U ↦ fun t : I ↦ LifetimePath.coordinate (t : NNReal) omega := by
    funext omega t
    show LifetimePath.coordinate (finiteSetTimes I ((I.orderIsoOfFin rfl).symm t)) omega =
      LifetimePath.coordinate (t : NNReal) omega
    rw [finiteSetTimes_orderIsoOfFin_symm_apply]
  rw [finiteSetKernel_eq_map, Kernel.map_apply _ (measurable_orderedPathToFiniteSet I),
    ← IsConservative.killedProcess_map_coordinates_ordered P hP U hU hFeller hK
      (finiteSetTimes I) x,
    Measure.map_map (measurable_orderedPathToFiniteSet I)
      (LifetimePath.measurable_coordinateFamily _), hfun]
