-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.exitLaw_apply_compl_frontier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:51:11.267777+00:00
-- url     : https://prove2.me/submissions/ebeb22a9-adee-4286-a856-969b551b2efc

import Definitions.Def_MarkovProcess_V3H_Path_ExitTimeShift_63f55a50
import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Trajectory_DiscountedDynkin_a0eb8ff0
import Definitions.Def_MarkovProcess_V3H_Trajectory_ExitLaw_2add356d
import Definitions.Def_MarkovProcess_V3H_Trajectory_StoppingLtTop_f2bd051e
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
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
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
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
import Theorems.Thm_MarkovProcess_ContinuousPath_coordinate_exitTime_mem_frontier
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_ae_eval_zero_eq

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exit times of open sets on continuous-path space

For an open set `U` this file studies `ContinuousPath.exitTime U`, the first time a continuous
path leaves `U`, in the `WithTop`-valued form `ContinuousPath.exitTimeTop U` demanded by
Mathlib's stopping-time convention.  The main consumer facts are: the exit time is a stopping
time for the canonical filtration; it is finite exactly when the path leaves `U` at some time;
at a finite exit time the path sits on the frontier of `U` when it started inside; and its
truncation `exitTimeTrunc U K` at a deterministic horizon is an `NNReal`-valued stopping time,
which is the form the finite-stopping-time API of this library consumes.  The generic time-set
identities `survivalSet_top`, `survivalSet_ne_top`, and `survivalSet` identify the positive real
times below an extended nonnegative horizon.

The route is the closed-set detection of `Path/ClosedSetDetection.lean`: the event
`{exitTime ≤ t}` is the event of hitting the closed set `Uᶜ` by time `t`, because a path that
stays in the open set `U` throughout `[0, t]` stays in it slightly beyond `t`.

This file constructs no probability law and proves no probabilistic statement; in particular it
does not claim that the exit time is almost surely finite for any process.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MarkovProcess

namespace ContinuousPath

noncomputable section

section SurvivalSets







end SurvivalSets

variable {alpha : Type*} [PseudoMetricSpace alpha]

section Order











end Order

section WithTopValue



/-- The `WithTop`-valued exit time is the exit time. -/
theorem exitTimeTop_apply (U : Set alpha) (omega : ContinuousPath alpha) :
    exitTimeTop U omega = exitTime U omega := rfl







end WithTopValue

section Frontier





end Frontier

section Stopping

variable [MeasurableSpace alpha] [BorelSpace alpha]





end Stopping

end

end ContinuousPath

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Stopped laws and exit distributions

For the continuous-path process `Q` of a conservative semigroup, this file packages as kernels the
laws that the strong Markov property and the boundary value problems of a domain consume:

* `stoppedLaw T hT : Kernel alpha (NNReal × alpha)`, the joint law of a finite stopping time and
  the position at that time, with its two marginals;
* `exitLawTrunc U hU K : Kernel alpha alpha`, the law of the position at the exit time of an open
  set `U` truncated at the horizon `K`; from a starting point in `U` it lives on the closure of `U`
  (`exitLawTrunc_apply_compl_closure`);
* `exitLaw U hU : Kernel alpha alpha`, the exit distribution (harmonic measure): the law of the
  position at the exit time on the event that the path leaves `U`; its total mass is the exit
  probability, and from a starting point in `U` it lives on the frontier of `U`
  (`exitLaw_apply_compl_frontier`).

The harmonic representation of `Trajectory/HarmonicRepresentation.lean` reads, in these terms,
`∫ f d(exitLawTrunc U hU K x) = f x` whenever `L f = 0` on `U`
(`integral_exitLawTrunc_eq_of_generator_eq_zero`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- The finite value of a finite exit time, read through `untopD`, is its `toNNReal`. -/
theorem untopD_exitTimeTop_eq_toNNReal (U : Set alpha) (omega : ContinuousPath alpha)
    (h : exitTime U omega ≠ ⊤) :
    (exitTimeTop U omega).untopD 0 = (exitTime U omega).toNNReal := by
  rw [exitTimeTop_apply, ← ENNReal.coe_toNNReal h]
  rfl

variable [MeasurableSpace alpha] [BorelSpace alpha]





/-- The position at the exit time of an open set, on the event that the path leaves it, is
measurable. -/
theorem measurable_eval_untopD_exitTimeTop (U : Set alpha) (hU : IsOpen U) :
    Measurable fun omega : ContinuousPath alpha ↦ omega ((exitTimeTop U omega).untopD 0) :=
  measurable_eval_untopD_stoppingTime _ (isStoppingTime_exitTime U hU)

end ContinuousPath

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)

section StoppedLaw

variable (T : ContinuousPath alpha → NNReal)
  (hT : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha))
    (fun omega ↦ (T omega : WithTop NNReal)))











end StoppedLaw

section ExitLaw

variable (U : Set alpha) (hU : IsOpen U)













/-- The exit distribution evaluated on a measurable set. -/
theorem IsConservative.exitLaw_apply (x : alpha) {B : Set alpha} (hB : MeasurableSet B) :
    IsConservative.exitLaw hP U hU x B =
      IsConservative.continuousProcess P hP x
        {omega | ContinuousPath.exitTime U omega < ⊤ ∧
          omega ((ContinuousPath.exitTimeTop U omega).untopD 0) ∈ B} := by
  rw [IsConservative.exitLaw,
    Kernel.map_apply' _ (ContinuousPath.measurable_eval_untopD_exitTimeTop U hU) _ hB,
    Kernel.restrict_apply' _ _ _ ((ContinuousPath.measurable_eval_untopD_exitTimeTop U hU) hB)]
  congr 1
  ext omega
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  exact and_comm





variable [LocallyCompactSpace alpha]



end ExitLaw

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
# Stopped laws and exit distributions

For the continuous-path process `Q` of a conservative semigroup, this file packages as kernels the
laws that the strong Markov property and the boundary value problems of a domain consume:

* `stoppedLaw T hT : Kernel alpha (NNReal × alpha)`, the joint law of a finite stopping time and
  the position at that time, with its two marginals;
* `exitLawTrunc U hU K : Kernel alpha alpha`, the law of the position at the exit time of an open
  set `U` truncated at the horizon `K`; from a starting point in `U` it lives on the closure of `U`
  (`exitLawTrunc_apply_compl_closure`);
* `exitLaw U hU : Kernel alpha alpha`, the exit distribution (harmonic measure): the law of the
  position at the exit time on the event that the path leaves `U`; its total mass is the exit
  probability, and from a starting point in `U` it lives on the frontier of `U`
  (`exitLaw_apply_compl_frontier`).

The harmonic representation of `Trajectory/HarmonicRepresentation.lean` reads, in these terms,
`∫ f d(exitLawTrunc U hU K x) = f x` whenever `L f = 0` on `U`
(`integral_exitLawTrunc_eq_of_generator_eq_zero`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ZeroAtInfty




variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable {P : SubMarkovKernelSemigroup alpha} (hP : P.IsConservative)



variable (U : Set alpha) (hU : IsOpen U)

















namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution (hK : P.KolmogorovRegular hP) {x : alpha}
    (hx : x ∈ U) : IsConservative.exitLaw hP U hU x (frontier U)ᶜ = 0 := by
  rw [IsConservative.exitLaw_apply hP U hU x isClosed_frontier.measurableSet.compl]
  refine measure_mono_null (fun omega homega ↦ ?_) ((ae_iff).mp
    (IsConservative.ae_eval_zero_eq hP hK x))
  intro h0
  obtain ⟨hfin, hnot⟩ := homega
  rw [ContinuousPath.untopD_exitTimeTop_eq_toNNReal U omega hfin.ne] at hnot
  exact hnot (ContinuousPath.coordinate_exitTime_mem_frontier U hU omega (h0 ▸ hx) hfin.ne)
