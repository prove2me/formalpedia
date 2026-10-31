-- Prove2me | solution 1 for MarkovProcess.SubMarkovKernelSemigroup.IsConservative.lintegral_exitTime_eq_killedResolvent_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:37:34.856894+00:00
-- url     : https://prove2.me/submissions/55e5033f-7328-4a17-841a-c1b7c1a5f026

import Definitions.Def_MarkovProcess_V3H_Killed_Resolvent_b61459c1
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
import Theorems.Thm_MarkovProcess_ContinuousPath_survivalSet_ne_top
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_killedResolvent_eq_lintegral

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

/-- The survival set below an infinite extended horizon is the positive half-line. -/
theorem survivalSet_top :
    {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < ⊤} ∩ Set.Ioi 0 = Set.Ioi 0 := by
  ext t
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioi]
  exact and_iff_right ENNReal.coe_lt_top



/-- The time set on which the nonnegative-time coordinate remains below an extended horizon. -/
theorem survivalSet (tau : ℝ≥0∞) :
    {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau} ∩ Set.Ioi 0 =
      if tau = ⊤ then Set.Ioi 0 else Set.Ioo 0 tau.toReal := by
  by_cases htau : tau = ⊤
  · rw [if_pos htau, htau]
    exact survivalSet_top
  · rw [if_neg htau]
    exact survivalSet_ne_top tau htau

end SurvivalSets

variable {alpha : Type*} [PseudoMetricSpace alpha]

section Order











end Order

section WithTopValue











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
# Identifying the expected exit time with a Dirichlet resolvent

The killed resolvent of the constant function one at the shift zero is the expected exit time,

  `E_x τ_U = R^U_0 1 (x)`  (`IsConservative.lintegral_exitTime_eq_killedResolvent_zero`),

and the shift zero is the increasing limit of the positive shifts `1 / (n + 1)`
(`IsConservative.killedResolvent_zero_eq_iSup`).  Both statements are unconditional.

Consumers who identify the killed resolvent at positive shifts with an analytically defined
Dirichlet resolvent `RU` then read the expected exit time off the limit of `RU`
(`IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq`): the identification enters only as a
hypothesis, so nothing here depends on how it is established.  Two one-sided corollaries are
recorded, an upper bound from a uniform upper bound on the limit
(`IsConservative.lintegral_exitTime_le_of_killedResolvent_eq`) and a lower bound on a subset from a
uniform lower bound there (`IsConservative.le_lintegral_exitTime_of_killedResolvent_eq`).

The limit of `RU` enters those statements as a supremum along the shifts `1 / (n + 1)`.  A
consumer who instead has a limit as the shift decreases to zero converts it with
`IsConservative.iSup_eq_of_tendsto_nhdsGT_zero`: the killed resolvent is antitone in the shift, so
the identification makes `RU` antitone on `U` too and the sequence increases to its limit.

The consumer-supplied resolvent and its limit are `ℝ≥0∞`-valued, so no integrability or finiteness
hypothesis appears; a consumer working with real-valued solutions bridges with `ENNReal.ofReal`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section



variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)





variable (RU : ℝ → alpha → ℝ≥0∞) (w : alpha → ℝ≥0∞)









end

end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying the expected exit time with a Dirichlet resolvent

The killed resolvent of the constant function one at the shift zero is the expected exit time,

  `E_x τ_U = R^U_0 1 (x)`  (`IsConservative.lintegral_exitTime_eq_killedResolvent_zero`),

and the shift zero is the increasing limit of the positive shifts `1 / (n + 1)`
(`IsConservative.killedResolvent_zero_eq_iSup`).  Both statements are unconditional.

Consumers who identify the killed resolvent at positive shifts with an analytically defined
Dirichlet resolvent `RU` then read the expected exit time off the limit of `RU`
(`IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq`): the identification enters only as a
hypothesis, so nothing here depends on how it is established.  Two one-sided corollaries are
recorded, an upper bound from a uniform upper bound on the limit
(`IsConservative.lintegral_exitTime_le_of_killedResolvent_eq`) and a lower bound on a subset from a
uniform lower bound there (`IsConservative.le_lintegral_exitTime_of_killedResolvent_eq`).

The limit of `RU` enters those statements as a supremum along the shifts `1 / (n + 1)`.  A
consumer who instead has a limit as the shift decreases to zero converts it with
`IsConservative.iSup_eq_of_tendsto_nhdsGT_zero`: the killed resolvent is antitone in the shift, so
the identification makes `RU` antitone on `U` too and the sequence increases to its limit.

The consumer-supplied resolvent and its limit are `ℝ≥0∞`-valued, so no integrability or finiteness
hypothesis appears; a consumer working with real-valued solutions bridges with `ENNReal.ofReal`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology





variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

namespace MarkovProcess.SubMarkovKernelSemigroup.IsConservative

end MarkovProcess.SubMarkovKernelSemigroup.IsConservative
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
theorem solution (U : Set alpha) (hU : IsOpen U)
    (x : alpha) :
    ∫⁻ omega, ContinuousPath.exitTime U omega ∂(IsConservative.continuousProcess P hP x) =
      IsConservative.killedResolvent P hP U hU 0 (fun _ ↦ 1) x := by
  rw [IsConservative.killedResolvent_eq_lintegral P hP U hU 0 (f := fun _ ↦ (1 : ℝ≥0∞))
    measurable_const x]
  refine lintegral_congr fun omega ↦ ?_
  set tau : ℝ≥0∞ := ContinuousPath.exitTime U omega with htau
  have hS : MeasurableSet {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal)
      measurable_const
  have hinner : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-0 * t)) *
      {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau}.indicator
        (fun _ ↦ (1 : ℝ≥0∞)) t) =
      volume ({t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau} ∩ Set.Ioi 0) := by
    have hpoint : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-0 * t)) *
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau}.indicator
          (fun _ ↦ (1 : ℝ≥0∞)) t =
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau}.indicator
          (fun _ ↦ (1 : ℝ≥0∞)) t := by
      intro t
      simp only [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    rw [lintegral_congr hpoint, lintegral_indicator hS, setLIntegral_one,
      Measure.restrict_apply hS]
  rw [hinner, ContinuousPath.survivalSet tau]
  by_cases htop : tau = ⊤
  · rw [if_pos htop, htop, Real.volume_Ioi]
  · rw [if_neg htop, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal htop]
