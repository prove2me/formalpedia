-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.coordinate_exitTime_mem_frontier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:32:43.9399+00:00
-- url     : https://prove2.me/submissions/f8b83d72-83e5-4bee-8893-3c3fee5907aa

import Definitions.Def_MarkovProcess_V3H_Lifetime_ExitTime_a7b75085
import Definitions.Def_MarkovProcess_V3H_Path_ClosedSetDetection_642089d8
import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Theorems.Thm_MarkovProcess_ContinuousPath_exitTime_le_iff_mem_hitsSetBy

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











end WithTopValue

section Frontier





end Frontier

section Stopping

variable [MeasurableSpace alpha] [BorelSpace alpha]





end Stopping

end

end ContinuousPath

end MarkovProcess


open MarkovProcess
open MarkovProcess.ContinuousPath
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

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology





variable {alpha : Type*} [PseudoMetricSpace alpha]






namespace MarkovProcess.ContinuousPath

end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
theorem solution (U : Set alpha) (hU : IsOpen U)
    (omega : ContinuousPath alpha) (h0 : omega 0 ∈ U) (hfin : exitTime U omega ≠ ⊤) :
    omega ((exitTime U omega).toNNReal) ∈ frontier U := by
  set tau : NNReal := (exitTime U omega).toNNReal with htau
  have hcoe : (tau : ℝ≥0∞) = exitTime U omega := ENNReal.coe_toNNReal hfin
  have hbefore : ∀ s : NNReal, s < tau → omega s ∈ U := by
    intro s hs
    apply mem_of_lt_exitTime
    rw [← hcoe, ENNReal.coe_lt_coe]
    exact hs
  have hnot : omega tau ∉ U := by
    obtain ⟨s, hs⟩ :=
      (exitTime_le_iff_mem_hitsSetBy U hU tau omega).mp (le_of_eq hcoe.symm)
    have hge : tau ≤ (s : NNReal) := by
      by_contra hlt
      exact hs (hbefore s (lt_of_not_ge hlt))
    have hseq : (s : NNReal) = tau := le_antisymm s.property hge
    rw [← hseq]
    exact hs
  have htau0 : tau ≠ 0 := by
    intro h
    rw [h] at hnot
    exact hnot h0
  have hclosure : omega tau ∈ closure U := by
    have hnebot : (nhdsWithin tau (Set.Iio tau)).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, lt_of_le_of_ne (zero_le : (0 : NNReal) ≤ tau) (Ne.symm htau0)⟩
    have htend : Filter.Tendsto (omega : NNReal → alpha) (nhdsWithin tau (Set.Iio tau))
        (nhds (omega tau)) := (omega.continuous.tendsto tau).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hbefore s hs
  rw [hU.frontier_eq]
  exact ⟨hclosure, hnot⟩
