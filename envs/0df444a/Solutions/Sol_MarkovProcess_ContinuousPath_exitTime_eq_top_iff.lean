-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.exitTime_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:29:02.638793+00:00
-- url     : https://prove2.me/submissions/b43900e0-ab6c-417a-a0c2-e7174d8a4eb4

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
theorem solution (U : Set alpha) (omega : ContinuousPath alpha) :
    exitTime U omega = ⊤ ↔ ∀ t : NNReal, omega t ∈ U := by
  constructor
  · intro htop t
    by_contra ht
    have hle := exitTime_le_of_notMem U omega t ht
    rw [htop, top_le_iff] at hle
    exact ENNReal.coe_ne_top hle
  · intro hmem
    have hempty : {s : ℝ≥0∞ | ∃ t : NNReal, s = (t : ℝ≥0∞) ∧ omega t ∉ U} = ∅ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro u _
      exact fun hu ↦ hu (hmem u)
    rw [exitTime, hempty, sInf_empty]
