-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.exitTime_le_iff_mem_hitsSetBy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:29:11.071991+00:00
-- url     : https://prove2.me/submissions/bde1fe23-a38f-43ea-ac99-5a3592d2dec2

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
theorem solution (U : Set alpha) (hU : IsOpen U) (t : NNReal)
    (omega : ContinuousPath alpha) :
    exitTime U omega ≤ (t : ℝ≥0∞) ↔ omega ∈ hitsSetBy t Uᶜ := by
  constructor
  · intro hle
    by_contra hnot
    have hall : ∀ s : NNReal, s ≤ t → omega s ∈ U := by
      intro s hs
      by_contra hsU
      exact hnot ⟨⟨s, Set.mem_Iic.mpr hs⟩, hsU⟩
    have hVopen : IsOpen ((omega : NNReal → alpha) ⁻¹' U) := hU.preimage omega.continuous
    have htV : t ∈ (omega : NNReal → alpha) ⁻¹' U := hall t le_rfl
    obtain ⟨delta, hdelta, hball⟩ := Metric.isOpen_iff.mp hVopen t htV
    have hhalf : (0 : ℝ) < delta / 2 := by linarith only [hdelta]
    set d : NNReal := ⟨delta / 2, le_of_lt hhalf⟩ with hd
    have hdpos : 0 < d := NNReal.coe_pos.mp hhalf
    have hmem : ∀ s : NNReal, s < t + d → omega s ∈ U := by
      intro s hs
      by_cases hst : s ≤ t
      · exact hall s hst
      · apply hball
        rw [Metric.mem_ball, NNReal.dist_eq]
        have hts : (t : ℝ) < (s : ℝ) := by exact_mod_cast lt_of_not_ge hst
        have hsd : (s : ℝ) < (t : ℝ) + delta / 2 := by
          have := hs
          rw [← NNReal.coe_lt_coe, NNReal.coe_add] at this
          exact this
        rw [abs_of_pos (by linarith only [hts])]
        linarith only [hsd, hdelta]
    have hge : ((t + d : NNReal) : ℝ≥0∞) ≤ exitTime U omega := by
      rw [exitTime]
      apply le_sInf
      rintro s ⟨u, rfl, hu⟩
      have hnotlt : ¬ u < t + d := fun h ↦ hu (hmem u h)
      exact_mod_cast not_lt.mp hnotlt
    have hlt : (t : ℝ≥0∞) < ((t + d : NNReal) : ℝ≥0∞) := by
      rw [ENNReal.coe_lt_coe]
      exact lt_add_of_pos_right t hdpos
    exact absurd (hlt.trans_le (hge.trans hle)) (lt_irrefl _)
  · rintro ⟨s, hs⟩
    refine le_trans (exitTime_le_of_notMem U omega s hs) ?_
    exact_mod_cast s.property
