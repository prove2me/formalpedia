-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.exists_lt_exitTime_dist_coordinate_exitTime_lt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:27:43.695275+00:00
-- url     : https://prove2.me/submissions/5a99f379-d5f6-45a6-82d9-01c15f289f18

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
# Uniform sampling of a continuous path

A continuous path is uniformly continuous on every bounded time interval, so for each accuracy
`h > 0` a uniform partition of `[0, T]` fine enough makes every consecutive pair of samples closer
than `h` (`ContinuousPath.exists_uniform_sampling`).  Three variants are recorded for use with the
exit time from a set `U`: when the horizon `T` is strictly before the exit time, every sample time
is too (`ContinuousPath.exists_uniform_sampling_lt_exitTime`), so the samples witness a family of
visited sets before the exit; and when the exit time is finite and positive there are times
strictly before it at which the path is within `h` of its exit position
(`ContinuousPath.exists_lt_exitTime_dist_coordinate_exitTime_lt`).  For an open `U` the exit
position lies on `frontier U`, and the third variant carries that conclusion with it
(`ContinuousPath.exists_lt_exitTime_mem_frontier_dist_lt`): a positive exit time already forces
`omega 0 ∈ U`, the hypothesis of `ContinuousPath.coordinate_exitTime_mem_frontier`, so no extra
hypothesis is needed.  The exit position is spelled `(exitTime U omega).toNNReal` throughout, as
in `Path/ExitTime.lean`; `ContinuousPath.untopD_exitTime` converts the `WithTop.untopD` spelling.

No lattice, no covering family and no discrete geometry appears here: the sampling is purely
metric.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]









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
# Uniform sampling of a continuous path

A continuous path is uniformly continuous on every bounded time interval, so for each accuracy
`h > 0` a uniform partition of `[0, T]` fine enough makes every consecutive pair of samples closer
than `h` (`ContinuousPath.exists_uniform_sampling`).  Three variants are recorded for use with the
exit time from a set `U`: when the horizon `T` is strictly before the exit time, every sample time
is too (`ContinuousPath.exists_uniform_sampling_lt_exitTime`), so the samples witness a family of
visited sets before the exit; and when the exit time is finite and positive there are times
strictly before it at which the path is within `h` of its exit position
(`ContinuousPath.exists_lt_exitTime_dist_coordinate_exitTime_lt`).  For an open `U` the exit
position lies on `frontier U`, and the third variant carries that conclusion with it
(`ContinuousPath.exists_lt_exitTime_mem_frontier_dist_lt`): a positive exit time already forces
`omega 0 ∈ U`, the hypothesis of `ContinuousPath.coordinate_exitTime_mem_frontier`, so no extra
hypothesis is needed.  The exit position is spelled `(exitTime U omega).toNNReal` throughout, as
in `Path/ExitTime.lean`; `ContinuousPath.untopD_exitTime` converts the `WithTop.untopD` spelling.

No lattice, no covering family and no discrete geometry appears here: the sampling is purely
metric.
-/

open Set
open scoped ENNReal NNReal



variable {alpha : Type*} [PseudoMetricSpace alpha]





namespace MarkovProcess.ContinuousPath

end MarkovProcess.ContinuousPath
open MarkovProcess.ContinuousPath
theorem solution (U : Set alpha)
    (omega : ContinuousPath alpha) (hpos : 0 < exitTime U omega) (hfin : exitTime U omega ≠ ⊤)
    (h : ℝ) (hh : 0 < h) :
    ∃ T : NNReal, (T : ℝ≥0∞) < exitTime U omega ∧
      dist (omega T) (omega ((exitTime U omega).toNNReal)) < h := by
  set tau : NNReal := (exitTime U omega).toNNReal with htau
  have hcoe : ((tau : NNReal) : ℝ≥0∞) = exitTime U omega := by
    rw [htau]
    exact ENNReal.coe_toNNReal hfin
  have htaupos : 0 < tau := by
    rw [← ENNReal.coe_pos, hcoe]
    exact hpos
  obtain ⟨delta, hdelta, hd⟩ :=
    Metric.continuousAt_iff.mp (omega.continuous.continuousAt (x := tau)) h hh
  set c : NNReal := min (Real.toNNReal (delta / 2)) (tau / 2)
  have hcpos : 0 < c := by
    refine lt_min ?_ ?_
    · rw [← NNReal.coe_pos, Real.coe_toNNReal _ (by positivity)]
      positivity
    · exact half_pos htaupos
  have hcle : c ≤ tau := by
    refine le_trans (min_le_right _ _) ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith only [tau.coe_nonneg]
  refine ⟨tau - c, ?_, ?_⟩
  · rw [← hcoe, ENNReal.coe_lt_coe]
    exact tsub_lt_self htaupos hcpos
  · refine hd ?_
    rw [NNReal.dist_eq, NNReal.coe_sub hcle]
    have hval : |(tau : ℝ) - (c : ℝ) - (tau : ℝ)| = (c : ℝ) := by
      rw [show (tau : ℝ) - (c : ℝ) - (tau : ℝ) = -(c : ℝ) by ring, abs_neg,
        abs_of_nonneg c.coe_nonneg]
    rw [hval]
    calc
      (c : ℝ) ≤ ((Real.toNNReal (delta / 2) : NNReal) : ℝ) := by
        exact_mod_cast min_le_left (Real.toNNReal (delta / 2)) (tau / 2)
      _ = delta / 2 := Real.coe_toNNReal _ (by positivity)
      _ < delta := by linarith only [hdelta]
