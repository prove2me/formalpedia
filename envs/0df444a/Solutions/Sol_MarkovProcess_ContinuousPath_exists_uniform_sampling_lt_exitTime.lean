-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.exists_uniform_sampling_lt_exitTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:32:47.272327+00:00
-- url     : https://prove2.me/submissions/d1d4ca24-3bb7-48f9-aad2-6104f5a114cf

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
import Theorems.Thm_MarkovProcess_ContinuousPath_exists_uniform_sampling

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
theorem solution (U : Set alpha) (omega : ContinuousPath alpha)
    (T : NNReal) (hT : (T : ℝ≥0∞) < exitTime U omega) (h : ℝ) (hh : 0 < h) :
    ∃ M : ℕ, 0 < M ∧
      (∀ k ≤ M, (((k : NNReal) * T / (M : NNReal) : NNReal) : ℝ≥0∞) < exitTime U omega) ∧
      ∀ k < M, dist (omega ((k : NNReal) * T / (M : NNReal)))
        (omega (((k : NNReal) + 1) * T / (M : NNReal))) < h := by
  obtain ⟨M, hM, hsample⟩ := exists_uniform_sampling omega T h hh
  refine ⟨M, hM, fun k hk ↦ ?_, hsample⟩
  have hMN : (0 : NNReal) < ((M : ℕ) : NNReal) := by
    rw [← NNReal.coe_pos]
    have : (0 : ℕ) < M := hM
    push_cast
    exact_mod_cast this
  have hle : (k : NNReal) * T / (M : NNReal) ≤ T := by
    rw [div_le_iff₀ hMN]
    calc
      (k : NNReal) * T ≤ ((M : ℕ) : NNReal) * T := mul_le_mul_left (Nat.cast_le.mpr hk) T
      _ = T * ((M : ℕ) : NNReal) := mul_comm _ _
  exact lt_of_le_of_lt (by exact_mod_cast hle) hT
