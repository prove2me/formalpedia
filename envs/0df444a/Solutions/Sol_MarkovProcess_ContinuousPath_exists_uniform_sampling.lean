-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.exists_uniform_sampling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:27:51.620881+00:00
-- url     : https://prove2.me/submissions/64234eac-708b-46b3-b77d-c7ce2fee8310

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
theorem solution (omega : ContinuousPath alpha) (T : NNReal) (h : ℝ) (hh : 0 < h) :
    ∃ M : ℕ, 0 < M ∧ ∀ k < M,
      dist (omega ((k : NNReal) * T / (M : NNReal)))
        (omega (((k : NNReal) + 1) * T / (M : NNReal))) < h := by
  obtain ⟨delta, hdelta, hd⟩ :=
    Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous
        (omega.continuous.continuousOn (s := Set.Icc (0 : NNReal) T))) h hh
  obtain ⟨n, hn⟩ := exists_nat_gt ((T : ℝ) / delta)
  refine ⟨n + 1, Nat.succ_pos n, fun k hk ↦ ?_⟩
  have hMR : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
  have hMN : (0 : NNReal) < ((n + 1 : ℕ) : NNReal) := by
    rw [← NNReal.coe_pos]
    push_cast
    positivity
  have hmem : ∀ j : ℕ, j ≤ n + 1 →
      (j : NNReal) * T / ((n + 1 : ℕ) : NNReal) ∈ Set.Icc (0 : NNReal) T := by
    intro j hj
    refine ⟨zero_le, ?_⟩
    rw [div_le_iff₀ hMN]
    calc
      (j : NNReal) * T ≤ ((n + 1 : ℕ) : NNReal) * T :=
        mul_le_mul_left (Nat.cast_le.mpr hj) T
      _ = T * ((n + 1 : ℕ) : NNReal) := mul_comm _ _
  have hstep : (T : ℝ) / ((n : ℝ) + 1) < delta := by
    rw [div_lt_iff₀ hMR]
    have hTn : (T : ℝ) < (n : ℝ) * delta := by
      rw [div_lt_iff₀ hdelta] at hn
      exact hn
    calc
      (T : ℝ) < (n : ℝ) * delta := hTn
      _ ≤ delta * ((n : ℝ) + 1) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (by linarith only []) hdelta.le
  have hdistR : dist ((k : NNReal) * T / ((n + 1 : ℕ) : NNReal))
      (((k : NNReal) + 1) * T / ((n + 1 : ℕ) : NNReal)) = (T : ℝ) / ((n : ℝ) + 1) := by
    have hnonneg : (0 : ℝ) ≤ (T : ℝ) / ((n : ℝ) + 1) := by positivity
    have hexpand : (k : ℝ) * (T : ℝ) / ((n : ℝ) + 1) -
        ((k : ℝ) + 1) * (T : ℝ) / ((n : ℝ) + 1) = -((T : ℝ) / ((n : ℝ) + 1)) := by
      field_simp
      ring
    rw [NNReal.dist_eq]
    push_cast
    rw [hexpand, abs_neg, abs_of_nonneg hnonneg]
  refine hd _ (hmem k (by omega)) _ (?_) ?_
  · have : ((k : NNReal) + 1) = ((k + 1 : ℕ) : NNReal) := by push_cast; ring
    rw [this]
    exact hmem (k + 1) (by omega)
  · rw [hdistR]
    exact hstep
