-- Prove2me | solution 1 for MarkovProcess.ContinuousPath.IsOpenExhaustion.exists_lt_exitTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:32:35.036089+00:00
-- url     : https://prove2.me/submissions/424dbb65-9c5e-4593-8a00-6314d22ed67b

import Definitions.Def_MarkovProcess_V3H_Path_Exhaustion_e03721f1
import Definitions.Def_MarkovProcess_V3H_Path_ExitTimeShift_63f55a50
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
# Exit times along an exhaustion

For an increasing sequence of open sets `U n` covering the state space (an open exhaustion), the
exit time of a continuous path from `U n` tends to infinity: the path restricted to a compact time
interval has compact range, which lies in some `U N`, and the path therefore stays in `U n` on that
interval for every `n ≥ N` (`tendsto_exitTime_atTop`).  Exit times are monotone in the set
(`exitTime_mono`), as are the truncated exit times.

This is the path-space fact behind nonexplosion arguments: no probability law is involved here.
-/

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped ENNReal NNReal

namespace MarkovProcess.ContinuousPath

variable {alpha : Type*} [PseudoMetricSpace alpha]

















end MarkovProcess.ContinuousPath


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exit times along an exhaustion

For an increasing sequence of open sets `U n` covering the state space (an open exhaustion), the
exit time of a continuous path from `U n` tends to infinity: the path restricted to a compact time
interval has compact range, which lies in some `U N`, and the path therefore stays in `U n` on that
interval for every `n ≥ N` (`tendsto_exitTime_atTop`).  Exit times are monotone in the set
(`exitTime_mono`), as are the truncated exit times.

This is the path-space fact behind nonexplosion arguments: no probability law is involved here.
-/

open Filter Topology
open scoped ENNReal NNReal


variable {alpha : Type*} [PseudoMetricSpace alpha]







namespace MarkovProcess.ContinuousPath.IsOpenExhaustion

end MarkovProcess.ContinuousPath.IsOpenExhaustion
open MarkovProcess.ContinuousPath.IsOpenExhaustion
theorem solution {U : ℕ → Set alpha} (hU : IsOpenExhaustion U)
    (omega : ContinuousPath alpha) (T : NNReal) :
    ∃ N, ∀ n ≥ N, (T : ℝ≥0∞) < exitTime (U n) omega := by
  have hcompact : IsCompact ((omega : NNReal → alpha) '' Set.Icc 0 T) :=
    isCompact_Icc.image omega.continuous
  have hcover : (omega : NNReal → alpha) '' Set.Icc 0 T ⊆ ⋃ n, U n := by
    rw [hU.iUnion_eq]
    exact Set.subset_univ _
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover U hU.isOpen hcover
  refine ⟨s.sup id, fun n hn ↦ ?_⟩
  have hsub : (omega : NNReal → alpha) '' Set.Icc 0 T ⊆ U n := by
    refine hs.trans (Set.iUnion₂_subset fun i hi ↦ hU.monotone ?_)
    exact (Finset.le_sup (f := id) hi).trans hn
  by_contra hle
  rw [not_lt, exitTime_le_iff_mem_hitsSetBy (U n) (hU.isOpen n) T omega] at hle
  obtain ⟨t, ht⟩ := hle
  exact ht (hsub ⟨t, Set.mem_Icc.mpr ⟨zero_le, t.2⟩, rfl⟩)
