-- Prove2me | solution 1 for OAI.Problem310.Auxiliary.exceptionalCenters_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:45:57.572898+00:00
-- url     : https://prove2.me/submissions/72aecbe3-d0ec-40ee-ac7c-86449f740012

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalCenters.lean:L42-L57
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.Auxiliary.exceptionalCenters_periodic. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters

-- ---- from OAI.MeasureTheory.DyadicAvoidance.ExceptionalCenters ----
namespace OAI

noncomputable section

open Set Filter Topology

namespace Problem310.Auxiliary

section

/-- Periodicity passes from the selected set to its exceptional centers. -/
theorem exceptionalCenters_periodic (B : Set ℝ)
    (hB : ∀ x : ℝ, x + 1 ∈ B ↔ x ∈ B) (N : Set ℕ) (a : ℕ → ℝ) :
    ∀ x : ℝ, x + 1 ∈ exceptionalCenters B N a ↔
      x ∈ exceptionalCenters B N a := by
  intro x
  simp only [exceptionalCenters, mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨t, ht, fun n hn hm => h n hn ?_⟩
    rw [show x + 1 + t * a n = (x + t * a n) + 1 by ring]
    exact (hB _).mpr hm
  · rintro ⟨t, ht, h⟩
    refine ⟨t, ht, fun n hn hm => h n hn ?_⟩
    apply (hB _).mp
    convert hm using 1; ring

open Set Filter Topology MeasureTheory Metric

end

open Set Filter Topology MeasureTheory

end Problem310.Auxiliary

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.Auxiliary
open Set Filter Topology


theorem solution : type_of% @_root_.OAI.Problem310.Auxiliary.exceptionalCenters_periodic := @_root_.OAI.Problem310.Auxiliary.exceptionalCenters_periodic
