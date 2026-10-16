-- Prove2me | solution 2 for OAI.Problem310.Auxiliary.thickening_periodic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:47:17.68998+00:00
-- url     : https://prove2.me/submissions/529b10bb-b25a-4443-be8d-921456dbb1e2

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalCenters.lean:L87-L101
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.Auxiliary.thickening_periodic. The node keeps its source
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

open Set Filter Topology MeasureTheory Metric

/-- Thickening preserves one-periodicity. -/
theorem thickening_periodic (R : Set ℝ)
    (hR : ∀ x : ℝ, x + 1 ∈ R ↔ x ∈ R) (ε : ℝ) :
    ∀ x : ℝ, x + 1 ∈ thickening ε R ↔ x ∈ thickening ε R := by
  intro x
  simp only [mem_thickening_iff]
  constructor
  · rintro ⟨z, hz, hdist⟩
    refine ⟨z - 1, ?_, ?_⟩
    · apply (hR (z - 1)).mp
      simpa using hz
    · simpa [Real.dist_eq, sub_sub] using hdist
  · rintro ⟨z, hz, hdist⟩
    refine ⟨z + 1, (hR z).mpr hz, ?_⟩
    simpa using hdist

end

open Set Filter Topology MeasureTheory

end Problem310.Auxiliary

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.Auxiliary
open Set Filter Topology
open Set Filter Topology MeasureTheory Metric


theorem solution : type_of% @_root_.OAI.Problem310.Auxiliary.thickening_periodic := @_root_.OAI.Problem310.Auxiliary.thickening_periodic
