-- Prove2me | solution 2 for OAI.Problem310.Auxiliary.exists_open_periodic_superset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:48:38.200887+00:00
-- url     : https://prove2.me/submissions/223e7586-7a6b-46d9-a88c-609d31c614b5

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalCenters.lean:L103-L127
-- (upload_full_project.md Phase 4): solution for node OAI.Problem310.Auxiliary.exists_open_periodic_superset. The node keeps its source
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
import Theorems.Thm_OAI_Problem310_Auxiliary_thickening_periodic

-- ---- from OAI.MeasureTheory.DyadicAvoidance.ExceptionalCenters ----
namespace OAI

noncomputable section

open Set Filter Topology

namespace Problem310.Auxiliary

section

open Set Filter Topology MeasureTheory Metric

/-- A closed periodic set admits an open periodic neighborhood with arbitrarily
small increase of its measure in one period. -/
theorem exists_open_periodic_superset (R : Set ℝ) (hRc : IsClosed R)
    (hRp : ∀ x : ℝ, x + 1 ∈ R ↔ x ∈ R) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set ℝ, IsOpen V ∧
      (∀ x : ℝ, x + 1 ∈ V ↔ x ∈ V) ∧ R ⊆ V ∧
      volume (V ∩ Icc (0 : ℝ) 1) ≤
        volume (R ∩ Icc (0 : ℝ) 1) + ENNReal.ofReal ε := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hfinite : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  let := hfinite
  have hlim : Tendsto (fun r => μ (thickening r R)) (𝓝[>] 0) (𝓝 (μ R)) :=
    tendsto_measure_thickening_of_isClosed ⟨1, zero_lt_one, measure_ne_top μ _⟩ hRc
  have hlt : μ R < μ R + ENNReal.ofReal ε :=
    ENNReal.lt_add_right (measure_ne_top μ R) (by positivity)
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (thickening r R) < μ R + ENNReal.ofReal ε :=
    hlim.eventually (eventually_lt_nhds hlt)
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hbound⟩ := (hpos.and hev).exists
  refine ⟨thickening r R, isOpen_thickening, thickening_periodic R hRp r,
    self_subset_thickening hr R, ?_⟩
  simpa [μ, Measure.restrict_apply, isOpen_thickening.measurableSet,
    hRc.measurableSet] using hbound.le

end

open Set Filter Topology MeasureTheory

end Problem310.Auxiliary

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem310 OAI.Problem310.Auxiliary
open Set Filter Topology
open Set Filter Topology MeasureTheory Metric


theorem solution : type_of% @_root_.OAI.Problem310.Auxiliary.exists_open_periodic_superset := @_root_.OAI.Problem310.Auxiliary.exists_open_periodic_superset
