-- Prove2me | solution 1 for OAI.CompactBanach.compact_shrinking_union
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:31:24.071541+00:00
-- url     : https://prove2.me/submissions/a10e785c-53cc-419b-ad2d-31f05efeeaf7

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/CompactUnion.lean:L10-L38
-- (upload_full_project.md Phase 4): solution for node OAI.CompactBanach.compact_shrinking_union. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateSupport
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateMap
import Definitions.Def_OAI_Geometry_DoublingHilbert_IntrinsicCovers

-- ---- from OAI.Geometry.DoublingHilbert.CompactUnion ----
namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach

theorem compact_shrinking_union {B : Type*} [MetricSpace B]
    (o : B) (C : ℕ → Finset B)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j ≥ N, ∀ z ∈ C j, dist z o < ε) :
    IsCompact ({o} ∪ ⋃ j : ℕ, (C j : Set B)) := by
  classical
  apply isCompact_of_finite_subcover
  intro ι U hU hcov
  obtain ⟨i₀, hi₀⟩ := mem_iUnion.mp (hcov (by simp : o ∈ {o} ∪ ⋃ j : ℕ, (C j : Set B)))
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp (hU i₀) o hi₀
  obtain ⟨N, hN⟩ := hsmall ε hε
  let F : Finset B := (Finset.range N).biUnion C
  have hFK : (F : Set B) ⊆ {o} ∪ ⋃ j : ℕ, (C j : Set B) := by
    intro z hz
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hz
    exact Or.inr (mem_iUnion.mpr ⟨j, hj⟩)
  obtain ⟨t, ht⟩ := F.finite_toSet.isCompact.elim_finite_subcover U hU (hFK.trans hcov)
  refine ⟨insert i₀ t, ?_⟩
  intro z hz
  rcases hz with hz | hz
  · rcases Set.mem_singleton_iff.mp hz with rfl
    exact mem_iUnion.mpr ⟨i₀, mem_iUnion.mpr ⟨by simp, hi₀⟩⟩
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    by_cases hjN : j < N
    · have hzF : z ∈ F := Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjN, hj⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp (ht hzF)
      obtain ⟨hit, hzi⟩ := mem_iUnion.mp hi
      exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hit, hzi⟩⟩
    · have hzi : z ∈ U i₀ := hεU (hN j (by omega) z hj)
      exact mem_iUnion.mpr ⟨i₀, mem_iUnion.mpr ⟨by simp, hzi⟩⟩

end CompactBanach
end

end OAI

-- ---- platform node ----
open OAI OAI.CompactBanach
open Set Metric
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.CompactBanach.compact_shrinking_union := @_root_.OAI.CompactBanach.compact_shrinking_union
