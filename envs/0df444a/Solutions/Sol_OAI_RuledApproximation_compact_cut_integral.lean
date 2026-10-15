-- Prove2me | solution 1 for OAI.RuledApproximation.compact_cut_integral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:49:35.778919+00:00
-- url     : https://prove2.me/submissions/1a9ac4b8-7127-4bcf-b74a-42766020b0ba

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/HyperbolicCover.lean:L94-L122
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.compact_cut_integral. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover

-- ---- from OAI.Geometry.RuledCovering.HyperbolicCover ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Compact pieces cut along a null frontier have exactly additive cost, even when
 the original compact set itself has a positive-area frontier. -/
lemma compact_cut_integral {K O : Set Plane} (hK : IsCompact K) (hO : IsOpen O)
    (hnull : volume (frontier O) = 0) {F : Plane → ℝ} (hF : IntegrableOn F K) :
    IsCompact (K ∩ closure O) ∧ IsCompact (K \ O) ∧
    K = (K ∩ closure O) ∪ (K \ O) ∧
    (∫ x in K, F x) = (∫ x in K ∩ closure O, F x) + (∫ x in K \ O, F x) := by
  have h₁ : IsCompact (K ∩ closure O) := hK.inter_right isClosed_closure
  have h₂ := hK.diff hO
  have hun : K = (K ∩ closure O) ∪ (K \ O) := by
    ext x
    simp only [mem_union, mem_inter_iff, Set.mem_sdiff]
    constructor
    · intro hx
      by_cases hxO : x ∈ O
      · exact Or.inl ⟨hx, subset_closure hxO⟩
      · exact Or.inr ⟨hx, hxO⟩
    · tauto
  refine ⟨h₁, h₂, hun, ?_⟩
  nth_rw 1 [hun]
  apply setIntegral_union₀
  · show volume ((K ∩ closure O) ∩ (K \ O)) = 0
    apply measure_mono_null _ hnull
    intro x hx
    rw [frontier, hO.interior_eq]
    exact ⟨hx.1.2, hx.2.2⟩
  · exact h₂.measurableSet.nullMeasurableSet
  · exact hF.mono_set inter_subset_left
  · exact hF.mono_set sdiff_subset

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.compact_cut_integral := @_root_.OAI.RuledApproximation.compact_cut_integral
