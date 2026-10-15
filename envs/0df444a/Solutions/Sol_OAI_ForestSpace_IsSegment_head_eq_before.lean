-- Prove2me | solution 1 for OAI.ForestSpace.IsSegment.head_eq_before
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:32:17.271632+00:00
-- url     : https://prove2.me/submissions/cad55ce2-a118-49b0-b8c7-f063aaa6464c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/FiniteGeometry.lean:L47-L67
-- (upload_full_project.md Phase 4): solution for node OAI.ForestSpace.IsSegment.head_eq_before. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry

-- ---- from OAI.Analysis.ForestSpace.Segments ----
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section Basic
variable {V : Type} [PartialOrder V]

end Basic

section Geometry
variable {V : Type} [PartialOrder V]

 theorem IsSegment.endpoints {S : Finset V} (hS : IsSegment S) (hne : S.Nonempty) :
    ∃ a ∈ S, ∃ b ∈ S, ∀ v, v ∈ S ↔ a ≤ v ∧ v ≤ b := by
  obtain ⟨a, ha, hamin⟩ := S.exists_minimal hne
  obtain ⟨b, hb, hbmax⟩ := S.exists_maximal hne
  refine ⟨a, ha, b, hb, ?_⟩
  intro v
  constructor
  · intro hv
    exact ⟨(hS.1 a ha v hv).elim id (hamin hv),
      (hS.1 v hv b hb).elim id (hbmax hv)⟩
  · rintro ⟨hav, hvb⟩
    exact hS.2 a ha b hb v hav hvb

end Geometry

end

end ForestSpace

end OAI

-- ---- from OAI.Analysis.ForestSpace.FiniteGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section FiniteGeometry
variable {V : Type} [Fintype V] [PartialOrder V]

 theorem IsSegment.head_eq_before {H : Set V} (hH : IsLowerSet H)
    {S : Finset V} (hS : IsSegment S) {g : V} (hg : Gate H g) (hgs : g ∈ S)
    (hp : ∃ a ∈ S, a ∈ H) :
    ∃ a, a < g ∧ S.filter (· ∈ H) = before a g := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hS.endpoints ⟨g, hgs⟩
  have haH : a ∈ H := by
    obtain ⟨w, hw, hwH⟩ := hp
    exact hH ((hab w).mp hw).1 hwH
  have hag : a < g := lt_of_le_of_ne ((hab g).mp hgs).1
    (fun h => hg.1 (h ▸ haH))
  refine ⟨a, hag, ?_⟩
  ext v
  simp only [mem_filter, mem_before]
  constructor
  · rintro ⟨hv, hvH⟩
    refine ⟨((hab v).mp hv).1, ?_⟩
    have hvg : v ≤ g := (hS.1 v hv g hgs).resolve_right (fun h => hg.1 (hH h hvH))
    exact lt_of_le_of_ne hvg (fun he => hg.1 (he ▸ hvH))
  · rintro ⟨hav, hvg⟩
    exact ⟨hS.2 a ha g hgs v hav hvg.le, hg.2 v hvg⟩

end FiniteGeometry

section CrossTermAlgebra

end CrossTermAlgebra

end

end ForestSpace

end OAI

-- ---- platform node ----
open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ForestSpace.IsSegment.head_eq_before := @_root_.OAI.ForestSpace.IsSegment.head_eq_before
