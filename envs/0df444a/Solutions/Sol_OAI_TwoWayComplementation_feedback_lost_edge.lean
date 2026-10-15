-- Prove2me | solution 1 for OAI.TwoWayComplementation.feedback_lost_edge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:14:23.499646+00:00
-- url     : https://prove2.me/submissions/97a24cfd-ebb5-495d-8b1f-4866bc2d6ca6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Relations.lean:L234-L251
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.feedback_lost_edge. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations

-- ---- from OAI.Combinatorics.TwoWayAutomata.Relations ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- A path lost after an edge replacement contains a lost edge between old path segments. -/
theorem relStar_lost_edge {α : Type*} (R S : SetRel α α) {x y : α}
    (hxy : (x, y) ∈ relStar R) (hnot : (x, y) ∉ relStar S) :
    ∃ a b, (x, a) ∈ relStar R ∧ (a, b) ∈ R ∧ (a, b) ∉ S ∧ (b, y) ∈ relStar R := by
  classical
  induction hxy with
  | refl => exact (hnot Relation.ReflTransGen.refl).elim
  | @tail a b hxa hab ih =>
    by_cases hgood : (x, a) ∈ relStar S
    · refine ⟨a, b, hxa, hab, ?_, .refl⟩
      exact fun habS => hnot (hgood.tail habS)
    · obtain ⟨u, v, hxu, huv, hnuv, hva⟩ := ih hgood
      exact ⟨u, v, hxu, huv, hnuv, hva.tail hab⟩

/-- A lost alternating traversal has a lost edge, allowing earlier and later bounces. -/
theorem feedback_lost_edge {α : Type*} (E E' B : SetRel α α) {x y : α}
    (hxy : (x, y) ∈ E ○ relStar (B ○ E))
    (hnot : (x, y) ∉ E' ○ relStar (B ○ E')) :
    ∃ a b, (x, a) ∈ relStar (E ○ B) ∧ (a, b) ∈ E ∧
      (a, b) ∉ E' ∧ (b, y) ∈ relStar (B ○ E) := by
  classical
  obtain ⟨z, hxz, hzy⟩ := hxy
  by_cases hfirst : (x, z) ∈ E'
  · have hnzy : (z, y) ∉ relStar (B ○ E') := fun h => hnot ⟨z, hfirst, h⟩
    obtain ⟨a, b, hza, ⟨c, hac, hcb⟩, hnab, hby⟩ :=
      relStar_lost_edge (B ○ E) (B ○ E') hzy hnzy
    have hprefix : (x, a) ∈ relStar (E ○ B) ○ E := by
      rw [← comp_relStar_rotate]
      exact ⟨z, hxz, hza⟩
    obtain ⟨d, hxd, hda⟩ := hprefix
    exact ⟨c, b, hxd.tail ⟨a, hda, hac⟩, hcb, fun h => hnab ⟨c, hac, h⟩, hby⟩
  · exact ⟨x, z, .refl, hxz, hfirst, hzy⟩

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.feedback_lost_edge := @_root_.OAI.TwoWayComplementation.feedback_lost_edge
