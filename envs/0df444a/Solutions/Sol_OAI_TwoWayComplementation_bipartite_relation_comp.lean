-- Prove2me | solution 1 for OAI.TwoWayComplementation.bipartite_relation_comp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:57:37.353564+00:00
-- url     : https://prove2.me/submissions/f7b5f11c-2ec4-4b4f-a9f5-901cea02a4ce

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Amplification.lean:L93-L109
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.bipartite_relation_comp. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification

-- ---- from OAI.Combinatorics.TwoWayAutomata.Amplification ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Disjoint source and target sets prevent two added edges from being concatenated. -/
theorem bipartite_relation_comp {H : Type*} (F U V : Set H)
    (hU : U ⊆ F) (hV : V ⊆ F) (hUV : Disjoint U V)
    (E E' : SetRel H H) (hE : E ⊆ U ×ˢ V) (hE' : E' ⊆ U ×ˢ V) :
    (restrictedIdentity F ∪ E) ○ (restrictedIdentity F ∪ E') =
      restrictedIdentity F ∪ (E ∪ E') := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨z, hxz | hxz, hzy | hzy⟩
    · exact Or.inl ⟨hxz.1.trans hzy.1, hxz.2⟩
    · exact Or.inr (Or.inr (hxz.1 ▸ hzy))
    · exact Or.inr (Or.inl (hzy.1 ▸ hxz))
    · exact (Set.disjoint_left.mp hUV (hE' hzy).1 (hE hxz).2).elim
  · rintro (hxy | hxy | hxy)
    · exact ⟨x, Or.inl ⟨rfl, hxy.2⟩, Or.inl hxy⟩
    · exact ⟨y, Or.inr hxy, Or.inl ⟨rfl, hV (hE hxy).2⟩⟩
    · exact ⟨x, Or.inl ⟨rfl, hU (hE' hxy).1⟩, Or.inr hxy⟩

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.bipartite_relation_comp := @_root_.OAI.TwoWayComplementation.bipartite_relation_comp
