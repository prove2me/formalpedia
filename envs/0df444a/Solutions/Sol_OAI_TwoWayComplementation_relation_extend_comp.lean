-- Prove2me | solution 1 for OAI.TwoWayComplementation.relation_extend_comp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:51:38.914163+00:00
-- url     : https://prove2.me/submissions/d8d692c6-09fb-4205-8a86-7421e37a0aa7

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/RelationMonoid.lean:L139-L155
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.relation_extend_comp. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid

-- ---- from OAI.Combinatorics.TwoWayAutomata.RelationMonoid ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace RelationMonoid

end RelationMonoid

/-- Extension of relations on a subset preserves path composition. -/
theorem relation_extend_comp {H : Type*} (F : Set H) (A B : SetRel F F) :
    (Prod.map Subtype.val Subtype.val) '' (A ○ B) =
      ((Prod.map Subtype.val Subtype.val) '' A) ○
        ((Prod.map Subtype.val Subtype.val) '' B) := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨⟨a, b⟩, ⟨c, hac, hcb⟩, hxy⟩
    cases hxy
    exact ⟨c.val, ⟨(a, c), hac, rfl⟩, (c, b), hcb, rfl⟩
  · rintro ⟨z, ⟨⟨a, b⟩, hab, habxy⟩, ⟨⟨c, d⟩, hcd, hcdxy⟩⟩
    have hbc : b = c := Subtype.ext ((congrArg Prod.snd habxy).trans
      (congrArg Prod.fst hcdxy).symm)
    subst c
    have hax : a.val = x := congrArg Prod.fst habxy
    have hdy : d.val = y := congrArg Prod.snd hcdxy
    exact ⟨(a, d), ⟨b, hab, hcd⟩, Prod.ext hax hdy⟩

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.relation_extend_comp := @_root_.OAI.TwoWayComplementation.relation_extend_comp
