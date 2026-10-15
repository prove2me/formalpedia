-- Prove2me | solution 1 for OAI.TwoWayComplementation.blockRelation_star_cross
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:13:04.337905+00:00
-- url     : https://prove2.me/submissions/eaaabb5d-7caa-41f6-b1ba-82d0512cbefb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Relations.lean:L77-L104
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.blockRelation_star_cross. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Theorems.Thm_OAI_TwoWayComplementation_blockRelation_star_right

-- ---- from OAI.Combinatorics.TwoWayAutomata.Relations ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- A path from the left block first leaves it once, then makes arbitrary finite excursions. -/
theorem blockRelation_star_cross {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) (x : α) (y : β) :
    ((Sum.inl x), (Sum.inr y)) ∈ relStar (blockRelation E F G H) ↔
      (x, y) ∈ relStar E ○ F ○ relStar (H ∪ (G ○ relStar E ○ F)) := by
  let R := blockRelation E F G H
  let K := H ∪ (G ○ relStar E ○ F)
  have hsound {c : α ⊕ β} (hrun : (c, Sum.inr y) ∈ relStar R) :
      ∀ x, c = Sum.inl x → (x, y) ∈ relStar E ○ F ○ relStar K := by
    induction hrun using Relation.ReflTransGen.head_induction_on with
    | refl => intro _ heq; cases heq
    | @head c d hcd hdy ih =>
      intro x hcx
      subst c
      cases d with
      | inl a =>
        obtain ⟨u, ⟨v, hxv, hvu⟩, huy⟩ := ih a rfl
        exact ⟨u, ⟨v, hxv.head hcd, hvu⟩, huy⟩
      | inr b =>
        exact ⟨b, ⟨x, .refl, hcd⟩, (blockRelation_star_right E F G H b y).mp hdy⟩
  constructor
  · intro hxy
    exact hsound hxy x rfl
  · rintro ⟨v, ⟨u, hxu, huv⟩, hvy⟩
    have hleft := hxu.lift (Sum.inl : α → α ⊕ β)
      (p := fun a b => (a, b) ∈ R) (fun _ _ h => h)
    have hcross : (Sum.inl x, Sum.inr v) ∈ relStar R := hleft.tail huv
    exact hcross.trans ((blockRelation_star_right E F G H v y).mpr hvy)

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.blockRelation_star_cross := @_root_.OAI.TwoWayComplementation.blockRelation_star_cross
