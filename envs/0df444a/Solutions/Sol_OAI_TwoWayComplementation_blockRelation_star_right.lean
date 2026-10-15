-- Prove2me | solution 1 for OAI.TwoWayComplementation.blockRelation_star_right
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:11:53.166596+00:00
-- url     : https://prove2.me/submissions/b8572789-9cbd-4edd-84da-e2c9a0c7fb01

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Relations.lean:L41-L75
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.blockRelation_star_right. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations

-- ---- from OAI.Combinatorics.TwoWayAutomata.Relations ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Eliminate the left block by replacing each finite excursion with one edge. -/
theorem blockRelation_star_right {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) (x y : β) :
    ((Sum.inr x), (Sum.inr y)) ∈ relStar (blockRelation E F G H) ↔
      (x, y) ∈ relStar (H ∪ (G ○ relStar E ○ F)) := by
  let R := blockRelation E F G H
  let K := H ∪ (G ○ relStar E ○ F)
  have hsound {c : α ⊕ β} (hrun : (Sum.inr x, c) ∈ relStar R) :
      match c with
      | .inl a => (x, a) ∈ relStar K ○ G ○ relStar E
      | .inr b => (x, b) ∈ relStar K := by
    induction hrun with
    | refl => exact .refl
    | @tail c d _ hcd ih =>
      cases c with
      | inl a =>
        obtain ⟨p, ⟨q, hxq, hqp⟩, hpa⟩ := ih
        cases d with
        | inl b => exact ⟨p, ⟨q, hxq, hqp⟩, hpa.tail hcd⟩
        | inr b => exact hxq.tail (Or.inr ⟨a, ⟨p, hqp, hpa⟩, hcd⟩)
      | inr a =>
        cases d with
        | inl b => exact ⟨b, ⟨a, ih, hcd⟩, .refl⟩
        | inr b => exact ih.tail (Or.inl hcd)
  constructor
  · exact hsound
  · intro hxy
    exact hxy.lift' (Sum.inr : β → α ⊕ β)
      (p := fun a b => (a, b) ∈ R) (by
        intro a b hab
        rcases hab with hH | ⟨q, ⟨p, hag, hpq⟩, hfb⟩
        · exact .single hH
        · have hmid := hpq.lift (Sum.inl : α → α ⊕ β)
            (p := fun a b => (a, b) ∈ R) (fun _ _ h => h)
          exact (hmid.head hag).tail hfb)

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.blockRelation_star_right := @_root_.OAI.TwoWayComplementation.blockRelation_star_right
