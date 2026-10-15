-- Prove2me | solution 1 for OAI.TwoWayComplementation.Network.summary_join
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:27:18.919716+00:00
-- url     : https://prove2.me/submissions/9d1200e7-4f0c-4e5a-8d65-1607226c31ce

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Network.lean:L108-L183
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.Network.summary_join. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Normalization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Source
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Network
import Theorems.Thm_OAI_TwoWayComplementation_blockRelation_star_cross
import Theorems.Thm_OAI_TwoWayComplementation_blockRelation_star_right

-- ---- from OAI.Combinatorics.TwoWayAutomata.Network ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Swap the two vertex blocks without changing the finite-path semantics. -/
theorem blockRelation_star_swap {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) (x y : α ⊕ β) :
    (x.swap, y.swap) ∈ relStar (blockRelation H G F E) ↔
      (x, y) ∈ relStar (blockRelation E F G H) := by
  have hs {a b : α ⊕ β} :
      (a.swap, b.swap) ∈ blockRelation H G F E ↔ (a, b) ∈ blockRelation E F G H := by
    cases a <;> cases b <;> rfl
  constructor
  · intro h
    have h' := h.lift Sum.swap (p := fun a b => (a, b) ∈ blockRelation E F G H)
      (fun a b hab => by cases a <;> cases b <;> exact hab)
    change Relation.ReflTransGen (fun a b => (a, b) ∈ blockRelation E F G H) x y
    simpa only [Function.onFun, Sum.swap_swap] using h'
  · exact fun h => h.lift Sum.swap (fun _ _ hab => hs.mpr hab)

/-- The left-left version of block elimination. -/
theorem blockRelation_star_left {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) (x y : α) :
    (Sum.inl x, Sum.inl y) ∈ relStar (blockRelation E F G H) ↔
      (x, y) ∈ relStar (E ∪ (F ○ relStar H ○ G)) := by
  rw [← blockRelation_star_swap]
  exact blockRelation_star_right H G F E x y

/-- The right-left version of block elimination. -/
theorem blockRelation_star_back {α β : Type*} (E : SetRel α α) (F : SetRel α β)
    (G : SetRel β α) (H : SetRel β β) (x : β) (y : α) :
    (Sum.inr x, Sum.inl y) ∈ relStar (blockRelation E F G H) ↔
      (x, y) ∈ relStar H ○ G ○ relStar (E ∪ (F ○ relStar H ○ G)) := by
  rw [← blockRelation_star_swap]
  exact blockRelation_star_cross H G F E x y

/-- Eliminate an internal graph while retaining arbitrary repeated feedback at its entry. -/
theorem relStar_entry_feedback {Q V : Type*} (I : SetRel Q V) (E : SetRel V V)
    (O R : SetRel V Q) (X : SetRel Q Q) :
    I ○ relStar (E ∪ (R ○ X ○ I)) ○ O =
      relStar (I ○ relStar E ○ R ○ X) ○ (I ○ relStar E ○ O) := by
  have hrotate := comp_relStar_rotate (I ○ relStar E) (R ○ X)
  simpa only [relStar_union, SetRel.comp_assoc] using congrArg (· ○ O) hrotate

/-- Internal paths either avoid the feedback edge or use it after a first internal segment. -/
theorem relStar_general_feedback {Q V : Type*} (I J : SetRel Q V) (E : SetRel V V)
    (O R : SetRel V Q) (X : SetRel Q Q) :
    I ○ relStar (E ∪ (R ○ X ○ J)) ○ O =
      (I ○ relStar E ○ O) ∪
        (I ○ relStar E ○ R ○ relStar (X ○ J ○ relStar E ○ R) ○ X ○ J ○ relStar E ○ O) := by
  have hu := relStar_comp_unfold (R : SetRel V Q) (X ○ J ○ relStar E)
  have hexpand := congrArg (fun K => I ○ relStar E ○ K ○ O) hu
  simpa only [relStar_union, relComp_union, union_relComp, SetRel.comp_id,
    SetRel.comp_assoc] using hexpand

namespace Network

/-- Joining path networks implements exactly the four diagram multiplication formulas. -/
theorem summary_join {m : ℕ} {V W : Type*} (N : Network m V) (M : Network m W) :
    (N.join M).summary = Diagram.comp N.summary M.summary := by
  have hF : (N.join M).summary.forward =
      N.leftIn ○ (relStar N.edge ○ (N.rightOut ○ M.leftIn) ○
        relStar (M.edge ∪ ((M.leftOut ○ N.rightIn) ○ relStar N.edge ○
          (N.rightOut ○ M.leftIn)))) ○ M.rightOut := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨v, ⟨u, ⟨a, rfl, hxa⟩, huv⟩, ⟨b, rfl, hby⟩⟩
      exact ⟨b, ⟨a, hxa, (blockRelation_star_cross _ _ _ _ a b).mp huv⟩, hby⟩
    · rintro ⟨b, hab, hby⟩
      obtain ⟨a, hxa, hab⟩ := hab
      exact ⟨Sum.inr b, ⟨Sum.inl a, ⟨a, rfl, hxa⟩,
        (blockRelation_star_cross _ _ _ _ a b).mpr hab⟩, ⟨b, rfl, hby⟩⟩
  have hB : (N.join M).summary.backward =
      M.rightIn ○ (relStar M.edge ○ (M.leftOut ○ N.rightIn) ○
        relStar (N.edge ∪ ((N.rightOut ○ M.leftIn) ○ relStar M.edge ○
          (M.leftOut ○ N.rightIn)))) ○ N.leftOut := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨v, ⟨u, ⟨a, rfl, hxa⟩, huv⟩, ⟨b, rfl, hby⟩⟩
      exact ⟨b, ⟨a, hxa, (blockRelation_star_back _ _ _ _ a b).mp huv⟩, hby⟩
    · rintro ⟨b, hab, hby⟩
      obtain ⟨a, hxa, hab⟩ := hab
      exact ⟨Sum.inl b, ⟨Sum.inr a, ⟨a, rfl, hxa⟩,
        (blockRelation_star_back _ _ _ _ a b).mpr hab⟩, ⟨b, rfl, hby⟩⟩
  have hL : (N.join M).summary.left =
      N.leftIn ○ relStar (N.edge ∪ ((N.rightOut ○ M.leftIn) ○ relStar M.edge ○
        (M.leftOut ○ N.rightIn))) ○ N.leftOut := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨v, ⟨u, ⟨a, rfl, hxa⟩, huv⟩, ⟨b, rfl, hby⟩⟩
      exact ⟨b, ⟨a, hxa, (blockRelation_star_left _ _ _ _ a b).mp huv⟩, hby⟩
    · rintro ⟨b, ⟨a, hxa, hab⟩, hby⟩
      exact ⟨Sum.inl b, ⟨Sum.inl a, ⟨a, rfl, hxa⟩,
        (blockRelation_star_left _ _ _ _ a b).mpr hab⟩, ⟨b, rfl, hby⟩⟩
  have hR : (N.join M).summary.right =
      M.rightIn ○ relStar (M.edge ∪ ((M.leftOut ○ N.rightIn) ○ relStar N.edge ○
        (N.rightOut ○ M.leftIn))) ○ M.rightOut := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨v, ⟨u, ⟨a, rfl, hxa⟩, huv⟩, ⟨b, rfl, hby⟩⟩
      exact ⟨b, ⟨a, hxa, (blockRelation_star_right _ _ _ _ a b).mp huv⟩, hby⟩
    · rintro ⟨b, ⟨a, hxa, hab⟩, hby⟩
      exact ⟨Sum.inr b, ⟨Sum.inr a, ⟨a, rfl, hxa⟩,
        (blockRelation_star_right _ _ _ _ a b).mpr hab⟩, ⟨b, rfl, hby⟩⟩
  apply Diagram.ext
  · rw [hF]
    have hf := relStar_entry_feedback M.leftIn M.edge M.rightOut M.leftOut
      (N.rightIn ○ relStar N.edge ○ N.rightOut)
    simpa only [summary, Diagram.comp, SetRel.comp_assoc] using
      congrArg ((N.leftIn ○ relStar N.edge ○ N.rightOut) ○ ·) hf
  · rw [hB]
    have hb := relStar_entry_feedback N.rightIn N.edge N.leftOut N.rightOut
      (M.leftIn ○ relStar M.edge ○ M.leftOut)
    simpa only [summary, Diagram.comp, SetRel.comp_assoc] using
      congrArg ((M.rightIn ○ relStar M.edge ○ M.leftOut) ○ ·) hb
  · rw [hL]
    simpa only [summary, Diagram.comp, SetRel.comp_assoc] using
      relStar_general_feedback N.leftIn N.rightIn N.edge N.leftOut N.rightOut
        (M.leftIn ○ relStar M.edge ○ M.leftOut)
  · rw [hR]
    have hr := relStar_general_feedback M.rightIn M.leftIn M.edge M.rightOut M.leftOut
      (N.rightIn ○ relStar N.edge ○ N.rightOut)
    have hrot := comp_relStar_rotate (N.rightIn ○ relStar N.edge ○ N.rightOut)
      (M.leftIn ○ relStar M.edge ○ M.leftOut)
    calc
      _ = M.summary.right ∪ (M.summary.backward ○
          relStar (N.summary.right ○ M.summary.left) ○ N.summary.right ○
            M.summary.forward) := by
        simpa only [summary, SetRel.comp_assoc] using hr
      _ = _ := by
        simpa only [summary, Diagram.comp, SetRel.comp_assoc] using
          congrArg (fun K => M.summary.right ∪ (M.summary.backward ○ K ○
            M.summary.forward)) hrot.symm

end Network

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Network
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.Network.summary_join := @_root_.OAI.TwoWayComplementation.Network.summary_join
