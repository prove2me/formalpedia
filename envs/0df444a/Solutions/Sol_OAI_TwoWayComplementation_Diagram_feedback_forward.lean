-- Prove2me | solution 1 for OAI.TwoWayComplementation.Diagram.feedback_forward
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:18:28.109303+00:00
-- url     : https://prove2.me/submissions/159ebabb-eef3-4a0b-83c9-d1634a316e3d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Diagram.lean:L142-L201
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.Diagram.feedback_forward. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram

-- ---- from OAI.Combinatorics.TwoWayAutomata.Relations ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

theorem feedback_insert {α : Type*} (E B : SetRel α α) :
    relStar (E ○ B) ○ E ○ relStar (B ○ E) = E ○ relStar (B ○ E) := by
  rw [← comp_relStar_rotate, SetRel.comp_assoc, relStar_comp_self]

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Diagram ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem feedback_forward {m : ℕ} (e : Diagram m) (R L : SetRel (Fin m) (Fin m))
    {p q : Fin m} :
    ((false, p), (true, q)) ∈ e.feedback R L ↔
      (p, q) ∈ relStar (e.left ○ R) ○ e.forward ○
        relStar (L ○ (e.right ∪ (e.backward ○ R ○ relStar (e.left ○ R) ○ e.forward))) := by
  let S := relStar (e.left ○ R)
  let P := e.right ∪ (e.backward ○ R ○ S ○ e.forward)
  let V := relStar (L ○ P)
  let E := e.portRelation
  let B := bounceRelation R L
  have hbound {a b : Bool × Fin m} (hab : (a, b) ∈ relStar (B ○ E)) (hb : b.1 = true) :
      (a.2, b.2) ∈ if a.1 then V else R ○ S ○ e.forward ○ V := by
    induction hab using Relation.ReflTransGen.head_induction_on with
    | refl => simp only [hb, ite_true]; exact Relation.ReflTransGen.refl
    | @head a c hac _ ih =>
      obtain ⟨mid, hB, hE⟩ := hac
      obtain ⟨sa, x⟩ := a
      obtain ⟨sc, y⟩ := c
      obtain ⟨sm, z⟩ := mid
      obtain ⟨hside, hreturn⟩ := hB
      change sa = sm at hside
      subst sm
      cases sa <;> cases sc
      · obtain ⟨t, ⟨u, ⟨v, hyv, hvu⟩, hut⟩, htb⟩ := ih
        exact ⟨t, ⟨u, ⟨z, hreturn, hvu.head ⟨y, hE, hyv⟩⟩, hut⟩, htb⟩
      · exact ⟨y, ⟨z, ⟨z, hreturn, .refl⟩, hE⟩, ih⟩
      · obtain ⟨t, ⟨u, ⟨v, hyv, hvu⟩, hut⟩, htb⟩ := ih
        exact htb.head ⟨z, hreturn, Or.inr ⟨u, ⟨v, ⟨y, hE, hyv⟩, hvu⟩, hut⟩⟩
      · exact ih.head ⟨z, hreturn, Or.inl hE⟩
  constructor
  · rintro ⟨⟨side, x⟩, hfirst, hrest⟩
    have h := hbound hrest rfl
    cases side
    · obtain ⟨t, ⟨u, ⟨v, hxv, hvu⟩, hut⟩, htq⟩ := h
      exact ⟨t, ⟨u, hvu.head ⟨x, hfirst, hxv⟩, hut⟩, htq⟩
    · exact ⟨x, ⟨p, .refl, hfirst⟩, h⟩
  · intro hpq
    have hS {x y : Fin m} (hxy : (x, y) ∈ S) :
        ((false, x), (false, y)) ∈ relStar (E ○ B) := by
      exact hxy.lift (fun a => (false, a)) (fun _ _ ⟨z, hxz, hzy⟩ =>
        ⟨(false, z), hxz, rfl, hzy⟩)
    have hV {x y : Fin m} (hxy : (x, y) ∈ V) :
        ((true, x), (true, y)) ∈ relStar (B ○ E) := by
      apply hxy.lift' (fun a => (true, a))
      rintro a b ⟨z, haz, hzb⟩
      rcases hzb with hright | ⟨u, ⟨v, ⟨w, hzw, hwv⟩, hvu⟩, hub⟩
      · exact Relation.ReflTransGen.single ⟨(true, z), ⟨rfl, haz⟩, hright⟩
      · have hmid : ((false, w), (false, u)) ∈ B ○ relStar (E ○ B) :=
          ⟨(false, v), ⟨rfl, hwv⟩, hS hvu⟩
        rw [comp_relStar_rotate] at hmid
        obtain ⟨c, hwc, hcu⟩ := hmid
        have htail : ((false, w), (true, b)) ∈ relStar (B ○ E) :=
          hwc.tail ⟨(false, u), hcu, hub⟩
        have hstart : ((true, a), (false, w)) ∈ B ○ E :=
          ⟨(true, z), ⟨rfl, haz⟩, hzw⟩
        exact htail.head hstart
    obtain ⟨b, ⟨a, hpa, hab⟩, hbq⟩ := hpq
    have h : ((false, p), (true, q)) ∈ relStar (E ○ B) ○ E ○ relStar (B ○ E) :=
      ⟨(true, b), ⟨(false, a), hS hpa, hab⟩, hV hbq⟩
    rwa [feedback_insert] at h

end Diagram

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.Diagram.feedback_forward := @_root_.OAI.TwoWayComplementation.Diagram.feedback_forward
