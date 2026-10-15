-- Prove2me | solution 1 for OAI.TwoWayComplementation.Diagram.context_surviving
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:20:25.588018+00:00
-- url     : https://prove2.me/submissions/ed3dba2c-26d0-45f0-b957-706935439236

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Diagram.lean:L304-L318
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.Diagram.context_surviving. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_feedback_forward

-- ---- from OAI.Combinatorics.TwoWayAutomata.Diagram ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem feedback_reflect_map {m : ℕ} (e : Diagram m) (R L : SetRel (Fin m) (Fin m))
    {s t : Bool} {p q : Fin m} (h : ((s, p), (t, q)) ∈ e.feedback R L) :
    ((!s, p), (!t, q)) ∈ (reflect e).feedback L R := by
  have hE {a b : Bool × Fin m} (hab : (a, b) ∈ e.portRelation) :
      ((!a.1, a.2), (!b.1, b.2)) ∈ (reflect e).portRelation := by
    obtain ⟨sa, a⟩ := a
    obtain ⟨sb, b⟩ := b
    cases sa <;> cases sb <;> exact hab
  have hB {a b : Bool × Fin m} (hab : (a, b) ∈ bounceRelation R L) :
      ((!a.1, a.2), (!b.1, b.2)) ∈ bounceRelation L R := by
    obtain ⟨sa, x⟩ := a
    obtain ⟨sb, y⟩ := b
    obtain ⟨hside, hreturn⟩ := hab
    refine ⟨congrArg Bool.not hside, ?_⟩
    cases sa <;> exact hreturn
  obtain ⟨a, hfirst, hrest⟩ := h
  refine ⟨(!a.1, a.2), hE hfirst, ?_⟩
  exact hrest.lift (fun a => (!a.1, a.2))
    (p := fun a b => (a, b) ∈ bounceRelation L R ○ (reflect e).portRelation)
    (fun _ _ ⟨b, hab, hbc⟩ => ⟨(!b.1, b.2), hB hab, hE hbc⟩)

theorem mem_feedback_reflect {m : ℕ} (e : Diagram m) (R L : SetRel (Fin m) (Fin m))
    {s t : Bool} {p q : Fin m} :
    ((s, p), (t, q)) ∈ (reflect e).feedback L R ↔
      ((!s, p), (!t, q)) ∈ e.feedback R L := by
  constructor
  · exact feedback_reflect_map (reflect e) L R
  · intro h
    simpa only [Bool.not_not] using feedback_reflect_map e R L h

theorem context_forward_iff {m : ℕ} (u e v : Diagram m) {p q : Fin m} :
    (p, q) ∈ (comp (comp u e) v).forward ↔
      ∃ a b, (p, a) ∈ u.forward ∧
        ((false, a), (true, b)) ∈ e.feedback u.right v.left ∧ (b, q) ∈ v.forward := by
  simp only [feedback_forward, comp, SetRel.comp_assoc, SetRel.mem_comp]
  aesop

theorem context_through_iff {m : ℕ} (u e v : Diagram m) (positive : Bool) {p q : Fin m} :
    (p, q) ∈ (comp (comp u e) v).through positive ↔
      ∃ a b, (p, a) ∈ (if positive then u.forward else v.backward) ∧
        ((!positive, a), (positive, b)) ∈ e.feedback u.right v.left ∧
        (b, q) ∈ (if positive then v.forward else u.backward) := by
  cases positive
  · have h := context_forward_iff (reflect v) (reflect e) (reflect u) (p := p) (q := q)
    have hd : comp (comp (reflect v) (reflect e)) (reflect u) =
        reflect (comp (comp u e) v) := by
      rw [comp_assoc, ← reflect_comp, ← reflect_comp]
    rw [hd] at h
    simp only [mem_feedback_reflect] at h
    exact h
  · exact context_forward_iff u e v

theorem context_surviving {m : ℕ} (d u e v : Diagram m) (positive : Bool) :
    d.surviving (comp (comp u e) v) positive =
      contextEntry d u v positive ○ e.feedback u.right v.left ○ contextExit d u v positive := by
  ext ⟨p, q⟩
  constructor
  · rintro ⟨b, ⟨a, hpa, hab⟩, hbq⟩
    obtain ⟨c, f, hac, hcf, hfb⟩ := (context_through_iff u e v positive).mp hab
    exact ⟨(positive, f), ⟨(!positive, c), ⟨rfl, a, hpa, hac⟩, hcf⟩,
      ⟨rfl, b, hfb, hbq⟩⟩
  · rintro ⟨⟨t, b⟩, ⟨⟨s, a⟩, ⟨hs, c, hpc, hca⟩, hab⟩, ⟨ht, f, hbf, hfq⟩⟩
    change s = !positive at hs
    change t = positive at ht
    subst s
    subst t
    exact ⟨f, ⟨c, hpc, (context_through_iff u e v positive).mpr ⟨a, b, hca, hab, hbf⟩⟩, hfq⟩

end Diagram

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.Diagram.context_surviving := @_root_.OAI.TwoWayComplementation.Diagram.context_surviving
