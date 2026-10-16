-- Prove2me | solution 1 for OAI.TwoWayComplementation.complementation_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:40:50.031029+00:00
-- url     : https://prove2.me/submissions/04225551-12dc-42ba-bff0-adfc3d2ccb7c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Main.lean:L10-L28
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.complementation_lower_bound. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Chain
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Tape
import Theorems.Thm_OAI_TwoWayComplementation_TwoNFA_diagram_representation
import Theorems.Thm_OAI_TwoWayComplementation_TwoNFA_reindex_language
import Theorems.Thm_OAI_TwoWayComplementation_diagram_recognition_lower_bound
import Theorems.Thm_OAI_TwoWayComplementation_sourceProductive_of_step

-- ---- from OAI.Combinatorics.TwoWayAutomata.Source ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

theorem sourceAutomaton_sound {H : Type*} (w : List (SetRel H H))
    (hw : w ∈ (sourceAutomaton H).language) : (relationProduct w).Nonempty := by
  obtain ⟨c, hc, hrun⟩ := hw
  have hproductive : c ∈ sourceProductive w := by
    change c.1 ∈ ({some none} : Set (Option (Option H))) at hc
    have hstate : c.1 = some none := hc
    simp only [sourceProductive, Set.mem_ofPred_eq, hstate]
  have hback : ∀ {c d}, (c, d) ∈ relStar ((sourceAutomaton H).step w) →
      d ∈ sourceProductive w → c ∈ sourceProductive w := by
    intro c d h
    induction h with
    | refl => exact id
    | tail _ hstep ih => exact fun hd => ih (sourceProductive_of_step w hstep hd)
  exact (hback hrun hproductive).2

theorem sourceAutomaton_suffix_run {H : Type*} (w : List (SetRel H H))
    (u v : List (SetRel H H)) (hw : w = u ++ v) {p q : H}
    (hpq : (p, q) ∈ relationProduct v) :
    ((some (some p), ⟨u.length + 1, by simp [hw]⟩),
      (some none, ⟨w.length + 1, by omega⟩)) ∈ relStar ((sourceAutomaton H).step w) := by
  induction v generalizing u p with
  | nil =>
    have hlen : w.length = u.length := by simp [hw]
    apply Relation.ReflTransGen.single
    refine ⟨1, ?_, ?_⟩
    · simp [sourceAutomaton, tapeSymbol, hlen]
    · simp [hlen]
  | cons R v ih =>
    obtain ⟨r, hpr, hrq⟩ := hpq
    have hlen : w.length = u.length + (v.length + 1) := by simp [hw]
    have hw' : w = (u ++ [R]) ++ v := by
      simpa only [List.append_assoc, List.singleton_append] using hw
    have htail := ih (u ++ [R]) hw' hrq
    apply htail.head
    refine ⟨2, ?_, ?_⟩
    · have hsymbol : tapeSymbol w ⟨u.length + 1, by omega⟩ = Sum.inr R := by
        simp [tapeSymbol, hw, List.getElem_append_right]
      change (some (some r), (2 : Fin 3)) ∈
        (sourceAutomaton H).transition (some (some p)) (tapeSymbol w _)
      rw [hsymbol]
      exact ⟨r, hpr, rfl⟩
    · simp [List.length_append]
      omega

/-- The explicit machine recognizes nonempty relation products. -/
theorem sourceAutomaton_language (H : Type*) :
    (sourceAutomaton H).language = sourceLanguage H := by
  ext w
  constructor
  · exact sourceAutomaton_sound w
  · rintro ⟨⟨p, q⟩, hpq⟩
    refine ⟨(some none, ⟨w.length + 1, by omega⟩), rfl, ?_⟩
    have hrun := sourceAutomaton_suffix_run w [] w (by simp) hpq
    apply hrun.head
    refine ⟨2, ?_, ?_⟩
    · exact ⟨p, rfl⟩
    · norm_num

/-- The source language on `h` labels is recognized using exactly `h + 2` states. -/
theorem sourceLanguage_state_bound (H : Type*) [Fintype H] :
    ∃ A : TwoNFA (SetRel H H) (Fin (Fintype.card H + 2)), A.language = sourceLanguage H := by
  classical
  let e : Option (Option H) ≃ Fin (Fintype.card H + 2) :=
    (Fintype.equivFin _).trans (finCongr (by simp))
  refine ⟨(sourceAutomaton H).reindex e, ?_⟩
  rw [TwoNFA.reindex_language, sourceAutomaton_language]

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Main ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- An n-state source language requires exponentially many states for any 2NFA complement. -/
theorem complementation_lower_bound (n : ℕ) (hn : 4 ≤ n) :
    ∃ A : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin n),
      ∀ s : ℕ, ∀ B : TwoNFA (SetRel (Fin (n - 2)) (Fin (n - 2))) (Fin s),
        B.language = A.languageᶜ → 2 ^ ((n - 4) / 127) ≤ 2 * (s + 1) := by
  obtain ⟨A, hA⟩ := sourceLanguage_state_bound (Fin (n - 2))
  have hsize : Fintype.card (Fin (n - 2)) + 2 = n := by simp; omega
  let A' := A.reindex (finCongr hsize)
  refine ⟨A', ?_⟩
  intro s B hB
  have hAlang : A'.language = sourceLanguage (Fin (n - 2)) := by
    rw [TwoNFA.reindex_language, hA]
  obtain ⟨τ, l, r, a, b, hzero, hmul, hrecognition⟩ := B.diagram_representation
  have hbound := diagram_recognition_lower_bound (n - 2) (s + 1) (by omega) (by omega)
    τ hzero hmul l r a b (by
      intro w
      rw [← hrecognition w, hB, hAlang]
      rfl)
  simpa only [lossBound, Nat.sub_sub, Nat.reduceAdd] using hbound

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.complementation_lower_bound := @_root_.OAI.TwoWayComplementation.complementation_lower_bound
