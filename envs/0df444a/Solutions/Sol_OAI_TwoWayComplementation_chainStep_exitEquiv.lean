-- Prove2me | solution 1 for OAI.TwoWayComplementation.chainStep_exitEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:35:14.548551+00:00
-- url     : https://prove2.me/submissions/97a2c775-e465-430d-9e2e-8c4ee6bbc1d6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Tape.lean:L103-L146
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.chainStep_exitEquiv. The node keeps its source
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
import Theorems.Thm_OAI_TwoWayComplementation_chainNetwork_edges
import Theorems.Thm_OAI_TwoWayComplementation_chainNetwork_exits

-- ---- from OAI.Combinatorics.TwoWayAutomata.Tape ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Chain symbols agree with ordinary zero-based lookup of the nonempty symbol list. -/
theorem chainSymbol_getElem {Sigma : Type*} {m : ℕ} (w : List Sigma) (last : Sigma)
    (c : ChainNode m w.length) :
    chainSymbol w last c = (w ++ [last])[c.position]'(by
      have := c.position_le
      simp only [List.length_append, List.length_singleton]
      omega) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases c with
    | inl q => rfl
    | inr c => simpa only [chainSymbol, ChainNode.position, List.cons_append,
        List.getElem_cons_succ] using ih c

/-- A cell's scanned symbol depends only on its position. -/
theorem chainSymbol_position {Sigma : Type*} {m : ℕ} (w : List Sigma) (last : Sigma)
    (c d : ChainNode m w.length) (hp : c.position = d.position) :
    chainSymbol w last c = chainSymbol w last d := by
  rw [chainSymbol_getElem, chainSymbol_getElem]
  simp only [hp]

/-- The joined network with terminal exits has exactly the bounded tape's local edges. -/
theorem chainStep_exitEquiv {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (x y : ChainNode m w.length ⊕ Fin m) :
    (ChainNode.exitEquiv m w.length x, ChainNode.exitEquiv m w.length y) ∈
        chainStep moves w last ↔
      (x, y) ∈ blockRelation (chainNetwork moves w last).edge
        (chainNetwork moves w last).rightOut ∅ ∅ := by
  cases x with
  | inl c =>
    cases y with
    | inl d =>
      change (∃ a : ChainNode m w.length, c.position = a.position ∧ ∃ move : Fin 3,
          (c.label, d.label) ∈ moves (chainSymbol w last a) move ∧
            (d.position : ℤ) = (c.position : ℤ) + (move.val : ℤ) - 1) ↔
        (c, d) ∈ (chainNetwork moves w last).edge
      rw [chainNetwork_edges]
      constructor
      · rintro ⟨a, hp, move, h, hd⟩
        exact ⟨move, (chainSymbol_position w last a c hp.symm) ▸ h, hd⟩
      · rintro ⟨move, h, hd⟩
        exact ⟨c, rfl, move, h, hd⟩
    | inr q =>
      change (∃ a : ChainNode m w.length, c.position = a.position ∧ ∃ move : Fin 3,
          (c.label, q) ∈ moves (chainSymbol w last a) move ∧
            ((w.length + 1 : ℕ) : ℤ) = (c.position : ℤ) + (move.val : ℤ) - 1) ↔
        (c, q) ∈ (chainNetwork moves w last).rightOut
      rw [(chainNetwork_exits moves w last c q).2]
      constructor
      · rintro ⟨a, hp, move, h, hd⟩
        have hc := c.position_le
        have hm : move = 2 := Fin.ext (by have := move.isLt; omega)
        refine ⟨by have := move.isLt; omega, ?_⟩
        simpa only [← chainSymbol_position w last c a hp, hm] using h
      · rintro ⟨hp, h⟩
        exact ⟨c, rfl, 2, h, by rw [hp]; push_cast; omega⟩
  | inr q =>
    change (∃ a : ChainNode m w.length, w.length + 1 = a.position ∧ _) ↔ _
    constructor
    · rintro ⟨a, hp, _⟩
      have := a.position_le
      omega
    · intro h
      cases y <;> exact h.elim

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.chainStep_exitEquiv := @_root_.OAI.TwoWayComplementation.chainStep_exitEquiv
