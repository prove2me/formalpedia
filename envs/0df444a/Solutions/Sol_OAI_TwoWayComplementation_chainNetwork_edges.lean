-- Prove2me | solution 1 for OAI.TwoWayComplementation.chainNetwork_edges
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:32:30.594077+00:00
-- url     : https://prove2.me/submissions/0700b7dd-46dd-4170-804a-91d65c6394ef

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Chain.lean:L165-L224
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.chainNetwork_edges. The node keeps its source
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
import Theorems.Thm_OAI_TwoWayComplementation_chainNetwork_entrances
import Theorems.Thm_OAI_TwoWayComplementation_chainNetwork_exits

-- ---- from OAI.Combinatorics.TwoWayAutomata.Chain ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace ChainNode

end ChainNode

/-- Internal edges are precisely local transitions that stay within the chain. -/
theorem chainNetwork_edges {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (c d : ChainNode m w.length) :
    (c, d) ∈ (chainNetwork moves w last).edge ↔
      ∃ move : Fin 3, (c.label, d.label) ∈ moves (chainSymbol w last c) move ∧
        (d.position : ℤ) = (c.position : ℤ) + (move.val : ℤ) - 1 := by
  induction w with
  | nil =>
    change (c, d) ∈ moves last 1 ↔
      ∃ move : Fin 3, (c, d) ∈ moves last move ∧ (0 : ℤ) = 0 + (move.val : ℤ) - 1
    constructor
    · exact fun h => ⟨1, h, by norm_num⟩
    · rintro ⟨move, h, hp⟩
      have hm : move = 1 := Fin.ext (by norm_num at hp; omega)
      simpa only [hm] using h
  | cons a w ih =>
    cases c with
    | inl q =>
      cases d with
      | inl r =>
        change (q, r) ∈ moves a 1 ↔
          ∃ move : Fin 3, (q, r) ∈ moves a move ∧ (0 : ℤ) = 0 + (move.val : ℤ) - 1
        constructor
        · exact fun h => ⟨1, h, by norm_num⟩
        · rintro ⟨move, h, hp⟩
          have hm : move = 1 := Fin.ext (by norm_num at hp; omega)
          simpa only [hm] using h
      | inr d =>
        change (q, d) ∈ moves a 2 ○ (chainNetwork moves w last).leftIn ↔ _
        constructor
        · rintro ⟨r, hqr, hrd⟩
          obtain ⟨hp, hq⟩ := (chainNetwork_entrances moves w last r d).1.mp hrd
          exact ⟨2, hq ▸ hqr, by dsimp [ChainNode.position]; rw [hp]; norm_num⟩
        · rintro ⟨move, h, hp⟩
          change ((d.position + 1 : ℕ) : ℤ) = 0 + (move.val : ℤ) - 1 at hp
          have hm : move = 2 := Fin.ext (by have := move.isLt; omega)
          have hd : d.position = 0 := by have := move.isLt; omega
          refine ⟨d.label, ?_, (chainNetwork_entrances moves w last d.label d).1.mpr ⟨hd, rfl⟩⟩
          simpa only [ChainNode.label, chainSymbol, hm] using h
    | inr c =>
      cases d with
      | inl r =>
        change (c, r) ∈ (chainNetwork moves w last).leftOut ○ SetRel.id ↔ _
        rw [SetRel.comp_id]
        constructor
        · intro h
          obtain ⟨hp, hq⟩ := (chainNetwork_exits moves w last c r).1.mp h
          exact ⟨0, hq, by dsimp [ChainNode.position]; rw [hp]; norm_num⟩
        · rintro ⟨move, h, hp⟩
          change (0 : ℤ) = ((c.position + 1 : ℕ) : ℤ) + (move.val : ℤ) - 1 at hp
          have hm : move = 0 := Fin.ext (by omega)
          have hc : c.position = 0 := by omega
          refine (chainNetwork_exits moves w last c r).1.mpr ⟨hc, ?_⟩
          simpa only [ChainNode.label, chainSymbol, hm] using h
      | inr d =>
        change (c, d) ∈ (chainNetwork moves w last).edge ↔ _
        rw [ih c d]
        simp only [ChainNode.label, chainSymbol, ChainNode.position, Nat.cast_add, Nat.cast_one]
        constructor <;> rintro ⟨move, h, hp⟩ <;> exact ⟨move, h, by omega⟩

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.chainNetwork_edges := @_root_.OAI.TwoWayComplementation.chainNetwork_edges
