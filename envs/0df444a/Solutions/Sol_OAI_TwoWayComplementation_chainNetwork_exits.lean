-- Prove2me | solution 1 for OAI.TwoWayComplementation.chainNetwork_exits
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:30:42.278905+00:00
-- url     : https://prove2.me/submissions/6231cec9-7b4b-4784-a674-79997daf323e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Chain.lean:L134-L163
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.chainNetwork_exits. The node keeps its source
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

-- ---- from OAI.Combinatorics.TwoWayAutomata.Chain ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace ChainNode

end ChainNode

/-- Only the endpoint cells can exit a chain, using the appropriate moving transition. -/
theorem chainNetwork_exits {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (c : ChainNode m w.length) (q : Fin m) :
    ((c, q) ∈ (chainNetwork moves w last).leftOut ↔
      c.position = 0 ∧ (c.label, q) ∈ moves (chainSymbol w last c) 0) ∧
    ((c, q) ∈ (chainNetwork moves w last).rightOut ↔
      c.position = w.length ∧ (c.label, q) ∈ moves (chainSymbol w last c) 2) := by
  induction w with
  | nil =>
    change ((c, q) ∈ moves last 0 ↔ 0 = 0 ∧ (c, q) ∈ moves last 0) ∧
      ((c, q) ∈ moves last 2 ↔ 0 = 0 ∧ (c, q) ∈ moves last 2)
    simp
  | cons a w ih =>
    cases c with
    | inl r =>
      change ((∃ v : Fin m, (Sum.inl r : Fin m ⊕ ChainNode m w.length) = Sum.inl v ∧
          (v, q) ∈ moves a 0) ↔ 0 = 0 ∧ (r, q) ∈ moves a 0) ∧
        ((∃ v, (Sum.inl r : Fin m ⊕ ChainNode m w.length) = Sum.inr v ∧
          (v, q) ∈ (chainNetwork moves w last).rightOut) ↔
            0 = w.length + 1 ∧ (r, q) ∈ moves a 2)
      simp
    | inr c =>
      change ((∃ v : Fin m, (Sum.inr c : Fin m ⊕ ChainNode m w.length) = Sum.inl v ∧
          (v, q) ∈ moves a 0) ↔ c.position + 1 = 0 ∧
            (c.label, q) ∈ moves (chainSymbol w last c) 0) ∧
        ((∃ v, (Sum.inr c : Fin m ⊕ ChainNode m w.length) = Sum.inr v ∧
          (v, q) ∈ (chainNetwork moves w last).rightOut) ↔
            c.position + 1 = w.length + 1 ∧ (c.label, q) ∈ moves (chainSymbol w last c) 2)
      simpa using (ih c).2

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.chainNetwork_exits := @_root_.OAI.TwoWayComplementation.chainNetwork_exits
