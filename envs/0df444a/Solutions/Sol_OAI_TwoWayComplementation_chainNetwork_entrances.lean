-- Prove2me | solution 1 for OAI.TwoWayComplementation.chainNetwork_entrances
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:29:27.384531+00:00
-- url     : https://prove2.me/submissions/1f1faabf-7472-4f0d-aabd-fd488035e6d5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Chain.lean:L108-L132
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.chainNetwork_entrances. The node keeps its source
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

/-- Entrances attach exactly to the first and last cells with their unchanged labels. -/
theorem chainNetwork_entrances {Sigma : Type*} {m : ℕ}
    (moves : Sigma → Fin 3 → SetRel (Fin m) (Fin m)) (w : List Sigma) (last : Sigma)
    (q : Fin m) (c : ChainNode m w.length) :
    ((q, c) ∈ (chainNetwork moves w last).leftIn ↔ c.position = 0 ∧ q = c.label) ∧
    ((q, c) ∈ (chainNetwork moves w last).rightIn ↔ c.position = w.length ∧ q = c.label) := by
  induction w with
  | nil =>
    change (q = c ↔ 0 = 0 ∧ q = c) ∧ (q = c ↔ 0 = 0 ∧ q = c)
    simp
  | cons a w ih =>
    cases c with
    | inl r =>
      change ((∃ v : Fin m, (Sum.inl r : Fin m ⊕ ChainNode m w.length) = Sum.inl v ∧
          q = v) ↔ 0 = 0 ∧ q = r) ∧
        ((∃ v, (Sum.inl r : Fin m ⊕ ChainNode m w.length) = Sum.inr v ∧
          (q, v) ∈ (chainNetwork moves w last).rightIn) ↔ 0 = w.length + 1 ∧ q = r)
      simp [eq_comm]
    | inr c =>
      change ((∃ v : Fin m, (Sum.inr c : Fin m ⊕ ChainNode m w.length) = Sum.inl v ∧
          q = v) ↔ c.position + 1 = 0 ∧ q = c.label) ∧
        ((∃ v, (Sum.inr c : Fin m ⊕ ChainNode m w.length) = Sum.inr v ∧
          (q, v) ∈ (chainNetwork moves w last).rightIn) ↔
            c.position + 1 = w.length + 1 ∧ q = c.label)
      simpa using (ih c).2

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.chainNetwork_entrances := @_root_.OAI.TwoWayComplementation.chainNetwork_entrances
