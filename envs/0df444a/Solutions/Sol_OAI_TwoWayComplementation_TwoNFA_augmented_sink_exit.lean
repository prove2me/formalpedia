-- Prove2me | solution 1 for OAI.TwoWayComplementation.TwoNFA.augmented_sink_exit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:17:13.575192+00:00
-- url     : https://prove2.me/submissions/b0159b02-8698-42c4-a37b-e68c043fd635

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Normalization.lean:L85-L103
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.TwoNFA.augmented_sink_exit. The node keeps its source
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

-- ---- from OAI.Combinatorics.TwoWayAutomata.Normalization ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace TwoNFA

/-- The fresh state can sweep from any position to the designated right exit. -/
theorem augmented_sink_exit {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma)
    (p : Fin (w.length + 3)) :
    ((none, p), (none, ⟨w.length + 2, by omega⟩)) ∈ relStar (A.augmentedStep w) := by
  have hsweep : ∀ k, ∀ p : Fin (w.length + 3), p.val + k = w.length + 2 →
      ((none, p), (none, ⟨w.length + 2, by omega⟩)) ∈ relStar (A.augmentedStep w) := by
    intro k
    induction k with
    | zero =>
      intro p hp
      have hlast : p = ⟨w.length + 2, by omega⟩ := Fin.ext (by omega)
      rw [hlast]
      exact .refl
    | succ k ih =>
      intro p hp
      let next : Fin (w.length + 3) := ⟨p.val + 1, by omega⟩
      have hnext : next.val + k = w.length + 2 := by dsimp [next]; omega
      exact (ih next hnext).head (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  exact hsweep (w.length + 2 - p.val) p (by omega)

end TwoNFA

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.TwoNFA
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.TwoNFA.augmented_sink_exit := @_root_.OAI.TwoWayComplementation.TwoNFA.augmented_sink_exit
