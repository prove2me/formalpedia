-- Prove2me | solution 1 for OAI.TwoWayComplementation.TwoNFA.augmented_acceptance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:18:46.333185+00:00
-- url     : https://prove2.me/submissions/68b76cc6-fbff-4d56-9a6d-31c1c9dfdcbc

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Normalization.lean:L105-L123
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.TwoNFA.augmented_acceptance. The node keeps its source
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
import Theorems.Thm_OAI_TwoWayComplementation_TwoNFA_augmented_run_cases
import Theorems.Thm_OAI_TwoWayComplementation_TwoNFA_augmented_sink_exit

-- ---- from OAI.Combinatorics.TwoWayAutomata.Normalization ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace TwoNFA

/-- Finite acceptance is equivalent to reaching the designated augmented exit. -/
theorem augmented_acceptance {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma) :
    w ∈ A.language ↔
      (augmentConfig (A.initial, ⟨0, by omega⟩), (none, ⟨w.length + 2, by omega⟩)) ∈
        relStar (A.augmentedStep w) := by
  constructor
  · rintro ⟨c, hc, hrun⟩
    have hlift := hrun.lift augmentConfig
      (p := fun c d => (c, d) ∈ A.augmentedStep w)
      (fun x y h => Or.inl ⟨x, y, rfl, rfl, h⟩)
    have hjump : (augmentConfig c, (none, c.2.castSucc)) ∈ A.augmentedStep w :=
      Or.inr (Or.inl ⟨c.1, c.2, rfl, rfl, hc⟩)
    exact (hlift.tail hjump).trans (A.augmented_sink_exit w c.2.castSucc)
  · intro hrun
    rcases A.augmented_run_cases w hrun with h | ⟨c, heq, _⟩
    · exact h
    · have hnone : (none : Option Q) = some c.1 :=
        congrArg (fun p : Option Q × Fin (w.length + 3) => p.1) heq
      cases hnone

end TwoNFA

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.TwoNFA
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.TwoNFA.augmented_acceptance := @_root_.OAI.TwoWayComplementation.TwoNFA.augmented_acceptance
