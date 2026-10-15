-- Prove2me | solution 1 for OAI.TwoWayComplementation.TwoNFA.augmented_run_cases
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:16:06.632273+00:00
-- url     : https://prove2.me/submissions/ba37a901-28ee-4faf-973f-106da785df7e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Normalization.lean:L67-L83
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.TwoNFA.augmented_run_cases. The node keeps its source
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

theorem augmentConfig_injective {Q : Type*} {n : ℕ} :
    Function.Injective (augmentConfig : Q × Fin n → Option Q × Fin (n + 1)) := by
  intro a b hab
  have hstate : some a.1 = some b.1 := congrArg Prod.fst hab
  have hpos : a.2.val = b.2.val :=
    congrArg (fun p : Option Q × Fin (n + 1) => p.2.val) hab
  exact Prod.ext (Option.some.inj hstate) (Fin.ext hpos)

/-- Before entering the fresh state, every augmented finite path is an original run. -/
theorem augmented_run_cases {Sigma Q : Type*} (A : TwoNFA Sigma Q) (w : List Sigma)
    {c : Option Q × Fin (w.length + 3)}
    (hrun : (augmentConfig (A.initial, ⟨0, by omega⟩), c) ∈ relStar (A.augmentedStep w)) :
    w ∈ A.language ∨ ∃ x : Q × Fin (w.length + 2),
      c = augmentConfig x ∧ ((A.initial, ⟨0, by omega⟩), x) ∈ relStar (A.step w) := by
  induction hrun with
  | refl => exact Or.inr ⟨(A.initial, ⟨0, by omega⟩), rfl, .refl⟩
  | @tail c d _ hstep ih =>
    rcases ih with haccept | ⟨x, rfl, hxrun⟩
    · exact Or.inl haccept
    rcases hstep with ⟨y, z, hxy, rfl, hyz⟩ | ⟨q, p, hxq, _, hq⟩ | ⟨hnone, _, _⟩
    · have hxy' : x = y := augmentConfig_injective hxy
      exact Or.inr ⟨z, rfl, (hxy' ▸ hxrun).tail hyz⟩
    · have hxq' : x = (q, p) := augmentConfig_injective hxq
      exact Or.inl ⟨(q, p), hq, hxq' ▸ hxrun⟩
    · exact (Option.some_ne_none _ hnone).elim

end TwoNFA

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.TwoNFA
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.TwoNFA.augmented_run_cases := @_root_.OAI.TwoWayComplementation.TwoNFA.augmented_run_cases
