-- Prove2me | solution 1 for OAI.TwoWayComplementation.exists_hub_families
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:03:58.03588+00:00
-- url     : https://prove2.me/submissions/8ff718ff-931d-4911-ba7d-1ba19a315460

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Retained.lean:L9-L37
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.exists_hub_families. The node keeps its source
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

-- ---- from OAI.Combinatorics.TwoWayAutomata.Retained ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Select the two 64-point families and a distinct hub. -/
theorem exists_hub_families {H : Type*} [Finite H] (hh : 129 ≤ Nat.card H) :
    ∃ u v : Fin 64 ↪ H, ∃ z : H,
      (∀ i j, u i ≠ v j) ∧ (∀ i, u i ≠ z) ∧ (∀ j, v j ≠ z) := by
  classical
  let := Fintype.ofFinite H
  obtain ⟨e⟩ : Nonempty (Fin 129 ↪ H) := Function.Embedding.nonempty_of_card_le (by simpa using hh)
  let u : Fin 64 ↪ H :=
    ⟨fun i => e ⟨i.val, by omega⟩,
      fun a b h => Fin.ext (congrArg (fun k : Fin 129 => k.val) (e.injective h))⟩
  let v : Fin 64 ↪ H := ⟨fun i => e ⟨64 + i.val, by omega⟩, by
    intro a b h
    have he := congrArg (fun k : Fin 129 => k.val) (e.injective h)
    apply Fin.ext
    change 64 + a.val = 64 + b.val at he
    omega⟩
  refine ⟨u, v, e 128, ?_, ?_, ?_⟩
  · intro i j h
    have he := congrArg (fun k : Fin 129 => k.val) (e.injective h)
    change i.val = 64 + j.val at he
    omega
  · intro i h
    have he := congrArg (fun k : Fin 129 => k.val) (e.injective h)
    change i.val = 128 at he
    omega
  · intro j h
    have he := congrArg (fun k : Fin 129 => k.val) (e.injective h)
    change 64 + j.val = 128 at he
    omega

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.exists_hub_families := @_root_.OAI.TwoWayComplementation.exists_hub_families
