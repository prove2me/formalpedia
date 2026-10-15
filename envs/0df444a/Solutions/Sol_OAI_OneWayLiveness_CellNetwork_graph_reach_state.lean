-- Prove2me | solution 1 for OAI.OneWayLiveness.CellNetwork.graph_reach_state
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:42:19.839975+00:00
-- url     : https://prove2.me/submissions/a1cda555-ca93-4fcd-85ca-2d5df6e47f44

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Network.lean:L356-L373
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.CellNetwork.graph_reach_state. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Theorems.Thm_OAI_OneWayLiveness_CellNetwork_graph_step_from_state

-- ---- from OAI.Combinatorics.Automata.Network ----
namespace OAI

namespace OneWayLiveness
namespace CellNetwork
variable (Q : Type)

variable {Q} {Alpha : Type} (M : Machine Alpha Q)

variable (Q)
variable {Q}

lemma stateVertex_injective (w : List Alpha) : Function.Injective (stateVertex (Q := Q) w) := by
  rintro ⟨i,p⟩ ⟨j,q⟩ h
  simpa [stateVertex] using h

lemma graph_reach_state (finish : Q) (w : List Alpha) (c c' : Machine.Config (Q := Q) w) :
    (graph M finish w).Reach (stateVertex w c) (stateVertex w c') ↔
      Relation.ReflTransGen (M.Step w) c c' := by
  constructor
  · intro h
    have aux (v : Vertex Q w.length) (hv : (graph M finish w).Reach (stateVertex w c) v) :
        ∃ d, v = stateVertex w d ∧ Relation.ReflTransGen (M.Step w) c d := by
      induction hv with
      | refl => exact ⟨c,rfl,.refl⟩
      | @tail v v' _ hvv ih =>
        obtain ⟨d,rfl,hd⟩ := ih
        obtain ⟨d',he,hs⟩ := (graph_step_from_state M finish w d v').mp hvv
        exact ⟨d',he,hd.tail hs⟩
    obtain ⟨d,hd,hp⟩ := aux _ h
    exact stateVertex_injective w hd ▸ hp
  · intro h
    exact h.lift (stateVertex w) (fun a b hab =>
      (graph_step_from_state M finish w a _).mpr ⟨b,rfl,hab⟩)

end CellNetwork
end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness OAI.OneWayLiveness.CellNetwork


theorem solution : type_of% @_root_.OAI.OneWayLiveness.CellNetwork.graph_reach_state := @_root_.OAI.OneWayLiveness.CellNetwork.graph_reach_state
