-- Prove2me | solution 1 for OAI.TwoWayComplementation.marked_getElem
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:33:57.833403+00:00
-- url     : https://prove2.me/submissions/2970967b-9848-4658-98b5-3a5979daafe4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Tape.lean:L25-L39
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.marked_getElem. The node keeps its source
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

-- ---- from OAI.Combinatorics.TwoWayAutomata.Tape ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Lookup of the explicitly marked list agrees with the automaton's tape lookup. -/
theorem marked_getElem {Sigma : Type*} (w : List Sigma) (p : Fin (w.length + 2)) :
    ((Sum.inl 0 : Fin 2 ⊕ Sigma) :: (w.map Sum.inr ++ [Sum.inl 1]))[p.val]'(by simp; omega) =
      tapeSymbol w p := by
  obtain ⟨p, hp⟩ := p
  cases p with
  | zero => rfl
  | succ p =>
    by_cases h : p = w.length
    · subst p
      simp [tapeSymbol]
    · have hlt : p < w.length := by omega
      rw [List.getElem_cons_succ, List.getElem_append_left (by simpa using hlt),
        List.getElem_map]
      simp [tapeSymbol, h]

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.marked_getElem := @_root_.OAI.TwoWayComplementation.marked_getElem
