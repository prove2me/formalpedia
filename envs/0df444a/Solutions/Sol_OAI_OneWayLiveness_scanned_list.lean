-- Prove2me | solution 1 for OAI.OneWayLiveness.scanned_list
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:10:55.880231+00:00
-- url     : https://prove2.me/submissions/aab16cdd-fefa-4cb3-b6bf-abc9e02e07e4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Recognition.lean:L8-L24
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.scanned_list. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss
import Definitions.Def_OAI_Combinatorics_Automata_Recognition

-- ---- from OAI.Combinatorics.Automata.Recognition ----
namespace OAI

namespace OneWayLiveness

/-- The scanned cells are the two fixed markers surrounding the ordinary word. -/
lemma scanned_list {Alpha : Type} (w : List Alpha) :
    List.ofFn (scanned w) = Symbol.left :: (w.map Symbol.letter ++ [Symbol.right]) := by
  rw [List.ofFn_succ]
  have hleft : scanned w (0 : Fin (w.length+2)) = .left := by simp [scanned]
  rw [hleft, List.ofFn_succ']
  congr 1
  have hre : scanned w (Fin.last (w.length)).succ = .right :=
    (scanned_eq_right_iff _ _).mpr rfl
  rw [hre, List.concat_eq_append]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn, List.getElem_map]
    simp [scanned, show i+1 < w.length+1 by omega]

namespace CellNetwork
variable {Alpha Q : Type} [Fintype Q] (M : Machine Alpha Q)

end CellNetwork

namespace Machine
variable {H Q : Type} [Fintype H] [Fintype Q] (M : Machine (BRel H) Q)

end Machine

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness


theorem solution : type_of% @_root_.OAI.OneWayLiveness.scanned_list := @_root_.OAI.OneWayLiveness.scanned_list
