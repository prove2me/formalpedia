-- Prove2me | solution 1 for OAI.TwoWayComplementation.Diagram.surviving_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:28:24.150922+00:00
-- url     : https://prove2.me/submissions/81f57f00-b827-4b1c-b390-d80b755ecbd1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean:L125-L142
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.Diagram.surviving_absorption. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_corner_through_absorption

-- ---- from OAI.Combinatorics.TwoWayAutomata.Classes ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem loopClosure_comp {m : ℕ} (e : Diagram m) (positive : Bool)
    (R : SetRel (Fin m) (Fin m)) :
    e.loopClosure positive ○ (e.loopClosure positive ○ R) = e.loopClosure positive ○ R := by
  rw [← SetRel.comp_assoc, loopClosure_comp_self]

theorem surviving_absorption {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner)
    (positive : Bool) :
    e.recurrence positive ○ e.surviving z positive ⊆ e.surviving z positive ∧
    e.surviving z positive ○ e.recurrence positive ⊆ e.surviving z positive := by
  obtain ⟨hl, hr⟩ := corner_through_absorption e z hz positive
  constructor
  · calc
      _ = e.loopClosure positive ○
          (e.through positive ○ e.loopClosure positive ○ z.through positive) ○
          e.loopClosure positive := by
            simp only [recurrence, surviving, SetRel.comp_assoc, loopClosure_comp]
      _ ⊆ e.surviving z positive := by unfold surviving; gcongr
  · calc
      _ = e.loopClosure positive ○
          (z.through positive ○ e.loopClosure positive ○ e.through positive) ○
          e.loopClosure positive := by
            simp only [recurrence, surviving, SetRel.comp_assoc, loopClosure_comp]
      _ ⊆ e.surviving z positive := by unfold surviving; gcongr

end Diagram

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.Diagram.surviving_absorption := @_root_.OAI.TwoWayComplementation.Diagram.surviving_absorption
