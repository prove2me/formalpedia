-- Prove2me | solution 1 for OAI.TwoWayComplementation.Diagram.corner_through_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:26:49.125543+00:00
-- url     : https://prove2.me/submissions/d2891c06-fa5f-4cab-af30-eca296d1d111

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean:L94-L113
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.Diagram.corner_through_absorption. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_corner_forward_absorption

-- ---- from OAI.Combinatorics.TwoWayAutomata.Classes ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem corner_returns {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner) :
    e.left ⊆ z.left ∧ e.right ⊆ z.right := by
  constructor
  · rw [← congrArg left hz.1]
    exact Set.subset_union_left
  · rw [← congrArg right hz.2]
    exact Set.subset_union_left

theorem corner_through_absorption {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner)
    (positive : Bool) :
    e.through positive ○ e.loopClosure positive ○ z.through positive ⊆ z.through positive ∧
    z.through positive ○ e.loopClosure positive ○ e.through positive ⊆ z.through positive := by
  cases positive
  · obtain ⟨hL, hR⟩ := corner_returns e z hz
    have hl : e.loopClosure false ⊆ relStar (e.right ○ z.left) :=
      relStar_mono (SetRel.comp_subset_comp_right hL)
    have hr : e.loopClosure false ⊆ relStar (z.right ○ e.left) :=
      relStar_mono (SetRel.comp_subset_comp_left hR)
    constructor
    · calc
        _ ⊆ e.backward ○ relStar (z.right ○ e.left) ○ z.backward := by
          dsimp [through]; gcongr
        _ = z.backward := congrArg backward hz.2
    · calc
        _ ⊆ z.backward ○ relStar (e.right ○ z.left) ○ e.backward := by
          dsimp [through]; gcongr
        _ = z.backward := congrArg backward hz.1
  · exact corner_forward_absorption e z hz

end Diagram

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.Diagram.corner_through_absorption := @_root_.OAI.TwoWayComplementation.Diagram.corner_through_absorption
