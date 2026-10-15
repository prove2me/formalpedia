-- Prove2me | solution 1 for OAI.TwoWayComplementation.Diagram.corner_forward_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:24:28.798791+00:00
-- url     : https://prove2.me/submissions/5ef259b2-7454-40d7-8360-a22609afec51

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean:L77-L92
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.Diagram.corner_forward_absorption. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes

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

/-- Positive through-edge absorption in a corner. -/
theorem corner_forward_absorption {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner) :
    e.forward ○ e.loopClosure true ○ z.forward ⊆ z.forward ∧
    z.forward ○ e.loopClosure true ○ e.forward ⊆ z.forward := by
  obtain ⟨hL, hR⟩ := corner_returns e z hz
  have hl : e.loopClosure true ⊆ relStar (z.left ○ e.right) :=
    relStar_mono (SetRel.comp_subset_comp_left hL)
  have hr : e.loopClosure true ⊆ relStar (e.left ○ z.right) :=
    relStar_mono (SetRel.comp_subset_comp_right hR)
  constructor
  · calc
      _ ⊆ e.forward ○ relStar (z.left ○ e.right) ○ z.forward := by gcongr
      _ = z.forward := congrArg forward hz.1
  · calc
      _ ⊆ z.forward ○ relStar (e.left ○ z.right) ○ e.forward := by gcongr
      _ = z.forward := congrArg forward hz.2

end Diagram

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.Diagram.corner_forward_absorption := @_root_.OAI.TwoWayComplementation.Diagram.corner_forward_absorption
