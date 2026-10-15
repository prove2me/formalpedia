-- Prove2me | solution 1 for OAI.TwoWayComplementation.Diagram.nested_recurrence_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:35:28.780021+00:00
-- url     : https://prove2.me/submissions/1346dcec-4e75-49ff-8045-889363055a8c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Nesting.lean:L110-L133
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.Diagram.nested_recurrence_absorption. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_nested_forward_loop_absorption

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

theorem loopClosure_comp {m : ℕ} (e : Diagram m) (positive : Bool)
    (R : SetRel (Fin m) (Fin m)) :
    e.loopClosure positive ○ (e.loopClosure positive ○ R) = e.loopClosure positive ○ R := by
  rw [← SetRel.comp_assoc, loopClosure_comp_self]

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Nesting ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem loopClosure_subset_of_corner {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) : e.loopClosure positive ⊆ d.loopClosure positive := by
  obtain ⟨hL, hR⟩ := corner_returns e d hd
  cases positive
  · exact relStar_mono (SetRel.comp_subset_comp hR hL)
  · exact relStar_mono (SetRel.comp_subset_comp hL hR)

theorem nested_through_loop_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) :
    e.through positive ○ d.loopClosure positive ○ d.through positive ⊆
      d.loopClosure positive ○ d.through positive ∧
    d.through positive ○ d.loopClosure positive ○ e.through positive ⊆
      d.through positive ○ d.loopClosure positive := by
  cases positive
  · have hreflect : reflect d ∈ (reflect e).corner :=
      ⟨by rw [← reflect_comp, hd.2], by rw [← reflect_comp, hd.1]⟩
    exact nested_forward_loop_absorption (reflect e) (reflect d) hreflect
  · exact nested_forward_loop_absorption e d hd

theorem nested_through_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) :
    e.through positive ○ d.recurrence positive ⊆ d.recurrence positive ∧
    d.recurrence positive ○ e.through positive ⊆ d.recurrence positive := by
  obtain ⟨hl, hr⟩ := nested_through_loop_absorption e d hd positive
  constructor
  · simpa only [recurrence, SetRel.comp_assoc] using
      SetRel.comp_subset_comp_left (S := d.loopClosure positive) hl
  · simpa only [recurrence, SetRel.comp_assoc] using
      SetRel.comp_subset_comp_right (R := d.loopClosure positive) hr

/-- Mixed recurrent relations are absorbed under nesting. -/
theorem nested_recurrence_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) :
    e.recurrence positive ○ d.recurrence positive ⊆ d.recurrence positive ∧
    d.recurrence positive ○ e.recurrence positive ⊆ d.recurrence positive := by
  have hK := loopClosure_subset_of_corner e d hd positive
  obtain ⟨hl, hr⟩ := nested_through_absorption e d hd positive
  have hKP : d.loopClosure positive ○ d.recurrence positive = d.recurrence positive := by
    simp only [recurrence, SetRel.comp_assoc, loopClosure_comp]
  have hPK : d.recurrence positive ○ d.loopClosure positive = d.recurrence positive := by
    simp only [recurrence, SetRel.comp_assoc, loopClosure_comp_self]
  constructor
  · calc
      _ ⊆ d.loopClosure positive ○ e.through positive ○ d.loopClosure positive ○
          d.recurrence positive := by unfold recurrence; gcongr
      _ ⊆ d.recurrence positive := by
        rw [SetRel.comp_assoc, SetRel.comp_assoc, hKP]
        exact (SetRel.comp_subset_comp_right hl).trans hKP.le
  · calc
      _ ⊆ d.recurrence positive ○ d.loopClosure positive ○ e.through positive ○
          d.loopClosure positive := by unfold recurrence; simp only [SetRel.comp_assoc]; gcongr
      _ ⊆ d.recurrence positive := by
        rw [hPK]
        exact (SetRel.comp_subset_comp_left hr).trans hPK.le

end Diagram

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.Diagram.nested_recurrence_absorption := @_root_.OAI.TwoWayComplementation.Diagram.nested_recurrence_absorption
