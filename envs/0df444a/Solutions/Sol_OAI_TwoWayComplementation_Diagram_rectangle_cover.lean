-- Prove2me | solution 1 for OAI.TwoWayComplementation.Diagram.rectangle_cover
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:33:09.192672+00:00
-- url     : https://prove2.me/submissions/337858ba-99cc-451b-8827-ecdd4a7e5c4c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean:L314-L328
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.Diagram.rectangle_cover. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_recurrence_idempotent
import Theorems.Thm_OAI_TwoWayComplementation_idempotent_relation_factor

-- ---- from OAI.Combinatorics.TwoWayAutomata.Classes ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

theorem through_loop_through {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) :
    e.through positive ○ e.loopClosure positive ○ e.through positive = e.through positive := by
  cases positive
  · exact congrArg backward he
  · exact congrArg forward he

theorem through_comp_recurrence {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) :
    e.through positive ○ e.recurrence positive = e.through positive ○ e.loopClosure positive := by
  simpa only [recurrence, SetRel.comp_assoc] using
    congrArg (· ○ e.loopClosure positive) (through_loop_through e he positive)

theorem recurrence_comp_through {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) :
    e.recurrence positive ○ e.through positive = e.loopClosure positive ○ e.through positive := by
  simpa only [recurrence, SetRel.comp_assoc] using
    congrArg (e.loopClosure positive ○ ·) (through_loop_through e he positive)

/-- The recurrent rectangles cover every through edge, including for an empty boundary. -/
theorem rectangle_cover {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {positive : Bool} {u v : Fin m} (huv : (u, v) ∈ e.through positive) :
    ∃ p, (p, p) ∈ e.recurrence positive ∧ (u, v) ∈ e.rectangle positive p := by
  have hFPF : e.through positive ○ e.recurrence positive ○ e.through positive =
      e.through positive := by
    rw [through_comp_recurrence e he positive, through_loop_through e he positive]
  obtain ⟨b, ⟨a, hua, hab⟩, hbv⟩ := hFPF.symm ▸ huv
  obtain ⟨p, hap, hpp, hpb⟩ :=
    idempotent_relation_factor _ (recurrence_idempotent e he positive) hab
  refine ⟨p, hpp, ?_, ?_⟩
  · rw [← through_comp_recurrence e he positive]
    exact ⟨a, hua, hap⟩
  · rw [← recurrence_comp_through e he positive]
    exact ⟨b, hpb, hbv⟩

end Diagram

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.Diagram.rectangle_cover := @_root_.OAI.TwoWayComplementation.Diagram.rectangle_cover
