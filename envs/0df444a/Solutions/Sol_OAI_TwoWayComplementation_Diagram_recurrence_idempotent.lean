-- Prove2me | solution 1 for OAI.TwoWayComplementation.Diagram.recurrence_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:22:51.222351+00:00
-- url     : https://prove2.me/submissions/7335c6f4-92f4-4e99-af70-4270e7677a15

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean:L53-L67
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.Diagram.recurrence_idempotent. The node keeps its source
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

theorem through_loop_through {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) :
    e.through positive ○ e.loopClosure positive ○ e.through positive = e.through positive := by
  cases positive
  · exact congrArg backward he
  · exact congrArg forward he

/-- Idempotence of the recurrence relation. -/
theorem recurrence_idempotent {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) :
    e.recurrence positive ○ e.recurrence positive = e.recurrence positive := by
  have hK : e.loopClosure positive ○ e.loopClosure positive = e.loopClosure positive := by
    cases positive <;> simp [loopClosure]
  unfold recurrence
  calc
    (e.loopClosure positive ○ e.through positive ○ e.loopClosure positive) ○
        (e.loopClosure positive ○ e.through positive ○ e.loopClosure positive) =
        e.loopClosure positive ○
          (e.through positive ○ (e.loopClosure positive ○ e.loopClosure positive) ○
            e.through positive) ○ e.loopClosure positive := by simp only [SetRel.comp_assoc]
    _ = e.loopClosure positive ○ e.through positive ○ e.loopClosure positive := by
      rw [hK, through_loop_through e he positive]

end Diagram

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.Diagram.recurrence_idempotent := @_root_.OAI.TwoWayComplementation.Diagram.recurrence_idempotent
