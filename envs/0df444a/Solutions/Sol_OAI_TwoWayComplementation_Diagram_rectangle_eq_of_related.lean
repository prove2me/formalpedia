-- Prove2me | solution 1 for OAI.TwoWayComplementation.Diagram.rectangle_eq_of_related
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:31:55.562541+00:00
-- url     : https://prove2.me/submissions/ef56ed43-e3c9-410f-9b47-b060625adcf0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean:L290-L312
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.Diagram.rectangle_eq_of_related. The node keeps its source
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

theorem loopClosure_comp {m : ℕ} (e : Diagram m) (positive : Bool)
    (R : SetRel (Fin m) (Fin m)) :
    e.loopClosure positive ○ (e.loopClosure positive ○ R) = e.loopClosure positive ○ R := by
  rw [← SetRel.comp_assoc, loopClosure_comp_self]

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

theorem rectangle_eq_of_related {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {positive : Bool} {p q : Fin m} (hpq : (p, q) ∈ e.recurrence positive)
    (hqp : (q, p) ∈ e.recurrence positive) :
    e.rectangle positive p = e.rectangle positive q := by
  have hleft : (e.through positive ○ e.loopClosure positive) ○ e.recurrence positive =
      e.through positive ○ e.loopClosure positive := by
    calc
      _ = e.through positive ○ e.recurrence positive := by
        simp only [recurrence, SetRel.comp_assoc, loopClosure_comp]
      _ = _ := through_comp_recurrence e he positive
  have hright : e.recurrence positive ○ (e.loopClosure positive ○ e.through positive) =
      e.loopClosure positive ○ e.through positive := by
    calc
      _ = e.recurrence positive ○ e.through positive := by
        simp only [recurrence, SetRel.comp_assoc, loopClosure_comp]
      _ = _ := recurrence_comp_through e he positive
  ext ⟨u, v⟩
  exact ⟨fun ⟨hup, hpv⟩ =>
    ⟨hleft ▸ (show (u, q) ∈ _ ○ e.recurrence positive from ⟨p, hup, hpq⟩),
      hright ▸ (show (q, v) ∈ e.recurrence positive ○ _ from ⟨p, hqp, hpv⟩)⟩,
    fun ⟨huq, hqv⟩ =>
    ⟨hleft ▸ (show (u, p) ∈ _ ○ e.recurrence positive from ⟨q, huq, hqp⟩),
      hright ▸ (show (p, v) ∈ e.recurrence positive ○ _ from ⟨q, hpq, hqv⟩)⟩⟩

end Diagram

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.Diagram.rectangle_eq_of_related := @_root_.OAI.TwoWayComplementation.Diagram.rectangle_eq_of_related
