-- Prove2me | solution 1 for OAI.TwoWayComplementation.Diagram.missing_comp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:30:39.793646+00:00
-- url     : https://prove2.me/submissions/2b47fb89-63a0-4650-81f5-60a28e424d15

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean:L233-L249
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.Diagram.missing_comp. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_recurrence_idempotent
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_surviving_absorption

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

theorem recurrence_trans {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {positive : Bool} {x y z : Fin m}
    (hxy : (x, y) ∈ e.recurrence positive) (hyz : (y, z) ∈ e.recurrence positive) :
    (x, z) ∈ e.recurrence positive := by
  rw [← recurrence_idempotent e he positive]
  exact ⟨y, hxy, hyz⟩

theorem class_nonempty {m : ℕ} {e : Diagram m} {c : Bool × Set (Fin m)}
    (hc : c ∈ e.classes) : c.2.Nonempty := by
  obtain ⟨x, hx, hxc⟩ := hc
  exact ⟨x, hxc ▸ ⟨hx, hx⟩⟩

theorem class_related {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {c : Bool × Set (Fin m)} (hc : c ∈ e.classes) {x y : Fin m}
    (hx : x ∈ c.2) (hy : y ∈ c.2) :
    (x, y) ∈ e.recurrence c.1 ∧ (y, x) ∈ e.recurrence c.1 := by
  obtain ⟨p, _, hC⟩ := hc
  rw [hC] at hx hy
  exact ⟨recurrence_trans e he hx.2 hy.1, recurrence_trans e he hy.2 hx.1⟩

theorem surviving_loop_iff {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) {c : Bool × Set (Fin m)} (hc : c ∈ e.classes)
    {x y : Fin m} (hx : x ∈ c.2) (hy : y ∈ c.2) :
    (x, x) ∈ e.surviving z c.1 ↔ (y, y) ∈ e.surviving z c.1 := by
  obtain ⟨hxy, hyx⟩ := class_related e he hc hx hy
  obtain ⟨hl, hr⟩ := surviving_absorption e z hz c.1
  exact ⟨fun h => hr ⟨x, hl ⟨x, hyx, h⟩, hxy⟩,
    fun h => hr ⟨y, hl ⟨y, hxy, h⟩, hyx⟩⟩

theorem not_mem_missing_iff {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) {c : Bool × Set (Fin m)} (hc : c ∈ e.classes)
    {x : Fin m} (hx : x ∈ c.2) :
    c ∉ e.missing z ↔ (x, x) ∈ e.surviving z c.1 := by
  classical
  change ¬ (c ∈ e.classes ∧ _) ↔ _
  simp only [hc, true_and, not_forall, not_not]
  exact ⟨fun ⟨y, hy, hyy⟩ => (surviving_loop_iff e z he hz hc hy hx).mp hyy,
    fun hxx => ⟨x, hx, hxx⟩⟩

theorem surviving_comp {m : ℕ} (e z w : Diagram m)
    (hz : z ∈ e.corner) (hw : w ∈ e.corner) (positive : Bool) :
    (if positive then e.surviving z positive ○ e.surviving w positive
      else e.surviving w positive ○ e.surviving z positive) ⊆
      e.surviving (comp z w) positive := by
  obtain ⟨hzL, hzR⟩ := corner_returns e z hz
  obtain ⟨hwL, hwR⟩ := corner_returns e w hw
  have hplus : e.loopClosure true ⊆ relStar (w.left ○ z.right) :=
    relStar_mono (SetRel.comp_subset_comp hwL hzR)
  have hminus : e.loopClosure false ⊆ relStar (z.right ○ w.left) :=
    relStar_mono (SetRel.comp_subset_comp hzR hwL)
  cases positive <;> simp only [Bool.false_eq_true, ite_false, ite_true]
  · calc
      _ = e.loopClosure false ○
          (w.backward ○ e.loopClosure false ○ z.backward) ○ e.loopClosure false := by
            simp only [surviving, through, Bool.false_eq_true, ite_false,
              SetRel.comp_assoc, loopClosure_comp]
      _ ⊆ e.surviving (comp z w) false := by
        dsimp [surviving, through, comp]; gcongr
  · calc
      _ = e.loopClosure true ○
          (z.forward ○ e.loopClosure true ○ w.forward) ○ e.loopClosure true := by
            simp only [surviving, through, ite_true,
              SetRel.comp_assoc, loopClosure_comp]
      _ ⊆ e.surviving (comp z w) true := by
        dsimp [surviving, through, comp]; gcongr

/-- A class can disappear from a product only if it disappears from a factor. -/
theorem missing_comp {m : ℕ} (e z w : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) (hw : w ∈ e.corner) :
    e.missing (comp z w) ⊆ e.missing z ∪ e.missing w := by
  classical
  intro c hc
  by_contra h
  obtain ⟨hnz, hnw⟩ := not_or.mp h
  obtain ⟨x, hx⟩ := class_nonempty hc.1
  have hzz := (not_mem_missing_iff e z he hz hc.1 hx).mp hnz
  have hww := (not_mem_missing_iff e w he hw hc.1 hx).mp hnw
  apply hc.2 x hx
  apply surviving_comp e z w hz hw c.1
  cases hs : c.1 <;> simp only [hs] at hzz hww ⊢ <;>
    simp only [Bool.false_eq_true, ite_false, ite_true]
  · exact ⟨x, hww, hzz⟩
  · exact ⟨x, hzz, hww⟩

end Diagram

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.Diagram.missing_comp := @_root_.OAI.TwoWayComplementation.Diagram.missing_comp
