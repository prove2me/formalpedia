-- Prove2me | solution 1 for OAI.TwoWayComplementation.Diagram.nested_class_containment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:38:41.913982+00:00
-- url     : https://prove2.me/submissions/4cb1b597-b8a4-4d7d-a201-57d69c9c2b08

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Nesting.lean:L199-L232
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.Diagram.nested_class_containment. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_nested_recurrence_absorption
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_nested_recurrent_witness
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_recurrence_idempotent
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_surviving_absorption

-- ---- from OAI.Combinatorics.TwoWayAutomata.Classes ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

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

theorem class_eq_of_mem {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {c : Bool × Set (Fin m)} (hc : c ∈ e.classes) {x : Fin m} (hx : x ∈ c.2) :
    c.2 = {y | (x, y) ∈ e.recurrence c.1 ∧ (y, x) ∈ e.recurrence c.1} := by
  ext y
  constructor
  · exact class_related e he hc hx
  · intro hy
    obtain ⟨p, _, hC⟩ := hc
    rw [hC] at hx ⊢
    exact ⟨recurrence_trans e he hx.1 hy.1, recurrence_trans e he hy.2 hx.2⟩

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

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Nesting ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

/-- A new class contains a surviving old class or two distinct old classes. -/
theorem nested_class_containment {m : ℕ} (e d : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hde : d ∈ e.corner)
    {c : Bool × Set (Fin m)} (hc : c ∈ d.classes) :
    (∃ C ∈ e.classes, C.1 = c.1 ∧ C.2 ⊆ c.2 ∧ C ∉ e.missing d) ∨
      ∃ C ∈ e.classes, ∃ D ∈ e.classes,
        C ≠ D ∧ C.1 = c.1 ∧ D.1 = c.1 ∧ C.2 ⊆ c.2 ∧ D.2 ⊆ c.2 := by
  classical
  obtain ⟨x, hx⟩ := class_nonempty hc
  have hxx := (class_related d hd hc hx hx).1
  obtain ⟨p, q, hpp, hqq, hxp, hpx, hxq, hqx, hpq⟩ :=
    nested_recurrent_witness e d he hde hxx
  let C : Bool × Set (Fin m) :=
    (c.1, {y | (p, y) ∈ e.recurrence c.1 ∧ (y, p) ∈ e.recurrence c.1})
  let D : Bool × Set (Fin m) :=
    (c.1, {y | (q, y) ∈ e.recurrence c.1 ∧ (y, q) ∈ e.recurrence c.1})
  have hC : C ∈ e.classes := ⟨p, hpp, rfl⟩
  have hD : D ∈ e.classes := ⟨q, hqq, rfl⟩
  obtain ⟨hPePd, hPdPe⟩ := nested_recurrence_absorption e d hde c.1
  have hCsub : C.2 ⊆ c.2 := by
    intro r hr
    rw [class_eq_of_mem d hd hc hx]
    exact ⟨hPdPe ⟨p, hxp, hr.1⟩, hPePd ⟨p, hr.2, hpx⟩⟩
  have hDsub : D.2 ⊆ c.2 := by
    intro r hr
    rw [class_eq_of_mem d hd hc hx]
    exact ⟨hPdPe ⟨q, hxq, hr.1⟩, hPePd ⟨q, hr.2, hqx⟩⟩
  by_cases hCD : C = D
  · left
    refine ⟨C, hC, rfl, hCsub, ?_⟩
    have hqC : q ∈ C.2 := by rw [hCD]; exact ⟨hqq, hqq⟩
    apply (not_mem_missing_iff e d he hde hC ⟨hpp, hpp⟩).mpr
    exact (surviving_absorption e d hde c.1).2 ⟨q, hpq, hqC.2⟩
  · exact Or.inr ⟨C, hC, D, hD, hCD, rfl, rfl, hCsub, hDsub⟩

end Diagram

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.Diagram.nested_class_containment := @_root_.OAI.TwoWayComplementation.Diagram.nested_class_containment
