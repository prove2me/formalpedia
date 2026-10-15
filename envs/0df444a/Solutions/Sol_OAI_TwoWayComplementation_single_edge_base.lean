-- Prove2me | solution 1 for OAI.TwoWayComplementation.single_edge_base
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:08:01.68833+00:00
-- url     : https://prove2.me/submissions/faa61d78-bd11-41ee-8650-58b4d187b420

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Retained.lean:L129-L147
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.single_edge_base. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_corner_through_absorption
import Theorems.Thm_OAI_TwoWayComplementation_Diagram_rectangle_cover
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

theorem recurrence_trans {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {positive : Bool} {x y z : Fin m}
    (hxy : (x, y) ∈ e.recurrence positive) (hyz : (y, z) ∈ e.recurrence positive) :
    (x, z) ∈ e.recurrence positive := by
  rw [← recurrence_idempotent e he positive]
  exact ⟨y, hxy, hyz⟩

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

theorem rectangle_survives {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner)
    {positive : Bool} {p : Fin m} (hp : (p, p) ∈ e.surviving z positive) :
    e.rectangle positive p ⊆ z.through positive := by
  obtain ⟨hl, hr⟩ := corner_through_absorption e z hz positive
  rintro ⟨u, v⟩ ⟨⟨a, hua, hap⟩, ⟨b, hpb, hbv⟩⟩
  obtain ⟨d, ⟨c, hpc, hcd⟩, hdp⟩ := hp
  exact hr ⟨b, ⟨d, hl ⟨c, ⟨a, hua, hap.trans hpc⟩, hcd⟩, hdp.trans hpb⟩, hbv⟩

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Transport ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

/-- Losing no recurrent class forces componentwise inclusion. -/
theorem inclusion_of_missing_empty {m : ℕ} (e z : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) (hmissing : e.missing z = ∅) : (e, z) ∈ inclusion m := by
  have hthrough (positive : Bool) : e.through positive ⊆ z.through positive := by
    rintro ⟨u, v⟩ huv
    obtain ⟨p, hpp, hp⟩ := rectangle_cover e he huv
    let C : Bool × Set (Fin m) :=
      (positive, {y | (p, y) ∈ e.recurrence positive ∧ (y, p) ∈ e.recurrence positive})
    have hC : C ∈ e.classes := ⟨p, hpp, rfl⟩
    have hnC : C ∉ e.missing z := by rw [hmissing]; exact Set.notMem_empty _
    have hloop := (not_mem_missing_iff e z he hz hC ⟨hpp, hpp⟩).mp hnC
    exact rectangle_survives e z hz hloop hp
  exact ⟨hthrough true, hthrough false, corner_returns e z hz⟩

end Diagram

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Amplification ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- The image of a monoid lies in the diagram corner of its image identity. -/
theorem map_identity_corner {A : Type*} [Monoid A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (a : A) : ι a ∈ (ι 1).corner := by
  constructor
  · change ι 1 * ι a = ι a
    rw [← map_mul, one_mul]
  · change ι a * ι 1 = ι a
    rw [← map_mul, mul_one]

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Retained ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- The base case detects the off-diagonal pair using rectangle coverage and order reversal. -/
theorem single_edge_base {A H : Type*} [Monoid A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H)
    (hreverse : ∀ a b, (ι a, ι b) ∈ Diagram.inclusion m → (φ b).toRel ⊆ (φ a).toRel)
    (a : A) (x y : H) (hxy : x ≠ y)
    (himage : (φ a).toRel = SetRel.id ∪ {(x, y)}) (hh : Nat.card H ≤ 128) :
    lossBound (Nat.card H) ≤ ((ι 1).missing (ι a)).ncard := by
  have hsmall : lossBound (Nat.card H) = 1 := by
    have he : (Nat.card H - 2) / 127 = 0 := by omega
    simp [lossBound, he]
  rw [hsmall]
  by_contra h
  have hempty : (ι 1).missing (ι a) = ∅ := (Set.ncard_eq_zero).mp (by omega)
  have hinclusion := Diagram.inclusion_of_missing_empty (ι 1) (ι a)
    (map_identity_corner ι 1).1 (map_identity_corner ι a) hempty
  have hedge : (x, y) ∈ (φ a).toRel := by rw [himage]; exact Or.inr rfl
  have hid := hreverse 1 a hinclusion hedge
  rw [map_one, RelationMonoid.toRel_one] at hid
  exact hxy hid

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.single_edge_base := @_root_.OAI.TwoWayComplementation.single_edge_base
