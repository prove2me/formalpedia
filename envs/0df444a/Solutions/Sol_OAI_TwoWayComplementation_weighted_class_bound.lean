-- Prove2me | solution 1 for OAI.TwoWayComplementation.weighted_class_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:16:00.922401+00:00
-- url     : https://prove2.me/submissions/5c5796c5-69e0-4987-b17b-95e4da682dd8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Relations.lean:L257-L315
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.weighted_class_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations

-- ---- from OAI.Combinatorics.TwoWayAutomata.Relations ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- A bound for weighted classes with integer weights one and two. -/
theorem weighted_class_bound {α β : Type*} (X M : Finset α) (Y : Finset β)
    (R : β → α → Prop) (hM : M ⊆ X)
    (hunique : ∀ y ∈ Y, ∀ z ∈ Y, ∀ x ∈ X, R y x → R z x → y = z)
    (hcover : ∀ y ∈ Y,
      (∃ x ∈ X, x ∉ M ∧ R y x) ∨
        ∃ x ∈ X, ∃ z ∈ X, x ≠ z ∧ R y x ∧ R y z) :
    2 * Y.card + M.card ≤ 2 * X.card := by
  classical
  let F : β → Finset α := fun y => X.filter (R y)
  let w : α → ℕ := fun x => if x ∈ M then 1 else 2
  have hweight : ∀ y ∈ Y, 2 ≤ ∑ x ∈ F y, w x := by
    intro y hy
    rcases hcover y hy with ⟨x, hx, hxm, hxy⟩ | ⟨x, hx, z, hz, hxz, hxy, hzy⟩
    · have h := Finset.single_le_sum (f := w) (fun _ _ => Nat.zero_le _)
        (show x ∈ F y from Finset.mem_filter.mpr ⟨hx, hxy⟩)
      simpa [w, hxm] using h
    · have hsub : ({x, z} : Finset α) ⊆ F y := by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact Finset.mem_filter.mpr ⟨hx, hxy⟩
        · have haeq := Finset.mem_singleton.mp ha
          subst a
          exact Finset.mem_filter.mpr ⟨hz, hzy⟩
      have h := Finset.sum_le_sum_of_subset hsub (f := w)
      have hxw : 1 ≤ w x := by unfold w; split_ifs <;> omega
      have hzw : 1 ≤ w z := by unfold w; split_ifs <;> omega
      simp only [Finset.sum_pair hxz] at h
      omega
  have hdisjoint : Set.PairwiseDisjoint (↑Y) F := by
    intro y hy z hz hne
    apply Finset.disjoint_left.mpr
    intro x hxy hxz
    obtain ⟨hx, hxy⟩ := Finset.mem_filter.mp hxy
    obtain ⟨_, hxz⟩ := Finset.mem_filter.mp hxz
    exact hne (hunique y hy z hz x hx hxy hxz)
  have hsum : 2 * Y.card ≤ ∑ x ∈ X, w x := by
    calc
      _ = ∑ _ ∈ Y, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ y ∈ Y, ∑ x ∈ F y, w x := Finset.sum_le_sum hweight
      _ = ∑ x ∈ Y.biUnion F, w x := (Finset.sum_biUnion hdisjoint).symm
      _ ≤ ∑ x ∈ X, w x := Finset.sum_le_sum_of_subset (by
        intro x hx
        obtain ⟨y, _, hxy⟩ := Finset.mem_biUnion.mp hx
        exact (Finset.mem_filter.mp hxy).1)
  have hfilter : X.filter (· ∈ M) = M := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hx => ⟨hM hx, hx⟩⟩
  have hindicator : (∑ x ∈ X, if x ∈ M then 1 else 0) = M.card := by
    rw [← Finset.sum_filter, hfilter]
    simp
  have htotal : (∑ x ∈ X, w x) + M.card = 2 * X.card := by
    rw [← hindicator, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _ ∈ X, 2 := Finset.sum_congr rfl (fun x _ => by
        unfold w; split_ifs <;> omega)
      _ = _ := by simp [Nat.mul_comm]
  omega

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.weighted_class_bound := @_root_.OAI.TwoWayComplementation.weighted_class_bound
