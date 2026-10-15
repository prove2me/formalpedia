-- Prove2me | solution 1 for OAI.TwoWayComplementation.idempotent_relation_factor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:17:19.738439+00:00
-- url     : https://prove2.me/submissions/d71d66dc-a0fa-47bb-a60b-0a671864ebc6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Relations.lean:L317-L347
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.idempotent_relation_factor. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations

-- ---- from OAI.Combinatorics.TwoWayAutomata.Relations ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Every edge of a finite idempotent relation factors through a recurrent point. -/
theorem idempotent_relation_factor {α : Type*} [Finite α] (P : SetRel α α)
    (hP : P ○ P = P) {u v : α} (huv : (u, v) ∈ P) :
    ∃ p, (u, p) ∈ P ∧ (p, p) ∈ P ∧ (p, v) ∈ P := by
  classical
  have htrans {a b c : α} (hab : (a, b) ∈ P) (hbc : (b, c) ∈ P) :
      (a, c) ∈ P := hP ▸ (show (a, c) ∈ P ○ P from ⟨b, hab, hbc⟩)
  let T := {x : α // (x, v) ∈ P}
  have hnext : ∀ x : T, ∃ y : T, (x.val, y.val) ∈ P := by
    intro x
    have hx : (x.val, v) ∈ P ○ P := hP.symm ▸ x.property
    obtain ⟨y, hxy, hyv⟩ := hx
    exact ⟨⟨y, hyv⟩, hxy⟩
  choose f hf using hnext
  have hpath (x : T) (n : ℕ) : (x.val, (f^[n + 1] x).val) ∈ P := by
    induction n with
    | zero => exact hf x
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact htrans ih (hf _)
  let x : T := ⟨u, huv⟩
  obtain ⟨i, j, hij, heq⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (fun n : ℕ => Set.mem_univ (f^[n] x))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have hloop := hpath (f^[i] x) k
  rw [← Function.iterate_add_apply, Nat.add_comm] at hloop
  rw [← Nat.add_assoc, ← heq] at hloop
  refine ⟨(f^[i] x).val, ?_, hloop, (f^[i] x).property⟩
  cases i with
  | zero => exact hloop
  | succ i => exact hpath x i

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.idempotent_relation_factor := @_root_.OAI.TwoWayComplementation.idempotent_relation_factor
