-- Prove2me | solution 1 for KneserColouring.isAlt_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:43:21.236454+00:00
-- url     : https://prove2.me/submissions/bfe65347-d358-4ab1-885c-c3619c84f136

module
public import Mathlib
public import Definitions.Def_KneserLib_AltSets

set_option autoImplicit true
@[expose] public section
public section
open KneserColouring
open Finset
namespace KneserColouring
theorem _root_.solution {s : ℕ} {z : ℤ} {T : Finset ℤ} (hz : z ∉ T)
    (hlt : ∀ b ∈ T, |b| < |z|) :
    IsAlt s (insert z T) ↔ IsAlt s T ∧ (0 < z ↔ Even (T.card + s)) := by
  unfold IsAlt
  rw [forall_mem_insert]
  have hz' : (insert z T).filter (fun b => |b| < |z|) = T := by
    ext b
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨rfl | h, h'⟩
      · exact absurd h' (lt_irrefl _)
      · exact h
    · intro h; exact ⟨Or.inr h, hlt b h⟩
  have ha : ∀ a ∈ T, (insert z T).filter (fun b => |b| < |a|) = T.filter (fun b => |b| < |a|) := by
    intro a haT
    rw [filter_insert]
    split_ifs with h
    · exact absurd h (not_lt.2 (hlt a haT).le)
    · rfl
  rw [hz', and_comm]
  apply and_congr_left'
  constructor
  · intro h a haT; rw [← ha a haT]; exact h a haT
  · intro h a haT; rw [ha a haT]; exact h a haT
end KneserColouring
