-- Prove2me | solution 1 for GwExact.find_ins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:22:29.731199+00:00
-- url     : https://prove2.me/submissions/7d98f5cd-81d2-45ab-8133-d1bd714b3b3b

module
public import Definitions.Def_GwExact_Check
public import Theorems.Thm_GwExact_find_node
public import Theorems.Thm_GwExact_find_parts
public import Theorems.Thm_GwExact_ins_succ

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution : ∀ (f : Nat) (t : Trie) (k : Nat) (c : Cls) (k' : Nat) (c' : Cls),
    (Trie.ins f t k c).find k' = some c' → c' = c ∨ t.find k' = some c' := by
  intro f
  induction f with
  | zero => intro t k c k' c' h; exact Or.inr h
  | succ f ih =>
    intro t k c k' c' h
    rw [find_parts t k']
    rw [ins_succ] at h
    split at h
    · rw [find_node] at h
      split at h
      · exact Or.inl (Option.some.inj h).symm
      · right; simp_all
    · split at h
      · rw [find_node] at h
        split at h
        · right; simp_all
        · split at h
          · rcases ih _ _ _ _ _ h with h5 | h5
            · exact Or.inl h5
            · right; simp_all
          · right; simp_all
      · rw [find_node] at h
        split at h
        · right; simp_all
        · split at h
          · right; simp_all
          · rcases ih _ _ _ _ _ h with h5 | h5
            · exact Or.inl h5
            · right; simp_all
end GwExact
