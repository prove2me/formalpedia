-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.pow_mulSwap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:11:04.331635+00:00
-- url     : https://prove2.me/submissions/eb6f6a7d-28a7-4d3b-89f1-f8c83982f43a

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
variable [DecidableEq α]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution (π : Perm α) (x y : α) (m : ℕ)
    (hm : ∀ i, 0 < i → i < m → (π ^ i) x ≠ x ∧ (π ^ i) x ≠ y) :
    ∀ j, 0 < j → j ≤ m → ((π * swap x y) ^ j) y = (π ^ j) x := by
  intro j hj hjm
  induction j with
  | zero => exact absurd hj (lt_irrefl 0)
  | succ j ih =>
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · rw [pow_succ', Perm.mul_apply, ih hj0 (by omega), pow_succ' π, Perm.mul_apply π]
      obtain ⟨h1, h2⟩ := hm j hj0 (by omega)
      simp [swap_apply_of_ne_of_ne h1 h2]
end LeanPool.K5MinorFreeChoosability
