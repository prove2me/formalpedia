-- Prove2me | solution 1 for MinModulus.exists_rep_le_LeanPool_e110dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:40:39.773521+00:00
-- url     : https://prove2.me/submissions/97c2910e-8cb9-42ff-9d2d-2011d475f97a

module
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_MinModulusUniqueMultisetSum_UniqueSums

set_option autoImplicit true
@[expose] public section
public section
open MinModulus
open Finset
namespace MinModulus
theorem _root_.solution : ∀ w x : ℕ, x < 2 ^ w →
    ∃ k, Supp w k ∧ val w k = x ∧ dsum w k ≤ w := by
  intro w
  induction w with
  | zero =>
    intro x hx
    rw [pow_zero] at hx
    obtain rfl : x = 0 := by omega
    refine ⟨fun _ => 0, fun _ _ => rfl, ?_, ?_⟩ <;> simp [val, dsum]
  | succ w ih =>
    intro x hx
    have h2 : 2 ^ (w + 1) = 2 * 2 ^ w := by rw [pow_succ]; ring
    rcases Nat.lt_or_ge x (2 ^ w) with h | h
    · obtain ⟨k, hs, hv, hd⟩ := ih x h
      exact ⟨k, supp_mono (by omega) hs,
        by rw [val_pad (by omega) hs, hv],
        by rw [dsum_pad (by omega) hs]; omega⟩
    · obtain ⟨k, hs, hv, hd⟩ := ih (x - 2 ^ w) (by omega)
      obtain ⟨us, uv, ud⟩ := update_top_LeanPool_e110dec w 1 k hs
      exact ⟨Function.update k w 1, us, by rw [uv, hv]; omega, by rw [ud]; omega⟩
end MinModulus
