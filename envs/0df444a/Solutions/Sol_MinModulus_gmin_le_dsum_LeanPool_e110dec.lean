-- Prove2me | solution 1 for MinModulus.gmin_le_dsum_LeanPool_e110dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:15.103916+00:00
-- url     : https://prove2.me/submissions/00f9afd2-5926-4f0c-97dd-b5ee7afdab25

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
public import Theorems.Thm_MinModulus_gmin_add_le_LeanPool_e110dec
public import Theorems.Thm_MinModulus_unshift_val_LeanPool_e110dec
public import Theorems.Thm_MinModulus_unshift_dsum_LeanPool_e110dec

set_option autoImplicit true
@[expose] public section
public section
open MinModulus
open Finset
namespace MinModulus
theorem _root_.solution : ∀ w (k : ℕ → ℕ), gmin w (val (w + 1) k) ≤ dsum (w + 1) k := by
  intro w
  induction w with
  | zero =>
    intro k
    simp [gmin, val, dsum]
  | succ w ih =>
    intro k
    have hv := unshift_val_LeanPool_e110dec (w + 1) k
    have hd := unshift_dsum_LeanPool_e110dec (w + 1) k
    have hih := ih (fun i => k (i + 1))
    obtain ⟨t, ht⟩ : ∃ t, k 0 = (val (w + 1 + 1) k) % 2 + 2 * t :=
      ⟨k 0 / 2, by omega⟩
    have hsplit : val (w + 1) (fun i => k (i + 1)) + t = (val (w + 1 + 1) k) / 2 := by
      omega
    have hadd := gmin_add_le_LeanPool_e110dec w (val (w + 1) (fun i => k (i + 1))) t
    rw [hsplit] at hadd
    simp only [gmin]
    omega
end MinModulus
