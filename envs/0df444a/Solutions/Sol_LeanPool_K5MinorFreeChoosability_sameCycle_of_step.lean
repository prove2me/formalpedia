-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.sameCycle_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:11:03.796943+00:00
-- url     : https://prove2.me/submissions/6b87c858-8b44-4e5e-ab5a-a14d915e711e

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution (s : Setoid α) {π : Perm α} (h : ∀ z, s z (π z)) {a b : α}
    (hab : SameCycle π a b) : s a b := by
  obtain ⟨i, rfl⟩ := hab
  induction i using Int.induction_on with
  | zero => exact s.refl a
  | succ i ih =>
    rw [add_comm, zpow_add, zpow_one, Perm.mul_apply]
    exact s.trans ih (h _)
  | pred i ih =>
    have h2 := h ((π ^ (-(i : ℤ) - 1)) a)
    rw [← Perm.mul_apply, ← zpow_one_add] at h2
    rw [show (1 : ℤ) + (-(i : ℤ) - 1) = -i by ring] at h2
    exact s.trans ih (s.symm h2)
end LeanPool.K5MinorFreeChoosability
