-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.sameCycle_mulSwap_of_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:16.555794+00:00
-- url     : https://prove2.me/submissions/e86c2ce9-a6c2-4502-b0bf-978388d26d65

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Orbits
public import Theorems.Thm_LeanPool_K5MinorFreeChoosability_pow_mulSwap_apply
section
@[expose] public section
namespace LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
variable [DecidableEq α]
omit [DecidableEq α] in
private theorem exists_min_pow (π : Perm α) [Finite α] (x t : α) (ht : SameCycle π x t) :
    ∃ m, 0 < m ∧ (π ^ m) x = t ∧ ∀ i, 0 < i → i < m → (π ^ i) x ≠ t := by
  classical
  have hex : ∃ m, 0 < m ∧ (π ^ m) x = t := by
    obtain ⟨i, hi⟩ := ht.exists_nat_pow_eq
    refine ⟨i + orderOf π, ?_, ?_⟩
    · have := orderOf_pos π
      omega
    · rw [add_comm, pow_add, pow_orderOf_eq_one, one_mul, hi]
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro i hi hlt heq
  exact Nat.find_min hex hlt ⟨hi, heq⟩
end LeanPool.K5MinorFreeChoosability
end
end

set_option autoImplicit true
@[expose] public section
public section
open LeanPool LeanPool.K5MinorFreeChoosability
open Equiv Equiv.Perm
variable {α : Type*}
variable [DecidableEq α]
namespace LeanPool.K5MinorFreeChoosability
theorem _root_.solution [Finite α] {π : Perm α} {x y : α}
    (h : ¬ SameCycle π x y) : SameCycle (π * swap x y) x y := by
  obtain ⟨m, hm0, hmx, hmin⟩ := exists_min_pow π x x (SameCycle.refl _ _)
  have key := pow_mulSwap_apply π x y m (fun i hi hlt => ⟨hmin i hi hlt, fun he =>
    h (he ▸ ⟨(i : ℤ), by simp⟩)⟩) m hm0 le_rfl
  rw [hmx] at key
  have h2 : SameCycle (π * swap x y) y x := ⟨(m : ℤ), by simpa using key⟩
  exact h2.symm
end LeanPool.K5MinorFreeChoosability
