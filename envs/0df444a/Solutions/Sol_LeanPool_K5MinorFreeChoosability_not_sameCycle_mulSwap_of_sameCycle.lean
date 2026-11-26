-- Prove2me | solution 1 for LeanPool.K5MinorFreeChoosability.not_sameCycle_mulSwap_of_sameCycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:13:20.805871+00:00
-- url     : https://prove2.me/submissions/a203ac34-81eb-43fa-aaf1-d43605df3f5b

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
omit [DecidableEq α] in
private theorem pow_apply_mod {π : Perm α} {y : α} {m : ℕ} (hm : (π ^ m) y = y) (k : ℕ) :
    (π ^ k) y = (π ^ (k % m)) y := by
  conv_lhs => rw [← Nat.mod_add_div k m, pow_add, Perm.mul_apply, pow_mul]
  congr 1
  induction k / m with
  | zero => simp
  | succ n ih => rw [pow_succ, Perm.mul_apply, hm, ih]
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
theorem _root_.solution [Finite α] {π : Perm α} {x y : α} (hne : x ≠ y)
    (h : SameCycle π x y) : ¬ SameCycle (π * swap x y) x y := by
  obtain ⟨m, hm0, hmy, hmin⟩ := exists_min_pow π x y h
  have hnx : ∀ i, 0 < i → i < m → (π ^ i) x ≠ x := by
    intro i hi hlt he
    apply hmin (m - i) (by omega) (by omega)
    have : (π ^ m) x = (π ^ (m - i)) ((π ^ i) x) := by
      rw [← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hlt.le]
    rw [he] at this
    rw [← this, hmy]
  have key := pow_mulSwap_apply π x y m (fun i hi hlt => ⟨hnx i hi hlt, hmin i hi hlt⟩)
  have hper : ((π * swap x y) ^ m) y = y := by rw [key m hm0 le_rfl, hmy]
  intro hs
  obtain ⟨k, hk⟩ := hs.symm.exists_nat_pow_eq
  rw [pow_apply_mod hper] at hk
  have hlt : k % m < m := Nat.mod_lt _ hm0
  rcases Nat.eq_zero_or_pos (k % m) with h0 | h0
  · rw [h0] at hk
    exact hne (by simpa using hk.symm)
  · rw [key _ h0 hlt.le] at hk
    exact hnx _ h0 hlt hk
end LeanPool.K5MinorFreeChoosability
