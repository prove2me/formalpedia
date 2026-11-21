-- Prove2me | solution 1 for MinModulus.ones_unique_LeanPool_e110dec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:41:49.2472+00:00
-- url     : https://prove2.me/submissions/e514ec54-58fa-44d5-80b2-f64c1eb29ab4

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
public import Theorems.Thm_MinModulus_gmin_ones_LeanPool_e110dec
public import Theorems.Thm_MinModulus_unshift_val_LeanPool_e110dec
public import Theorems.Thm_MinModulus_unshift_dsum_LeanPool_e110dec
public import Theorems.Thm_MinModulus_gmin_le_dsum_LeanPool_e110dec

set_option autoImplicit true
@[expose] public section
public section
open MinModulus
open Finset
namespace MinModulus
theorem _root_.solution : ∀ n (k : ℕ → ℕ), val n k = 2 ^ n - 1 → dsum n k = n →
    ∀ i < n, k i = 1 := by
  intro n
  induction n with
  | zero => intro k _ _ i hi; omega
  | succ n ih =>
    intro k hv hd
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · intro i hi
      have h0 : i = 0 := by omega
      subst h0
      simp [val] at hv
      omega
    · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
      have hv' := unshift_val_LeanPool_e110dec (p + 1) k
      have hd' := unshift_dsum_LeanPool_e110dec (p + 1) k
      have h2 : 2 ^ (p + 1 + 1) = 2 * 2 ^ (p + 1) := by rw [pow_succ]; ring
      have h1 : 1 ≤ 2 ^ (p + 1) := Nat.one_le_pow _ _ (by norm_num)
      obtain ⟨t, ht⟩ : ∃ t, k 0 = 1 + 2 * t := ⟨k 0 / 2, by omega⟩
      have hveq : val (p + 1) (fun i => k (i + 1)) + t = 2 ^ (p + 1) - 1 := by
        omega
      have hlb := gmin_le_dsum_LeanPool_e110dec p (fun i => k (i + 1))
      have hg := gmin_ones_LeanPool_e110dec p
      have hadd := gmin_add_le_LeanPool_e110dec p (val (p + 1) (fun i => k (i + 1))) t
      rw [hveq, hg] at hadd
      have ht0 : t = 0 := by omega
      have hk0 : k 0 = 1 := by omega
      have hval1 : val (p + 1) (fun i => k (i + 1)) = 2 ^ (p + 1) - 1 := by omega
      have hds1 : dsum (p + 1) (fun i => k (i + 1)) = p + 1 := by omega
      have hres := ih (fun i => k (i + 1)) hval1 hds1
      intro i hi
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · exact hk0
      · have hi1 : i - 1 + 1 = i := by omega
        have h := hres (i - 1) (by omega)
        simpa [hi1] using h
end MinModulus
