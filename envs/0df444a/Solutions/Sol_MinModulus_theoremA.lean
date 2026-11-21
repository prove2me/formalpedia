-- Prove2me | solution 1 for MinModulus.theoremA
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:34.36941+00:00
-- url     : https://prove2.me/submissions/ea3d3693-c5cb-4e04-a24a-d53d6bcafeda

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
public import Theorems.Thm_MinModulus_slack_LeanPool_e110dec
public import Theorems.Thm_MinModulus_dsum_le_val
public import Theorems.Thm_MinModulus_gmin_le_dsum_LeanPool_e110dec
public import Theorems.Thm_MinModulus_ones_unique_LeanPool_e110dec

set_option autoImplicit true
@[expose] public section
public section
open MinModulus
open Finset
namespace MinModulus
theorem _root_.solution {n : ℕ} (hn : 2 ≤ n) :
    Valid n (2 ^ n - 2 ^ Nat.log 2 n) := by
  have hmn : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hnm : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  set m := Nat.log 2 n with hm
  set N := 2 ^ n - 2 ^ m with hN
  have h1m : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have hnlt : n < 2 ^ n := Nat.lt_two_pow_self
  have hmltn : m < n := by
    have h : m < 2 ^ m := Nat.lt_two_pow_self
    omega
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hmle : 2 ^ m ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2p : 2 ≤ 2 ^ (n - 1) := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 1 ≤ n - 1)
    simpa using h
  intro k hd hcong
  -- pass from the `a`-congruence to `M = val n k ≡ 2^n − 1 [MOD N]`
  have e1 : (∑ i ∈ range n, k i * a i) + n = val n k := by
    have h0 := sum_a_add_dsum n k
    rw [hd] at h0
    exact h0
  have hd1 : dsum n (fun _ => 1) = n := by
    unfold dsum
    rw [Finset.sum_const, smul_eq_mul, mul_one, card_range]
  have hv1 : val n (fun _ => 1) = 2 ^ n - 1 := by
    unfold val
    calc (∑ i ∈ range n, 1 * 2 ^ i) = ∑ i ∈ range n, 2 ^ i :=
          Finset.sum_congr rfl fun i _ => one_mul _
      _ = 2 ^ n - 1 := sum_two_pow n
  have e2 : (∑ i ∈ range n, a i) + n = 2 ^ n - 1 := by
    have h0 := sum_a_add_dsum n (fun _ => 1)
    simp only [one_mul] at h0
    rw [hd1, hv1] at h0
    exact h0
  have hMcong : val n k ≡ 2 ^ n - 1 [MOD N] := by
    have h := Nat.ModEq.add_right n hcong
    rwa [e1, e2] at h
  have hlow : n ≤ val n k := by
    have h := dsum_le_val n k
    omega
  rcases lt_trichotomy (val n k) (2 ^ n - 1) with hlt | heq | hgt
  · -- M < 2^n − 1: a positive multiple downward lands below 2^m ≤ n ≤ M
    exfalso
    have hdvd : N ∣ 2 ^ n - 1 - val n k :=
      (Nat.modEq_iff_dvd' (by omega)).mp hMcong
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  · exact ones_unique_LeanPool_e110dec n k heq hd
  · -- M = 2^n − 1 + jN with 1 ≤ j ≤ n − 2: greedy digit sum exceeds n
    exfalso
    have hdvd : N ∣ val n k - (2 ^ n - 1) :=
      (Nat.modEq_iff_dvd' (by omega)).mp hMcong.symm
    obtain ⟨j, hj⟩ := hdvd
    have hcomm : N * j = j * N := Nat.mul_comm N j
    have hjeq : val n k = 2 ^ n - 1 + j * N := by omega
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | h
      · rw [Nat.zero_mul] at hjeq
        omega
      · exact h
    have hgd : gmin (n - 1) (val n k) ≤ n := by
      have h := gmin_le_dsum_LeanPool_e110dec (n - 1) k
      have h' : n - 1 + 1 = n := by omega
      rw [h'] at h
      omega
    -- `slack_LeanPool_e110dec` at gap `2^m`: `gmin (n−1) M_j ≥ n + j > n`, contradiction
    have hw : n - 1 + 1 = n := by omega
    have hNt : N + 2 ^ m = 2 ^ (n - 1 + 1) := by rw [hw]; omega
    have hs := slack_LeanPool_e110dec (by omega : m ≤ n - 1) hNt j
    have harg : 2 ^ (n - 1 + 1) - 1 + j * N = val n k := by
      rw [hw]
      omega
    rw [harg, hw] at hs
    omega
end MinModulus
