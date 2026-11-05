-- Prove2me | solution 1 for LL_Decomp1528b.harmonic_mul_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:07.772644+00:00
-- url     : https://prove2.me/submissions/23d338f2-b2c9-4e0c-bf4a-0aabc37fe7ac

import Mathlib

open Real Finset Filter Topology

theorem ChMeAux.harmonic_le_prod (N : ℕ) :
    (∑ m ∈ Icc 1 N, ((m : ℝ))⁻¹) ≤ ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p)⁻¹ := by
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ ↦ ‖((((p ^ n : ℕ)) : ℝ))⁻¹‖) := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have : (fun n : ℕ ↦ ‖((((p ^ n : ℕ)) : ℝ))⁻¹‖) = fun n : ℕ ↦ ((p : ℝ)⁻¹) ^ n := by
      ext n
      rw [Real.norm_of_nonneg (by positivity)]
      push_cast
      rw [inv_pow]
    rw [this]
    exact summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)
  have key := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    (f := fun n : ℕ ↦ ((n : ℝ))⁻¹) (by simp)
    (fun {m n} _ ↦ by simp [mul_comm]) hsum (N + 1)).2
  have hprod : ∏ p ∈ (N + 1).primesBelow, ∑' n : ℕ, ((((p ^ n : ℕ)) : ℝ))⁻¹
      = ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p)⁻¹ := by
    show _ = ∏ p ∈ (N + 1).primesBelow, (1 - (1 : ℝ) / p)⁻¹
    refine prod_congr rfl fun p hp ↦ ?_
    have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have : (fun n : ℕ ↦ ((((p ^ n : ℕ)) : ℝ))⁻¹) = fun n : ℕ ↦ ((p : ℝ)⁻¹) ^ n := by
      ext n
      push_cast
      rw [inv_pow]
    rw [this, tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)]
    simp
  rw [hprod] at key
  have hle := sum_le_hasSum ((Icc 1 N).subtype (· ∈ (N + 1).smoothNumbers))
    (fun i _ ↦ by positivity) key
  rw [Finset.sum_subtype_of_mem (fun m : ℕ ↦ ((m : ℝ))⁻¹)
    (fun m hm ↦ Nat.mem_smoothNumbers_of_lt (by simp at hm; omega) (by simp at hm; omega))] at hle
  exact hle

theorem solution (N : ℕ) :
    (harmonic N : ℝ) * ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) ≤ 1 := by
  have h := ChMeAux.harmonic_le_prod N
  have hpos : 0 < ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) := by
    refine prod_pos fun p hp ↦ ?_
    have hpp : p.Prime := (Nat.mem_primesLE.mp hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    rw [sub_pos, div_lt_one (by linarith)]
    exact hp1
  rw [prod_inv_distrib] at h
  have hH : (harmonic N : ℝ) = ∑ m ∈ Icc 1 N, ((m : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  rw [hH]
  calc (∑ m ∈ Icc 1 N, ((m : ℝ))⁻¹) * ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p)
      ≤ (∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p))⁻¹ * ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) :=
        mul_le_mul_of_nonneg_right h hpos.le
    _ = 1 := inv_mul_cancel₀ hpos.ne'
