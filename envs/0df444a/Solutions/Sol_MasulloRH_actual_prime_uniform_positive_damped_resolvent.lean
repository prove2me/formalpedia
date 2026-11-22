-- Prove2me | solution 1 for MasulloRH.actual_prime_uniform_positive_damped_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T12:51:56.468414+00:00
-- url     : https://prove2.me/submissions/198f303b-7072-4e58-9b7f-7004857a7d97

import Mathlib
import Theorems.Thm_MasulloRH_prime_resolvent_zero_profile_and_uniform_prime_power_transfer
import Theorems.Thm_MasulloRH_uniform_damped_resolvent_mesh_discrepancy

open Finset Real

theorem solution (N : ℕ) (c Y : ℝ) (hc : 0 < c) (hY : Y = Real.log ((N : ℝ)+2)) :
    |(∑ i ∈ (range (N+1)).filter (fun i => (i+2).Prime),
      Real.exp (-c * (Real.log ((i:ℝ)+2) / Y)) *
        ((Real.log ((i:ℝ)+2))^2 / ((i:ℝ)+2) / Y^2)) -
      (1-(1+c)*Real.exp (-c))/c^2| ≤
      ((2*(Real.log 4+4)+1537 / Real.log 2)*Y + 1537)/Y^2 + Real.log 2 / Y := by
  classical
  let C := 2*(Real.log 4+4)+1537 / Real.log 2
  have hy : 0 < Y := by rw [hY]; apply Real.log_pos; linarith [Nat.cast_nonneg (α:=ℝ) N]
  have hC : 0 ≤ C := by
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [C]; positivity
  let a (k : ℕ) : ℝ := if k.Prime then (Real.log k)^2 / k else 0
  let u (i : ℕ) : ℝ := Real.log ((i:ℝ)+1) / Y
  let A (i : ℕ) : ℝ := (∑ k ∈ range (i+2), a k) / Y^2
  have hA0 : A 0 = 0 := by norm_num [A, a, sum_range_succ]
  have hu0 : u 0 = 0 := by simp [u]
  have hu1 : u (N+1) = 1 := by
    dsimp [u]; push_cast; rw [show (N:ℝ)+1+1=(N:ℝ)+2 by ring, ← hY, div_self hy.ne']
  have hmono : Monotone u := by
    intro i j hij
    apply div_le_div_of_nonneg_right _ hy.le
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.succ_le_succ hij
  have hmesh (i : ℕ) : u (i+1)-u i ≤ Real.log 2/Y := by
    dsimp [u]; push_cast; rw [← sub_div]
    apply div_le_div_of_nonneg_right _ hy.le
    have hi : 0 < (i:ℝ)+1 := by positivity
    have hh : Real.log ((i:ℝ)+1+1) ≤ Real.log (2*((i:ℝ)+1)) :=
      Real.log_le_log (by positivity) (by linarith [Nat.cast_nonneg (α:=ℝ) i])
    rw [Real.log_mul (by norm_num) hi.ne'] at hh
    linarith
  have hD (i : ℕ) (hi : i ≤ N+1) :
      |A i - (u i)^2/2| ≤ (C*Y+1537)/Y^2 := by
    by_cases hz : i = 0
    · subst i; rw [hA0,hu0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, zero_div, sub_zero, abs_zero]; positivity
    have hx : (2:ℝ) ≤ ((i+1:ℕ):ℝ) := by exact_mod_cast (show 2 ≤ i+1 by omega)
    have hp := (MasulloRH.prime_resolvent_zero_profile_and_uniform_prime_power_transfer
      ((i+1:ℕ):ℝ) hx).1
    rw [Nat.floor_natCast] at hp
    have heq : (∑ k ∈ range (i+2), a k) =
        ∑ k ∈ (Ioc 0 (i+1)).filter Nat.Prime, Real.log k ^ 2 / k := by
      rw [show i+2=(i+1)+1 by omega, Nat.range_succ_eq_Icc_zero,
        Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons, sum_filter]
      simp [a]
    have hlog : Real.log ((i+1:ℕ):ℝ) ≤ Y := by
      rw [hY]; apply Real.log_le_log (by positivity)
      exact_mod_cast (show i+1 ≤ N+2 by omega)
    have hb := hp.trans (add_le_add (mul_le_mul_of_nonneg_left hlog hC) (le_refl (1537:ℝ)))
    dsimp [A,u]
    rw [heq, div_pow, show (Real.log ((i:ℝ)+1))^2 / Y^2 / 2 =
      ((Real.log ((i+1:ℕ):ℝ))^2 / 2)/Y^2 by push_cast; ring,
      ← sub_div, abs_div, abs_of_nonneg (sq_nonneg Y)]
    exact div_le_div_of_nonneg_right hb (sq_nonneg _)
  have hm := MasulloRH.uniform_damped_resolvent_mesh_discrepancy
    (N+1) u A c (Real.log 2/Y) ((C*Y+1537)/Y^2) hc
    (div_nonneg (Real.log_nonneg (by norm_num)) hy.le) (by positivity)
    hmono hu0 hu1 hA0 (fun i _ => hmesh i) hD
  have heq : (∑ i ∈ range (N+1), Real.exp (-c*u (i+1)) * (A (i+1)-A i)) =
      ∑ i ∈ (range (N+1)).filter (fun i => (i+2).Prime),
      Real.exp (-c*(Real.log ((i:ℝ)+2)/Y)) * (Real.log ((i:ℝ)+2)^2 / ((i:ℝ)+2) / Y^2) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro i _
    have hdiff : A (i+1)-A i = a (i+2)/Y^2 := by
      dsimp [A]; rw [show i+1+2=(i+2)+1 by omega, sum_range_succ]; ring
    rw [hdiff]
    dsimp [u]; push_cast
    rw [show (i:ℝ)+1+1=(i:ℝ)+2 by ring]
    by_cases h : (i+2).Prime <;> simp [a,h]
  rw [heq] at hm
  exact hm
