-- Prove2me | solution 1 for IncrKnapsack.PTAS.profit_rounding
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T02:58:44.395001+00:00
-- url     : https://prove2.me/submissions/2d23bb7e-3497-4a8b-bb9b-d90d9e3b5fac

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model

open Classical
open Finset BigOperators
open IncrKnapsack.PTAS

theorem solution (I : Instance) (hI : I.Standing) (K : ℕ) (hK : 4 < K)
    (S : Sol I) :
    pmin I * Psi I (pr I K) S ≤ Psi I I.p S ∧
      (1 - eps K) * Psi I I.p S ≤ pmin I * Psi I (pr I K) S := by
  have hne : (univ : Finset (Fin I.n)).Nonempty := ⟨⟨0, hI.n_pos⟩, mem_univ _⟩
  have hpmin : 0 < pmin I := by
    unfold pmin
    rw [dif_pos hne, Finset.lt_inf'_iff]
    intro i _; exact hI.p_pos i
  have hpmin_le : ∀ i, pmin I ≤ I.p i := by
    intro i; unfold pmin; rw [dif_pos hne]; exact Finset.inf'_le _ (mem_univ i)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have he : 0 < eps K := by unfold eps; positivity
  set b : ℝ := 1 + eps K with hb
  have hb1 : 1 < b := by linarith
  have hb0 : 0 < b := by linarith
  have item : ∀ i, pmin I * pr I K i ≤ I.p i ∧ (1 - eps K) * I.p i ≤ pmin I * pr I K i := by
    intro i
    set x := I.p i / pmin I with hx
    have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ hpmin]; simpa using hpmin_le i
    have hx0 : 0 < x := by linarith
    have hy : 0 ≤ Real.logb b x := Real.logb_nonneg hb1 hx1
    have hc1 : ((cls I K i : ℕ) : ℝ) ≤ Real.logb b x := Nat.floor_le hy
    have hc2 : Real.logb b x < ((cls I K i : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hpr : pr I K i = b ^ ((cls I K i : ℕ) : ℝ) := by
      unfold pr; rw [Real.rpow_natCast]
    have hxb : b ^ Real.logb b x = x := Real.rpow_logb hb0 hb1.ne' hx0
    have up : pr I K i ≤ x := by
      rw [hpr]; calc b ^ ((cls I K i : ℕ) : ℝ) ≤ b ^ Real.logb b x :=
            Real.rpow_le_rpow_of_exponent_le hb1.le hc1
        _ = x := hxb
    have lo : x < b * pr I K i := by
      rw [hpr]
      calc x = b ^ Real.logb b x := hxb.symm
        _ < b ^ (((cls I K i : ℕ) : ℝ) + 1) := Real.rpow_lt_rpow_of_exponent_lt hb1 hc2
        _ = b * b ^ ((cls I K i : ℕ) : ℝ) := by rw [Real.rpow_add_one hb0.ne']; ring
    have hpi : I.p i = pmin I * x := by rw [hx]; field_simp
    have hpr0 : 0 ≤ pr I K i := by unfold pr; positivity
    constructor
    · rw [hpi]; exact mul_le_mul_of_nonneg_left up hpmin.le
    · rw [hpi]
      have : (1 - eps K) * x ≤ pr I K i := by
        have h1 : (1 - eps K) * x ≤ (1 - eps K) * (b * pr I K i) := by
          have : 0 ≤ 1 - eps K := by
            unfold eps; rw [sub_nonneg, div_le_one hKpos]; exact_mod_cast (by omega : 1 ≤ K)
          exact mul_le_mul_of_nonneg_left lo.le this
        have h2 : (1 - eps K) * (b * pr I K i) ≤ pr I K i := by
          rw [hb]; nlinarith [sq_nonneg (eps K)]
        linarith
      nlinarith
  unfold Psi
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro t _
    rw [mul_left_comm, Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (hI.lam_nonneg t)
    exact Finset.sum_le_sum (fun i _ => (item i).1)
  · rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum; intro t _
    have h := Finset.sum_le_sum (fun i (_ : i ∈ S.set t) => (item i).2)
    rw [← Finset.mul_sum, ← Finset.mul_sum] at h
    have := mul_le_mul_of_nonneg_left h (hI.lam_nonneg t)
    linarith
