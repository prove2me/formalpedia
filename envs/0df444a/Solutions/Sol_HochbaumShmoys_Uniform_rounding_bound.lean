-- Prove2me | solution 1 for HochbaumShmoys.Uniform.rounding_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T11:51:20.873988+00:00
-- url     : https://prove2.me/submissions/4c2a5f21-be74-486c-b252-8bbdca6673ea

import Mathlib
import Definitions.Def_HochbaumShmoys_Uniform_Rounding
open HochbaumShmoys.Uniform

theorem g69g_floor_bound (N : ℕ) (hN : 2 ≤ N) (y : ℝ) (hy : (N : ℝ) < y) :
    y ≤ (1 + (N : ℝ)⁻¹) * (⌊y⌋ : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hfl : (N : ℝ) ≤ (⌊y⌋ : ℝ) := by
    have : (N : ℤ) ≤ ⌊y⌋ := Int.le_floor.mpr (by exact_mod_cast hy.le)
    exact_mod_cast this
  have h1 : y < (⌊y⌋ : ℝ) + 1 := Int.lt_floor_add_one y
  have h2 : (1 : ℝ) ≤ (N : ℝ)⁻¹ * (⌊y⌋ : ℝ) := by
    rw [inv_mul_eq_div, le_div_iff₀ hN0]; linarith
  nlinarith

theorem solution (N : ℕ) (hN : 2 ≤ N) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    x ≤ (1 + (N : ℝ)⁻¹) * roundDown N x := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  set δ : ℝ := (N : ℝ)⁻¹ with hδ
  have hδ0 : 0 < δ := inv_pos.mpr hN0
  have hδ1 : δ < 1 := inv_lt_one_of_one_lt₀ hN1
  have hne : {q : ℕ | δ ^ (q + 1) < x}.Nonempty := by
    obtain ⟨q, hq⟩ := exists_pow_lt_of_lt_one hx0 hδ1
    exact ⟨q, lt_of_le_of_lt (pow_le_pow_of_le_one hδ0.le hδ1.le (Nat.le_succ q)) hq⟩
  have hk : δ ^ (intervalIndex N x + 1) < x := Nat.sInf_mem hne
  set k := intervalIndex N x
  unfold roundDown
  rw [← hδ]
  set y := x / δ ^ (k + 2)
  have hp : 0 < δ ^ (k + 2) := pow_pos hδ0 _
  have hy : (N : ℝ) < y := by
    rw [lt_div_iff₀ hp]
    have : (N : ℝ) * δ ^ (k + 2) = δ ^ (k + 1) := by
      rw [hδ, pow_succ, mul_comm, mul_assoc, inv_mul_cancel₀ hN0.ne', mul_one]
    rw [this]; exact hk
  have := g69g_floor_bound N hN y hy
  have hx : x = y * δ ^ (k + 2) := by simp [y, hp.ne']
  calc x = y * δ ^ (k + 2) := hx
    _ ≤ (1 + (N : ℝ)⁻¹) * (⌊y⌋ : ℝ) * δ ^ (k + 2) := mul_le_mul_of_nonneg_right this hp.le
    _ = _ := by rw [mul_assoc]
