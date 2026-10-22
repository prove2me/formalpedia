-- Prove2me | solution 1 for MLLangevin.General.display_28
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:41:03.848486+00:00
-- url     : https://prove2.me/submissions/5d9f08ad-df21-411a-a4f6-5a3e6b73f978

import Mathlib
import Definitions.Def_MLLangevin_General_Setting
set_option autoImplicit false
open MLLangevin.General

theorem ww_term (a γ₀ T₀ : ℝ) (hγ₀ : 0 < γ₀) (r : ℕ) (hr : 1 ≤ r) :
    geomHorizon T₀ a r / levelStep γ₀ r + geomHorizon T₀ a r / levelStep γ₀ (r - 1)
      = T₀ / γ₀ * (3 / 2) * ((2 : ℝ) ^ ((1 - a) / 2)) ^ r := by
  unfold geomHorizon levelStep
  have hy : (2 : ℝ) ^ (-((1 + a) / 2) * (r : ℝ)) = ((2 : ℝ) ^ (-((1 + a) / 2))) ^ r := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_natCast]
  have hx : (2 : ℝ) ^ ((1 - a) / 2) = 2 * (2 : ℝ) ^ (-((1 + a) / 2)) := by
    have : (1 - a) / 2 = 1 + (-((1 + a) / 2)) := by ring
    rw [this, Real.rpow_add (by norm_num), Real.rpow_one]
  rw [hy, hx]
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h2 : (0 : ℝ) < 2 := by norm_num
  field_simp
  ring

theorem ww_geom (x : ℝ) (R : ℕ) :
    (1 - x) * ∑ r ∈ Finset.Icc 1 R, x ^ r = x - x ^ (R + 1) := by
  induction R with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

theorem solution (𝔞 γ₀ T₀ : ℝ) (R : ℕ) (h𝔞 : 1 ≤ 𝔞 ∧ 𝔞 ≤ 2) (hγ₀ : 0 < γ₀) (hT₀ : 0 < T₀) :
    cost R γ₀ (geomHorizon T₀ 𝔞)
      ≤ if 1 < 𝔞 then T₀ / γ₀ * (1 + 3 / 2 * ((2 : ℝ) ^ ((𝔞 - 1) / 2) - 1)⁻¹)
        else T₀ * (1 + 3 / 2 * (R : ℝ)) / γ₀ := by
  set x : ℝ := (2 : ℝ) ^ ((1 - 𝔞) / 2) with hxdef
  have hxpos : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  have hcost : cost R γ₀ (geomHorizon T₀ 𝔞)
      = T₀ / γ₀ + T₀ / γ₀ * (3 / 2) * ∑ r ∈ Finset.Icc 1 R, x ^ r := by
    unfold cost
    rw [Finset.sum_congr rfl (fun r hr => ww_term 𝔞 γ₀ T₀ hγ₀ r (Finset.mem_Icc.1 hr).1),
      ← Finset.mul_sum]
    have : geomHorizon T₀ 𝔞 0 = T₀ := by simp [geomHorizon]
    rw [this]
  rw [hcost]
  by_cases h1 : 1 < 𝔞
  · rw [if_pos h1]
    have hx1 : x < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      linarith
    have hxinv : x⁻¹ = (2 : ℝ) ^ ((𝔞 - 1) / 2) := by
      rw [hxdef, ← Real.rpow_neg (by norm_num)]
      congr 1
      ring
    have hsum : ∑ r ∈ Finset.Icc 1 R, x ^ r ≤ ((2 : ℝ) ^ ((𝔞 - 1) / 2) - 1)⁻¹ := by
      rw [← hxinv]
      have hg := ww_geom x R
      have h1x : 0 < 1 - x := by linarith
      have hxR : 0 < x ^ (R + 1) := pow_pos hxpos _
      have hle : ∑ r ∈ Finset.Icc 1 R, x ^ r ≤ x / (1 - x) := by
        rw [le_div_iff₀ h1x, mul_comm]
        linarith
      have heq : x / (1 - x) = (x⁻¹ - 1)⁻¹ := by
        field_simp
      rw [← heq]
      exact hle
    have hc : 0 ≤ T₀ / γ₀ * (3 / 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsum hc]
  · rw [if_neg h1]
    have h𝔞1 : 𝔞 = 1 := le_antisymm (not_lt.1 h1) h𝔞.1
    have hx1 : x = 1 := by
      rw [hxdef, h𝔞1]; norm_num
    rw [hx1]
    simp only [one_pow, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
    have : (R + 1 - 1 : ℕ) = R := by omega
    rw [this]
    field_simp
    ring_nf
    rfl
