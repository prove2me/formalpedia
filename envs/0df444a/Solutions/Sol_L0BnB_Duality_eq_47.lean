-- Prove2me | solution 1 for L0BnB.Duality.eq_47
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:26:16.521515+00:00
-- url     : https://prove2.me/submissions/bc1d140b-4ba7-4be9-9ba2-3e484f074f0b

import Mathlib
import Definitions.Def_L0BnB_Duality_Dual

set_option autoImplicit false
open L0BnB.Duality

theorem solution (lam0 lam2 a η : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hη : 0 ≤ η)
    (hcase : |a| - η ≥ 2 * Real.sqrt (lam0 * lam2)) :
    IsLeast (Set.range (D lam0 lam2 a η)) (-(1 / (4 * lam2)) * (|a| - η) ^ 2 + lam0) := by
  have hD : ∀ b, D lam0 lam2 a η b = 2 * lam0 * (if |b * Real.sqrt (lam2 / lam0)| ≤ 1 then |b * Real.sqrt (lam2 / lam0)| else ((b * Real.sqrt (lam2 / lam0)) ^ 2 + 1) / 2)
      + a * b + η * |b| := by
    intro b
    unfold D L0BnB.Reduced.psi1 L0BnB.Reduced.reverseHuber
    rfl
  have hw0 : 0 < Real.sqrt (lam0 * lam2) := Real.sqrt_pos.mpr (mul_pos hlam0 hlam2)
  have hw2 : Real.sqrt (lam0 * lam2) ^ 2 = lam0 * lam2 := Real.sq_sqrt (mul_pos hlam0 hlam2).le
  have hs0 : 0 < Real.sqrt (lam2 / lam0) := Real.sqrt_pos.mpr (div_pos hlam2 hlam0)
  have hs2 : Real.sqrt (lam2 / lam0) ^ 2 = lam2 / lam0 := Real.sq_sqrt (div_pos hlam2 hlam0).le
  generalize Real.sqrt (lam0 * lam2) = w at hw0 hw2 hcase
  generalize Real.sqrt (lam2 / lam0) = s at hs0 hs2 hD
  generalize hcdef : |a| - η = c at hcase
  have hls2 : lam0 * s ^ 2 = lam2 := by rw [hs2]; field_simp
  have hws : lam0 * s = w := by
    have h1 : (lam0 * s) ^ 2 = w ^ 2 := by
      rw [mul_pow, hw2]; nlinarith [hls2]
    exact (sq_eq_sq₀ (by positivity) hw0.le).mp h1
  have hws2 : w * s = lam2 := by rw [← hws]; nlinarith [hls2]
  have hc2 : 2 * w ≤ c := hcase
  have hcpos : 0 < c := by linarith
  constructor
  · -- attained
    let b0 : ℝ := if 0 ≤ a then -(c / (2 * lam2)) else c / (2 * lam2)
    have hb0abs : |b0| = c / (2 * lam2) := by
      unfold b0
      split_ifs
      · rw [abs_neg, abs_of_pos (by positivity)]
      · rw [abs_of_pos (by positivity)]
    have hab0 : a * b0 = -|a| * (c / (2 * lam2)) := by
      unfold b0
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (not_le.mp h)]; ring
    have hbs : 1 ≤ |b0 * s| := by
      rw [abs_mul, hb0abs, abs_of_pos hs0]
      rw [← sub_nonneg]
      have : c / (2 * lam2) * s - 1 = (c * s - 2 * lam2) / (2 * lam2) := by field_simp
      rw [this]
      apply div_nonneg _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_right hc2 hs0.le]
    refine ⟨b0, ?_⟩
    rw [hD]
    have hRH : (if |b0 * s| ≤ 1 then |b0 * s| else ((b0 * s) ^ 2 + 1) / 2) = ((b0 * s) ^ 2 + 1) / 2 := by
      split_ifs with h
      · have h1 : |b0 * s| = 1 := le_antisymm h hbs
        have h2 : (b0 * s) ^ 2 = 1 := by rw [← sq_abs, h1]; norm_num
        rw [h1, h2]; norm_num
      · rfl
    rw [hRH, hab0, hb0abs]
    have hb2 : (b0 * s) ^ 2 = (c / (2 * lam2)) ^ 2 * s ^ 2 := by
      rw [mul_pow, ← sq_abs b0, hb0abs]
    rw [hb2]
    have hη' : η = |a| - c := by linarith [hcdef]
    rw [hη']
    field_simp
    nlinarith [hls2]
  · rintro _ ⟨b, rfl⟩
    rw [hD]
    have hab : -|a| * |b| ≤ a * b := by
      have := neg_abs_le (a * b)
      rw [abs_mul] at this
      linarith
    have hη' : η = |a| - c := by linarith [hcdef]
    have hb0 : 0 ≤ |b| := abs_nonneg b
    by_cases hcs : |b * s| ≤ 1
    · rw [if_pos hcs]
      have h1 : |b * s| = |b| * s := by rw [abs_mul, abs_of_pos hs0]
      rw [h1] at hcs ⊢
      have h2 : |b| * w ≤ lam0 := by
        have := mul_le_mul_of_nonneg_left hcs hlam0.le
        nlinarith [hws]
      have h3 : lam2 * |b| ≤ w := by
        have h4 : lam2 * |b| * w ≤ w * w := by nlinarith [hw2]
        exact le_of_mul_le_mul_right h4 hw0
      have h5 : 2 * lam0 * (|b| * s) = 2 * w * |b| := by
        rw [← hws]; ring
      rw [h5]
      have : 0 ≤ (c - 2 * w) * (2 * w + c - 4 * lam2 * |b|) :=
        mul_nonneg (by linarith) (by linarith)
      have e : -(1 / (4 * lam2)) * c ^ 2 + lam0 = (4 * lam0 * lam2 - c ^ 2) / (4 * lam2) := by
        field_simp
        ring
      rw [e, div_le_iff₀ (by positivity)]
      have hlam : lam0 * lam2 = w ^ 2 := hw2.symm
      nlinarith [hab, this]
    · rw [if_neg hcs]
      have h1 : (b * s) ^ 2 = |b| ^ 2 * s ^ 2 := by rw [mul_pow, sq_abs]
      rw [h1]
      have h6 : 2 * lam0 * ((|b| ^ 2 * s ^ 2 + 1) / 2) = lam2 * |b| ^ 2 + lam0 := by
        have : lam0 * (|b| ^ 2 * s ^ 2) = lam2 * |b| ^ 2 := by
          calc lam0 * (|b| ^ 2 * s ^ 2) = |b| ^ 2 * (lam0 * s ^ 2) := by ring
            _ = lam2 * |b| ^ 2 := by rw [hls2]; ring
        nlinarith [this]
      rw [h6]
      have e : -(1 / (4 * lam2)) * c ^ 2 + lam0 = lam0 - c ^ 2 / (4 * lam2) := by ring
      rw [e]
      have h7 : 0 ≤ (2 * lam2 * |b| - c) ^ 2 / (4 * lam2) := by positivity
      have h8 : (2 * lam2 * |b| - c) ^ 2 / (4 * lam2) = lam2 * |b| ^ 2 - c * |b| + c ^ 2 / (4 * lam2) := by
        field_simp; ring
      rw [hη']
      nlinarith [hab, h7, h8]
