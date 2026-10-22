-- Prove2me | solution 1 for MarketplaceLeakage.Communication.ban_value
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:23:09.036744+00:00
-- url     : https://prove2.me/submissions/90ecad03-bbd0-45dc-8e91-6feda4bc40db

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_Setting
set_option autoImplicit false

open MarketplaceLeakage.Communication

theorem solution (v c : ℝ) (hvc : c < v) (hv : 0 < v) (q η : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hη0 : 0 ≤ η) (hη1 : η < 1) :
    IsBanValue v c q η (max (PiH v c q η) (PiL v c q η)) := by
  have hη : 0 < 1 - η := by linarith
  have hB : 0 ≤ η * q := by positivity
  have hA : 0 < 1 - η + η * q := by linarith
  set fm : ℝ := ((1 - η) * (q * v - c) - η * q * v * (1 - q)) / (1 - η) with hfm
  have hPiL : PiL v c q η = (1 - η + η * q) * fm := by
    unfold PiL; rw [hfm]; field_simp; ring
  have hPiH : PiH v c q η = η * q * (v - c) := rfl
  have hvc0 : 0 ≤ v - c := by linarith
  have hPiH0 : 0 ≤ PiH v c q η := by
    rw [hPiH]; exact mul_nonneg hB hvc0
  -- attainment of PiH
  have hatt_H : banRev v c q η (v - c) = PiH v c q η := by
    unfold banRev highPay lowPay
    have h1 : (1 - η + η * q) * (q * v - c - (v - c)) < η * q * (v - c - (v - c)) := by
      have : (1 - η + η * q) * (q * v - c - (v - c)) = -(1 - η + η * q) * (v * (1 - q)) := by ring
      rw [this]
      have : 0 < (1 - η + η * q) * (v * (1 - q)) := by
        have : 0 < 1 - q := by linarith
        positivity
      nlinarith
    rw [if_pos h1, if_pos (by simp), hPiH]; ring
  -- attainment of PiL
  have hatt_L : banRev v c q η fm = PiL v c q η := by
    unfold banRev highPay lowPay
    have heq : (1 - η + η * q) * (q * v - c - fm) = η * q * (v - c - fm) := by
      rw [hfm]; field_simp; ring
    have hlow : 0 ≤ (1 - η + η * q) * (q * v - c - fm) := by
      have : q * v - c - fm = η * q * v * (1 - q) / (1 - η) := by
        rw [hfm]; field_simp; ring
      rw [this]
      have : 0 < 1 - q := by linarith
      positivity
    rw [if_neg (by rw [heq]; exact lt_irrefl _), if_pos hlow, hPiL]; ring
  constructor
  · rcases max_choice (PiH v c q η) (PiL v c q η) with h | h
    · rw [h]; exact ⟨v - c, hatt_H⟩
    · rw [h]; exact ⟨fm, hatt_L⟩
  · rintro _ ⟨f, rfl⟩
    unfold banRev highPay lowPay
    by_cases h1 : (1 - η + η * q) * (q * v - c - f) < η * q * (v - c - f)
    · rw [if_pos h1]
      by_cases h2 : 0 ≤ η * q * (v - c - f)
      · rw [if_pos h2]
        have : f * (η * q) ≤ PiH v c q η := by
          rw [hPiH]
          rcases eq_or_lt_of_le hB with h0 | hpos
          · rw [← h0]; simp
          · have : f ≤ v - c := by
              by_contra hh; push_neg at hh
              nlinarith [mul_pos hpos (sub_pos.2 hh)]
            nlinarith
        exact le_trans this (le_max_left _ _)
      · rw [if_neg h2]; exact le_trans hPiH0 (le_max_left _ _)
    · rw [if_neg h1]
      by_cases h2 : 0 ≤ (1 - η + η * q) * (q * v - c - f)
      · rw [if_pos h2]
        push_neg at h1
        have hf : f ≤ fm := by
          rw [hfm, le_div_iff₀ hη]
          nlinarith [h1]
        have : f * (1 - η + η * q) ≤ PiL v c q η := by
          rw [hPiL]; nlinarith [mul_le_mul_of_nonneg_left hf hA.le]
        exact le_trans this (le_max_right _ _)
      · rw [if_neg h2]; exact le_trans hPiH0 (le_max_left _ _)
