-- Prove2me | solution 1 for GeneralCK.CKFast.hC1_actual
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T11:44:09.609002+00:00
-- url     : https://prove2.me/submissions/402eea78-219c-4d0e-a87e-7c84fc2ce5ef

import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_33554432_r62914560_838860800
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_50331648_r62914560_838860800
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u50331648_67108864_r62914560_838860800
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u67108864_83886080_r62914560_838860800

theorem solution : ∀ ⦃u rho : ℝ⦄, u ∈ Set.Icc (1/50 : ℝ) (1/10 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  rcases le_or_gt u (1/25 : ℝ) with h | h
  · exact GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r62914560_838860800 u rho ⟨hu.1, h⟩ hr hr1
  · have hu : u ∈ Set.Icc (1/25 : ℝ) (1/10 : ℝ) := ⟨h.le, hu.2⟩
    rcases le_or_gt u (3/50 : ℝ) with h | h
    · exact GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r62914560_838860800 u rho ⟨hu.1, h⟩ hr hr1
    · have hu : u ∈ Set.Icc (3/50 : ℝ) (1/10 : ℝ) := ⟨h.le, hu.2⟩
      rcases le_or_gt u (2/25 : ℝ) with h | h
      · exact GeneralCK.CKFast.Band.minors_pos_u50331648_67108864_r62914560_838860800 u rho ⟨hu.1, h⟩ hr hr1
      · have hu : u ∈ Set.Icc (2/25 : ℝ) (1/10 : ℝ) := ⟨h.le, hu.2⟩
        exact GeneralCK.CKFast.Band.minors_pos_u67108864_83886080_r62914560_838860800 u rho hu hr hr1
