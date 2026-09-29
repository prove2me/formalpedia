-- Prove2me | solution 1 for GeneralCK.CKFast.hC2_actual
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T11:42:32.471775+00:00
-- url     : https://prove2.me/submissions/eaa2ffc3-c6e6-4fba-9339-b374f9c11573

import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u83886080_104857600_r83886080_838860800
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u104857600_125829120_r83886080_838860800
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u125829120_146800640_r83886080_838860800
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u146800640_167772160_r83886080_838860800

theorem solution : ∀ ⦃u rho : ℝ⦄, u ∈ Set.Icc (1/10 : ℝ) (1/5 : ℝ) →
    rho ∈ Set.Icc (1/10 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  rcases le_or_gt u (1/8 : ℝ) with h | h
  · exact GeneralCK.CKFast.Band.minors_pos_u83886080_104857600_r83886080_838860800 u rho ⟨hu.1, h⟩ hr hr1
  · have hu : u ∈ Set.Icc (1/8 : ℝ) (1/5 : ℝ) := ⟨h.le, hu.2⟩
    rcases le_or_gt u (3/20 : ℝ) with h | h
    · exact GeneralCK.CKFast.Band.minors_pos_u104857600_125829120_r83886080_838860800 u rho ⟨hu.1, h⟩ hr hr1
    · have hu : u ∈ Set.Icc (3/20 : ℝ) (1/5 : ℝ) := ⟨h.le, hu.2⟩
      rcases le_or_gt u (7/40 : ℝ) with h | h
      · exact GeneralCK.CKFast.Band.minors_pos_u125829120_146800640_r83886080_838860800 u rho ⟨hu.1, h⟩ hr hr1
      · have hu : u ∈ Set.Icc (7/40 : ℝ) (1/5 : ℝ) := ⟨h.le, hu.2⟩
        exact GeneralCK.CKFast.Band.minors_pos_u146800640_167772160_r83886080_838860800 u rho hu hr hr1
