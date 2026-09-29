-- Prove2me | solution 1 for GeneralCK.CKFast.directC3_actual
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T17:55:17.174306+00:00
-- url     : https://prove2.me/submissions/d345ea86-e0fc-4452-b2c1-85b4122946f4

import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u167772160_188743680_r125829120_838860800
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u188743680_209715200_r125829120_838860800
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u209715200_230686720_r125829120_838860800
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u230686720_251658240_r125829120_838860800

theorem solution : ∀ ⦃u rho : ℝ⦄, u ∈ Set.Icc (1/5 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  rcases le_or_gt u (9/40 : ℝ) with h | h
  · exact GeneralCK.CKFast.Band.minors_pos_u167772160_188743680_r125829120_838860800 u rho ⟨hu.1, h⟩ hr hr1
  · have hu : u ∈ Set.Icc (9/40 : ℝ) (3/10 : ℝ) := ⟨h.le, hu.2⟩
    rcases le_or_gt u (1/4 : ℝ) with h | h
    · exact GeneralCK.CKFast.Band.minors_pos_u188743680_209715200_r125829120_838860800 u rho ⟨hu.1, h⟩ hr hr1
    · have hu : u ∈ Set.Icc (1/4 : ℝ) (3/10 : ℝ) := ⟨h.le, hu.2⟩
      rcases le_or_gt u (11/40 : ℝ) with h | h
      · exact GeneralCK.CKFast.Band.minors_pos_u209715200_230686720_r125829120_838860800 u rho ⟨hu.1, h⟩ hr hr1
      · have hu : u ∈ Set.Icc (11/40 : ℝ) (3/10 : ℝ) := ⟨h.le, hu.2⟩
        exact GeneralCK.CKFast.Band.minors_pos_u230686720_251658240_r125829120_838860800 u rho hu hr hr1
