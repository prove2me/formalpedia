-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_top_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:48:17.751979+00:00
-- url     : https://prove2.me/submissions/4a3435a3-64a6-4600-a668-b6337a01c18b

import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_successor_product_top_coeff_zero
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_successor_product_top_coeff_pos

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ)
    (a d : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, d i.succ = a i.succ) :
    MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X i.succ + liftLogSeries m (delta i)) ^ (a i.succ)) =
      if d 0 = 0 then 1 else 0 := by
  by_cases hzero : d 0 = 0
  · rw [if_pos hzero]
    exact OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_top_coeff_zero
      delta a d htop hzero
  · rw [if_neg hzero]
    exact OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_top_coeff_pos
      delta a d htop hzero