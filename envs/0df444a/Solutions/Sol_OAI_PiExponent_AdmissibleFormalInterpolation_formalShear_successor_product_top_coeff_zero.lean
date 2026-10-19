-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_top_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:56:03.695277+00:00
-- url     : https://prove2.me/submissions/d5c86b57-5ad3-423e-b697-c124c40e6350

import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_shear_top_zero_specialize
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_constant_shift_successor_product_top_coeff_zero

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ)
    (a d : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, d i.succ = a i.succ)
    (hzero : d 0 = 0) :
    MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X i.succ + liftLogSeries m (delta i)) ^ (a i.succ)) = 1 := by
  rw [OAI.PiExponent.AdmissibleFormalInterpolation.coeff_shear_top_zero_specialize
    delta a d htop hzero]
  exact OAI.PiExponent.AdmissibleFormalInterpolation.constant_shift_successor_product_top_coeff_zero
    (fun i => (delta i).constantCoeff) a d htop hzero