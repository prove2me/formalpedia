-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.constant_shift_successor_product_top_coeff_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:15:58.007067+00:00
-- url     : https://prove2.me/submissions/7555dd89-8016-49a4-b245-4563d68d7e23
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_product_constant_shift_top_of_injective_coordinates

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (c : Fin m → ℂ)
    (a d : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, d i.succ = a i.succ)
    (hzero : d 0 = 0) :
    MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X i.succ + MvPowerSeries.C (c i)) ^ (a i.succ)) = 1 := by
  apply OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_top_of_injective_coordinates
    (v := Fin.succ) (x0 := 0) (c := c) (e := fun i => a i.succ) (d := d)
  · exact Fin.succ_injective m
  · intro i
    exact Fin.succ_ne_zero i
  · exact hzero
  · exact htop
  · intro x hx hnot
    revert hx hnot
    refine Fin.cases ?_ ?_ x
    · intro _ _
      simpa using hzero
    · intro i _ hnot
      exact (hnot i rfl).elim