-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_successor_product_top_coeff_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T09:04:22.999612+00:00
-- url     : https://prove2.me/submissions/68fb9e3b-0214-433f-a9e6-29c8d62cb5b2

import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_top_exponent_product_coeff
import Mathlib.RingTheory.PowerSeries.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

/-!
The positive zeroth-coordinate coefficient vanishes at the maximal
successor exponents, by the previously proved coefficient theorem.
-/
theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ)
    (a d : Fin (m + 1) →₀ ℕ)
    (htop : ∀ i : Fin m, d i.succ = a i.succ)
    (hpos : d 0 ≠ 0) :
    MvPowerSeries.coeff d
        (∏ i : Fin m,
          (MvPowerSeries.X i.succ + liftLogSeries m (delta i)) ^ (a i.succ)) = 0 := by
  exact OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_top_exponent_product_coeff
    delta a d htop hpos
