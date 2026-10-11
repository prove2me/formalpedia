-- Prove2me | solution 1 for GravityNonRenorm.cft_entropy_energy_eq29
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T11:51:17.400381+00:00
-- url     : https://prove2.me/submissions/2b63d689-8ea7-43d0-96c3-a4a91f4e2474

import Definitions.Def_GravityNonRenorm_Defs
import Mathlib

open GravityNonRenorm Filter Asymptotics

namespace GravityNonRenorm

theorem cfte29_main (d : ℕ) (hd : 2 ≤ d) (a b R T : ℝ) (hb : 0 < b) (hR : 0 < R)
    (hT : 0 < T) :
    cftEntropyOfEnergy d a b R (b * R ^ (d - 1) * T ^ d) = a * (R * T) ^ (d - 1) := by
  unfold cftEntropyOfEnergy
  have hbR : b * R ^ (d - 1) ≠ 0 := by positivity
  have h1 : b * R ^ (d - 1) * T ^ d / (b * R ^ (d - 1)) = T ^ d := by
    exact mul_div_cancel_left₀ _ hbR
  have hd0 : d ≠ 0 := by omega
  rw [h1, one_div, Real.pow_rpow_inv_natCast hT.le hd0]

end GravityNonRenorm

theorem solution (d : ℕ) (hd : 2 ≤ d) (a b R T : ℝ) (hb : 0 < b) (hR : 0 < R)
    (hT : 0 < T) :
    cftEntropyOfEnergy d a b R (b * R ^ (d - 1) * T ^ d) = a * (R * T) ^ (d - 1) :=
  GravityNonRenorm.cfte29_main d hd a b R T hb hR hT
