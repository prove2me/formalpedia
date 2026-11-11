-- Prove2me | solution 1 for OAI.ShortDraftCRT.strong_sector_additive_congruences
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T01:09:46.754204+00:00
-- url     : https://prove2.me/submissions/2b1eda8e-28d5-45ac-b602-52561c976396

import Mathlib
set_option autoImplicit false
variable {R : Type*} [CommRing R]

theorem solution (M lam c r r0 d d0 : R)
    (hlam : lam^3∣M) (hc : c∣M) (hr : M^2∣r-r0) (hd : M*c∣d-d0) :
    lam^3*c∣r-r0 ∧ lam^3*c∣d-d0 := by
  constructor
  · apply (show lam^3*c ∣ M^2 by simpa only [pow_two] using mul_dvd_mul hlam hc).trans hr
  · exact (mul_dvd_mul hlam (dvd_refl c)).trans hd
