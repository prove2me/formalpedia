-- Prove2me | solution 1 for OAI.ShortDraftCRT.fixed_additive_sector
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T01:18:46.090243+00:00
-- url     : https://prove2.me/submissions/c03ef15a-ce55-45ef-8b16-e75e09ed56fe

import Theorems.Thm_OAI_ShortDraftCRT_addChar_congr_of_dvd
import Theorems.Thm_OAI_ShortDraftCRT_inverse_weight_residue_congr
import Mathlib
set_option autoImplicit false
open OAI.ShortDraftCRT
variable {R : Type*} [CommRing R]

theorem solution {K : Type*} [Field K]
    (ι : R→+*K) (ψ : AddChar K ℂ) (lam D r r0 u u0 d d0 x : R)
    (hlam : ι lam≠0) (hD : ι D≠0)
    (hperiod : ∀y : R,ψ (ι y/ι lam)=1)
    (hcop : IsCoprime D r) (hr : D∣r-r0)
    (hu : D∣u*r-1) (hu0 : D∣u0*r0-1) (hd : D∣d-d0) :
    ψ (ι (-d*u)*ι x/(ι lam*ι D))=
      ψ (ι (-d0*u0)*ι x/(ι lam*ι D)) := by
  exact addChar_congr_of_dvd ι ψ lam D (-d*u) (-d0*u0) x hlam hD hperiod
    (inverse_weight_residue_congr D r r0 u u0 d d0 hcop hr hu hu0 hd)
