-- Prove2me | solution 1 for OAI.ShortDraftCRT.exists_frequency_lift
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T01:05:40.777201+00:00
-- url     : https://prove2.me/submissions/1ac8f7e2-681d-47fe-8e20-d427a8f043c3

import Mathlib
set_option autoImplicit false
variable {R : Type*} [CommRing R]

theorem solution (N p h : R) (hcop : IsCoprime N p) :
    ∃k : R, N∣k ∧ p∣k-h := by
  obtain ⟨u,v,huv⟩ := hcop
  refine ⟨h*u*N,⟨h*u,by ring⟩,⟨-h*v,?_⟩⟩
  linear_combination h*huv
