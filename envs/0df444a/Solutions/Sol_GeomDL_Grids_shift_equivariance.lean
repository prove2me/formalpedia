-- Prove2me | solution 1 for GeomDL.Grids.shift_equivariance
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:33:55.681572+00:00
-- url     : https://prove2.me/submissions/3db48051-e02d-4807-a78c-cd6d3add1b97

import Mathlib
import Definitions.Def_GeomDL_Grids_Defs

open GeomDL.Grids Matrix

theorem solution {R : Type*} [CommRing R] {n : ℕ} [NeZero n]
    (θ x : ZMod n → R) :
    shift R n *ᵥ (circulant θ *ᵥ x) = circulant θ *ᵥ (shift R n *ᵥ x) := by
  rw [mulVec_mulVec, mulVec_mulVec, shift, circulant_mul_comm]
