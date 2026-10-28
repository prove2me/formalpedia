-- Prove2me | solution 1 for MazurProof.N13EffectiveDataCompatibility.cancel_invertible_ideal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:22:00.216425+00:00
-- url     : https://prove2.me/submissions/e2aefb45-bf60-4040-9da9-f4a36b33f742

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped nonZeroDivisors
theorem solution {T K : Type*} [CommRing T] [IsDomain T] [Field K] [Algebra T K] [IsFractionRing T K] (I J U : Ideal T) (hU : IsUnit (U : FractionalIdeal T⁰ K)) (h : I * U = J * U) : I = J := by
  have h2 : ((I * U : Ideal T) : FractionalIdeal T⁰ K) = ((J * U : Ideal T) : FractionalIdeal T⁰ K) := by
    rw [h]
  rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul, hU.mul_left_inj] at h2
  exact FractionalIdeal.coeIdeal_injective h2
