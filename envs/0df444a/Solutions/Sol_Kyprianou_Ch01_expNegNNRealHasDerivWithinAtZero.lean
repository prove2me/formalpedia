-- Prove2me | solution 1 for Kyprianou.Ch01.expNegNNRealHasDerivWithinAtZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:21:20.027284+00:00
-- url     : https://prove2.me/submissions/53d8b122-024c-4721-b25a-a6eecd78cd0a

import Mathlib
open Real Set Filter
open scoped NNReal
set_option autoImplicit false

theorem solution
    (c : ℝ) :
    HasDerivWithinAt
      (fun t : ℝ => Real.exp (-(c * (Real.toNNReal t : ℝ))))
      (-c) (Set.Ici 0) 0 := by
  have hlin : HasDerivAt (fun z : ℝ => -(c * z)) (-c) 0 := by
    simpa [mul_comm] using
      ((hasDerivAt_id (0 : ℝ)).neg).mul_const c
  have hexp : HasDerivAt (fun z : ℝ => Real.exp (-(c * z))) (-c) 0 := by
    have hh := (Real.hasDerivAt_exp (-(c * (0 : ℝ)))).comp 0 hlin
    simpa [Function.comp_def] using hh
  have hres : HasDerivWithinAt
      (fun z : ℝ => Real.exp (-(c * z))) (-c) (Set.Ici 0) 0 :=
    hexp.hasDerivWithinAt
  apply hres.congr
  · intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht
    rw [Real.coe_toNNReal t ht0]
  · simp
