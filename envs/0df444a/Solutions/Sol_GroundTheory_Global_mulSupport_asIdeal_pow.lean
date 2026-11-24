-- Prove2me | solution 1 for GroundTheory.Global.mulSupport_asIdeal_pow
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:59:44.066292+00:00
-- url     : https://prove2.me/submissions/c17571de-dcde-4ba2-b181-f2c3899a5895

import Mathlib
open IsDedekindDomain Function
variable {R : Type*} [CommRing R]


theorem solution (a : HeightOneSpectrum R → ℕ) :
    mulSupport (fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v) = support a := by
  ext v; change (v.asIdeal ^ a v ≠ 1) ↔ a v ≠ 0
  constructor
  · intro hp h0; exact hp (by simp [h0])
  · intro hn he; apply v.isPrime.ne_top; apply top_unique
    have H := Ideal.pow_le_self (I := v.asIdeal) hn; simpa only [he, Ideal.one_eq_top] using H
