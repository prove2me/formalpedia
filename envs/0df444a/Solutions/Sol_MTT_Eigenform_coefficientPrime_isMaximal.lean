-- Prove2me | solution 1 for MTT.Eigenform.coefficientPrime_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-20T10:42:35.606957+00:00
-- url     : https://prove2.me/submissions/1334ed49-8e51-4902-9e52-f65f6daebd7d

import Theorems.Thm_MTT_Eigenform_coefficientPrime_isPrime
import Theorems.Thm_MTT_Eigenform_coefficientPrime_ne_bot
import Theorems.Thm_MTT_numberField_coefficientField
import Mathlib.RingTheory.DedekindDomain.Basic

set_option autoImplicit false
noncomputable section

theorem solution
    {N k p : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    (f.coefficientPrime ιp).IsMaximal := by
  let _ := MTT.numberField_coefficientField hN hk ι f
  exact (f.coefficientPrime_isPrime ιp).isMaximal
    (f.coefficientPrime_ne_bot ιp)
