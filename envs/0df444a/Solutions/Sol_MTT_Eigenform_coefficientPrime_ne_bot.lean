-- Prove2me | solution 1 for MTT.Eigenform.coefficientPrime_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-20T10:35:33.597323+00:00
-- url     : https://prove2.me/submissions/2b2643b3-b2db-4e19-9694-c01e84aa95a1

import Theorems.Thm_MTT_Eigenform_p_mem_coefficientPrime

set_option autoImplicit false
noncomputable section

theorem solution
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (ιp : MTT.Qbar →+* ℂ_[p]) :
    f.coefficientPrime ιp ≠ ⊥ := by
  intro hbot
  have hp := f.p_mem_coefficientPrime ιp
  rw [hbot, Ideal.mem_bot] at hp
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp
