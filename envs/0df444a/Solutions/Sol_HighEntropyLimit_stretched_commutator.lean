-- Prove2me | solution 1 for HighEntropyLimit.stretched_commutator
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:36:18.171988+00:00
-- url     : https://prove2.me/submissions/f06ebb5b-c435-49d1-bf6b-596a09e653d3

import Mathlib

theorem solution {A : Type*} [Ring A] [Algebra ℂ A] (X P : A) (hbar lam : ℝ)
    (hlam : 1 < lam) (hccr : X * P - P * X = (Complex.I * hbar) • (1 : A)) :
    ((Real.sqrt lam : ℂ) • X) * ((Real.sqrt lam : ℂ) • P) -
        ((Real.sqrt lam : ℂ) • P) * ((Real.sqrt lam : ℂ) • X) =
      (Complex.I * (lam * hbar : ℝ)) • (1 : A) := by
  have hs : ((Real.sqrt lam : ℂ) * (Real.sqrt lam : ℂ)) = (lam : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  rw [smul_mul_smul_comm, smul_mul_smul_comm, hs, ← smul_sub, hccr, smul_smul]
  congr 1
  push_cast; ring
