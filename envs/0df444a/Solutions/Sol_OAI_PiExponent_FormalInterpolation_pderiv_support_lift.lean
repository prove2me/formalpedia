-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.pderiv_support_lift
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:09:52.608042+00:00
-- url     : https://prove2.me/submissions/1fbd4177-f6d0-4ddb-a80f-4c29ba8297ff

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib

open OAI.PiExponent.FormalInterpolation

open MeasureTheory Filter Topology in

theorem solution
    {d : Nat} (i : Fin d) (F : MvPolynomial (Fin d) Complex)
    (a : Fin d →₀ Nat) (ha : a ∈ (MvPolynomial.pderiv i F).support) :
    ∃ b ∈ F.support, b = a + Finsupp.single i 1 := by
  refine ⟨_, ?_, rfl⟩
  rw [MvPolynomial.mem_support_iff] at ha ⊢
  rw [MvPolynomial.coeff_pderiv] at ha
  exact left_ne_zero_of_mul ha
