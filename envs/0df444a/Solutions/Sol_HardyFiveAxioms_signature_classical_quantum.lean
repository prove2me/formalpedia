-- Prove2me | solution 1 for HardyFiveAxioms.signature_classical_quantum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:39:59.895903+00:00
-- url     : https://prove2.me/submissions/4b82fcb4-4a77-4c63-9a4b-e2ca622a43a8

import Mathlib
import Definitions.Def_hardy2001_signature

set_option autoImplicit false

open HardyFiveAxioms in
theorem solution (N : ℕ) :
    dofOfSignature [1] N = N ∧ dofOfSignature [1, 2] N = N ^ 2 := by
  have h2 : N.choose 2 * 2 = N * (N - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.div_mul_cancel (Nat.even_mul_pred_self N).two_dvd
  constructor
  · simp [dofOfSignature]
  · simp [dofOfSignature, Fin.sum_univ_two]
    rw [h2]
    rcases N with _ | n
    · simp
    · simp only [Nat.add_sub_cancel]
      ring
