-- Prove2me | solution 1 for HardyFiveAxioms.real_composite_excess
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:30:49.186225+00:00
-- url     : https://prove2.me/submissions/97735bb9-8810-40c1-9d3e-d9bbe81404ce

import Mathlib
import Definitions.Def_hardy2001_signature

set_option autoImplicit false

open HardyFiveAxioms in
theorem dof11_two_mul_05418f90 (N : ℕ) :
    2 * dofOfSignature [1, 1] N = N * (N + 1) := by
  have h : dofOfSignature [1, 1] N = N + N.choose 2 := by
    simp [dofOfSignature, Fin.sum_univ_two]
  rw [h]
  clear h
  induction N with
  | zero => simp
  | succ n ih =>
    have e : (n + 1).choose 2 = n + n.choose 2 := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ', Nat.choose_one_right]
    rw [e]
    nlinarith [ih]

open HardyFiveAxioms in
theorem solution (NA NB : ℕ) (hA : 2 ≤ NA) (hB : 2 ≤ NB) :
    dofOfSignature [1, 1] NA * dofOfSignature [1, 1] NB < dofOfSignature [1, 1] (NA * NB) := by
  have a := dof11_two_mul_05418f90 NA
  have b := dof11_two_mul_05418f90 NB
  have c := dof11_two_mul_05418f90 (NA * NB)
  have key : (NA + 1) * (NB + 1) < 2 * (NA * NB + 1) := by nlinarith
  have hpos : 0 < NA * NB := by positivity
  have h4 : 4 * (dofOfSignature [1, 1] NA * dofOfSignature [1, 1] NB)
      < 4 * dofOfSignature [1, 1] (NA * NB) := by
    have e1 : 4 * (dofOfSignature [1, 1] NA * dofOfSignature [1, 1] NB)
        = (NA * NB) * ((NA + 1) * (NB + 1)) := by
      calc 4 * (dofOfSignature [1, 1] NA * dofOfSignature [1, 1] NB)
          = (2 * dofOfSignature [1, 1] NA) * (2 * dofOfSignature [1, 1] NB) := by ring
        _ = (NA * (NA + 1)) * (NB * (NB + 1)) := by rw [a, b]
        _ = (NA * NB) * ((NA + 1) * (NB + 1)) := by ring
    have e2 : 4 * dofOfSignature [1, 1] (NA * NB) = (NA * NB) * (2 * (NA * NB + 1)) := by
      calc 4 * dofOfSignature [1, 1] (NA * NB)
          = 2 * (2 * dofOfSignature [1, 1] (NA * NB)) := by ring
        _ = 2 * ((NA * NB) * (NA * NB + 1)) := by rw [c]
        _ = (NA * NB) * (2 * (NA * NB + 1)) := by ring
    rw [e1, e2]
    exact Nat.mul_lt_mul_of_pos_left key hpos
  omega
