-- Prove2me | solution 1 for HardyFiveAxioms.signature_real_quaternionic_cubic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T02:21:53.327768+00:00
-- url     : https://prove2.me/submissions/502b5af8-5e20-452f-8a3c-72fffb7dc056

import Mathlib
import Definitions.Def_hardy2001_signature

namespace HardyFiveAxioms.P7bf6598d

theorem two_choose_two (N : ℕ) : 2 * N.choose 2 + N = N ^ 2 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith [ih]

theorem six_choose_three (N : ℕ) : 6 * N.choose 3 + 6 * N.choose 2 + N = N ^ 3 := by
  induction N with
  | zero => simp
  | succ n ih =>
    have h2 := two_choose_two n
    rw [Nat.choose_succ_succ (n := n) (k := 2), Nat.choose_succ_succ (n := n) (k := 1),
      Nat.choose_one_right]
    nlinarith [ih, h2]

end HardyFiveAxioms.P7bf6598d

open HardyFiveAxioms in
theorem solution (N : ℕ) :
    2 * dofOfSignature [1, 1] N = N * (N + 1) ∧
      dofOfSignature [1, 4] N + N = 2 * N ^ 2 ∧
      dofOfSignature [1, 6, 6] N = N ^ 3 := by
  have h2 := HardyFiveAxioms.P7bf6598d.two_choose_two N
  have h3 := HardyFiveAxioms.P7bf6598d.six_choose_three N
  simp only [dofOfSignature, Fin.sum_univ_succ, Fin.sum_univ_zero, List.length_cons,
    List.length_nil, Fin.val_zero, Fin.val_succ, List.get_eq_getElem]
  simp only [Fin.val_zero, Fin.val_succ, Nat.choose_one_right, zero_add, List.getElem_cons_zero,
    List.getElem_cons_succ, Fin.succ_zero_eq_one, Fin.val_one, Fin.val_two]
  norm_num
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [h2, h3]
