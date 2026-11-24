-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s9_two_fibre_count_transitions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:34:09.970301+00:00
-- url     : https://prove2.me/submissions/f7020f67-5776-4944-a3c0-f2c96d0fa87d

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
set_option maxHeartbeats 500000
namespace InverseZeroSum.Candidate3
theorem _root_.solution
    (p q : ℕ) (hp : p + 1 ≤ 2) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hBefore : p = 1 → q ≠ 1)
    (hAfter : p + 1 = 1 → q - 1 ≠ 1) :
    (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 2) := by
  omega
end InverseZeroSum.Candidate3
