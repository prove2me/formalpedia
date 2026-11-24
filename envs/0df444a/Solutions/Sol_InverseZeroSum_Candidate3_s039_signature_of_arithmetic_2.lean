-- Prove2me | solution 2 for InverseZeroSum.Candidate3.s039_signature_of_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:31:48.890263+00:00
-- url     : https://prove2.me/submissions/7a388534-a624-4d18-870a-d92fb6442cf5

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3

set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3
namespace InverseZeroSum.Candidate3
theorem _root_.solution {l s r : ℕ}
    (hl : 6 ≤ l) (hs : 8 ≤ s) (hls : l ≤ s)
    (hlen : l + 2 * s + r = 24) :
    S039Signature l s r := by
  have hs' : s = 8 ∨ s = 9 := by omega
  rcases hs' with hs8 | hs9
  · subst s
    have hl' : l = 6 ∨ l = 7 ∨ l = 8 := by omega
    rcases hl' with hl6 | hl7 | hl8
    · left
      omega
    · right
      left
      omega
    · right
      right
      left
      omega
  · subst s
    right
    right
    right
    omega
end InverseZeroSum.Candidate3
