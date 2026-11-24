-- Prove2me | solution 1 for InverseZeroSum.Candidate3.s039_signature_of_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T05:31:25.323474+00:00
-- url     : https://prove2.me/submissions/265533eb-a503-4416-9e2f-eafe7b9bcbb8

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3


theorem solution {l s r : ℕ}
    (hl : 6 ≤ l) (hs : 8 ≤ s) (hls : l ≤ s)
    (hlen : l + 2 * s + r = 24) :
    S039Signature l s r := by
  unfold S039Signature; omega
