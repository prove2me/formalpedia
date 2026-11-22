-- Prove2me | solution 1 for Nock.Verb.siblingAxis_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:22.295808+00:00
-- url     : https://prove2.me/submissions/7a1a69ff-122d-469c-b2e1-08f01eb72344

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (a : Nat) :
    ((siblingAxis (a + 2)) % 2 == 0) = !((a + 2) % 2 == 0) := by
  unfold siblingAxis
  by_cases hb : ((a + 2) % 2 == 0) = true
  · have hbn : (a + 2) % 2 = 0 := by simpa using hb
    rw [if_pos hb, hb]
    have h1 : (a + 2 + 1) % 2 = 1 := by omega
    rw [h1]; decide
  · have hbf : ((a + 2) % 2 == 0) = false := by
      cases hh : (a + 2) % 2 == 0 with
      | true => exact absurd hh hb
      | false => rfl
    have hbn : (a + 2) % 2 ≠ 0 := by simpa using hb
    rw [if_neg hb, hbf]
    have h0 : (a + 2 - 1) % 2 = 0 := by omega
    rw [h0]; decide
end Nock.Verb
