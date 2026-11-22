-- Prove2me | solution 1 for Nock.Verb.siblingAxis_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:17.531784+00:00
-- url     : https://prove2.me/submissions/aa799c0d-d09a-4035-8ec6-45f1a909f4a5

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
theorem _root_.solution (a : Nat) : siblingAxis (a + 2) / 2 = (a + 2) / 2 := by
  unfold siblingAxis
  by_cases hb : ((a + 2) % 2 == 0) = true
  · rw [if_pos hb]
    have hbn : (a + 2) % 2 = 0 := by simpa using hb
    omega
  · rw [if_neg hb]
    have hbn : (a + 2) % 2 ≠ 0 := by simpa using hb
    omega
end Nock.Verb
