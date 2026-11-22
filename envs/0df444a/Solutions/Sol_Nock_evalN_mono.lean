-- Prove2me | solution 1 for Nock.evalN_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:27.751446+00:00
-- url     : https://prove2.me/submissions/ed5f06cd-2a0b-4d5f-ae99-27afd96d5394

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Theorems.Thm_Nock_evalN_succ

set_option autoImplicit true
@[expose] public section
public section
open Nock
namespace Nock
theorem _root_.solution {n m : Nat} {s form r : Noun}
    (hle : n ≤ m) (h : evalN n s form = some r) : evalN m s form = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalN_succ ih
end Nock
