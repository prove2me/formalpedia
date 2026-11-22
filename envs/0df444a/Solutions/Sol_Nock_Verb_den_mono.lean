-- Prove2me | solution 1 for Nock.Verb.den_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:58.219124+00:00
-- url     : https://prove2.me/submissions/59d80f18-daeb-4116-b54a-124b20ca45ec

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_den_succ

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {n m : Nat} {v : Verb} {r : Noun}
    (hle : n ≤ m) (h : den n v = some r) : den m v = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact den_succ ih
end Nock.Verb
