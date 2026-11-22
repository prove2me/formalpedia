-- Prove2me | solution 1 for Nock.evalPaper_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:28.482801+00:00
-- url     : https://prove2.me/submissions/07bcb459-67ae-4312-8487-c9196de9b6f0

module
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Theorems.Thm_Nock_evalPaper_succ

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Noun
namespace Nock
theorem _root_.solution {n m : Nat} {s form r : Noun}
    (hle : n ≤ m) (h : evalPaper n s form = some r) : evalPaper m s form = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact evalPaper_succ ih
end Nock
