-- Prove2me | solution 1 for Nock.Verb.eval_crash_mono_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:23.357052+00:00
-- url     : https://prove2.me/submissions/49c259aa-9f68-4bb1-a2e9-fd2b10664908

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_eval_crash_mono

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {n m : Nat} {v : Verb} (hnm : n ≤ m) (h : eval n v = .crash) :
    eval m v = .crash := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact eval_crash_mono ih
end Nock.Verb
