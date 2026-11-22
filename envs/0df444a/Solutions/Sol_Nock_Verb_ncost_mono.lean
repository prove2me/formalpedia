-- Prove2me | solution 1 for Nock.Verb.ncost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:25:50.143566+00:00
-- url     : https://prove2.me/submissions/c12ca6db-8272-4e66-81e6-91c0d24c6b3a

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_ncost_succ
public import Theorems.Thm_Nock_Verb_RelP_refl
public import Theorems.Thm_Nock_Verb_Rel_refl
public import Theorems.Thm_Nock_evalN_mono


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {n m : Nat} {a b r : Noun} (hle : n ≤ m) (hb : evalN n a b = some r) :
    ncost m a b = ncost n a b := by
  induction hle with
  | refl => rfl
  | step hk ih => rw [ncost_succ (evalN_mono hk hb)]; exact ih
end Nock.Verb
