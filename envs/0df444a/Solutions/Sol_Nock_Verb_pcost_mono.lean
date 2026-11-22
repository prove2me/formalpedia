-- Prove2me | solution 1 for Nock.Verb.pcost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:08.973699+00:00
-- url     : https://prove2.me/submissions/e2d4c710-3cf3-4ccd-b2de-fad52e7c445e

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_RelP_refl
public import Theorems.Thm_Nock_Verb_pcost_succ
public import Theorems.Thm_Nock_Verb_Rel_refl
public import Theorems.Thm_Nock_evalPaper_mono


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {n m : Nat} {a b r : Noun} (hle : n ≤ m) (hb : evalPaper n a b = some r) :
    pcost m a b = pcost n a b := by
  induction hle with
  | refl => rfl
  | step hk ih => rw [pcost_succ (evalPaper_mono hk hb)]; exact ih
end Nock.Verb
