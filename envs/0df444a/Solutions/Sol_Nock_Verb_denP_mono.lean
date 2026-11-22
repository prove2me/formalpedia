-- Prove2me | solution 1 for Nock.Verb.denP_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:09.027449+00:00
-- url     : https://prove2.me/submissions/11f45543-6651-44f6-bb0f-e9671cda088e

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_denP_succ
public import Theorems.Thm_Nock_Verb_Rel_refl


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {n m : Nat} {v : Verb} {r : Noun}
    (hle : n ≤ m) (h : denP n v = some r) : denP m v = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact denP_succ ih
end Nock.Verb
