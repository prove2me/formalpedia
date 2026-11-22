-- Prove2me | solution 1 for Nock.Verb.denP_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:32.625028+00:00
-- url     : https://prove2.me/submissions/c2880e95-2206-47c2-a15d-d2f0a08e86be

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_evalPaper_succ


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {n : Nat} {v : Verb} {r : Noun}
    (h : denP n v = some r) : denP (n + 1) v = some r := by
  induction n, v using denP.induct generalizing r with
  | case1 k => simp only [denP] at h ⊢; exact h
  | case5 f l r' a b hrb hla ih2 ih1 =>
      have hla' : denP (f + 1) l = some a := ih2 hla
      have hrb' : denP (f + 1) r' = some b := ih1 hrb
      simp only [denP, hla, hrb] at h
      simp only [denP, hla', hrb']
      exact evalPaper_succ h
  | _ => simp_all only [denP, Option.some.injEq, reduceCtorEq]
end Nock.Verb
