-- Prove2me | solution 1 for Nock.Verb.den_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:02:31.515801+00:00
-- url     : https://prove2.me/submissions/bd04bde5-d596-4d0a-be5d-abe53c4f698b

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_evalN_succ


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {n : Nat} {v : Verb} {r : Noun}
    (h : den n v = some r) : den (n + 1) v = some r := by
  induction n, v using den.induct generalizing r with
  | case1 k => simp only [den] at h ⊢; exact h
  | case5 f l r' a b hrb hla ih2 ih1 =>
      have hla' : den (f + 1) l = some a := ih2 hla
      have hrb' : den (f + 1) r' = some b := ih1 hrb
      simp only [den, hla, hrb] at h
      simp only [den, hla', hrb']
      exact evalN_succ h
  | _ => simp_all only [den, Option.some.injEq, reduceCtorEq]
end Nock.Verb
