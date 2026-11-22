-- Prove2me | solution 1 for Nock.Verb.adjNockCheckB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:29:34.171777+00:00
-- url     : https://prove2.me/submissions/5bae64b8-69a1-44df-b121-61a626e78d73

module
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_TraceCertificate

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution : ∀ (T : List Verb), adjNockCheckB T = true ↔ AdjNockCheck T
  | []             => by simp [adjNockCheckB, AdjNockCheck]
  | [_]            => by simp [adjNockCheckB, AdjNockCheck]
  | _ :: b :: rest => by
      simp only [adjNockCheckB, AdjNockCheck, Bool.and_eq_true]
      exact and_congr Iff.rfl (solution (b :: rest))
end Nock.Verb
