-- Prove2me | solution 1 for Nock.Verb.DenP_ofNoun_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:54.670486+00:00
-- url     : https://prove2.me/submissions/cfa3388f-6ca1-481c-aaf6-6e65f887ef8f

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_DenP_terminal_iff
public import Theorems.Thm_Nock_Verb_ofNoun_noun
public import Theorems.Thm_Nock_Verb_ofNoun_terminal


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {n x} : DenP (ofNoun n) x ↔ x = n := by
  rw [DenP_terminal_iff (ofNoun_terminal n), ofNoun_noun]
end Nock.Verb
