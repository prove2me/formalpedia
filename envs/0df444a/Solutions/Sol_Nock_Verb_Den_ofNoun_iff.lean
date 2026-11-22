-- Prove2me | solution 1 for Nock.Verb.Den_ofNoun_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:00.542916+00:00
-- url     : https://prove2.me/submissions/e22917b2-1ab8-4995-acfe-ffe5fb69540d

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_Den_terminal_iff
public import Theorems.Thm_Nock_Verb_ofNoun_noun
public import Theorems.Thm_Nock_Verb_ofNoun_terminal

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {n x} : Den (ofNoun n) x ↔ x = n := by
  rw [Den_terminal_iff (ofNoun_terminal n), ofNoun_noun]
end Nock.Verb
