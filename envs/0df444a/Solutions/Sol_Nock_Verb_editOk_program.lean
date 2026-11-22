-- Prove2me | solution 1 for Nock.Verb.editOk_program
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:08.325917+00:00
-- url     : https://prove2.me/submissions/239df342-e087-4733-872d-4d9cbb30e6c4

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_editOk_ofNoun

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (s f : Noun) : editOk (program s f) = true := by
  simp [program, editOk, editOk_ofNoun]
end Nock.Verb
