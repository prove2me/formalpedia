-- Prove2me | solution 1 for Nock.Verb.vcost_star_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:02.846392+00:00
-- url     : https://prove2.me/submissions/8ab162d6-400d-40bf-9be6-072c464d92b5

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_vcost_star_eq
public import Theorems.Thm_Nock_Verb_vcost_terminal


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F : Nat} {A B : Verb}
    (hA : isTerminal A = true) (hB : isTerminal B = true)
    (hdA : denP F A = some A.noun) (hdB : denP F B = some B.noun) :
    vcost F (Verb.node .star A B) = pcost F A.noun B.noun := by
  simp only [vcost_star_eq, hdA, hdB, vcost_terminal A hA F, vcost_terminal B hB F, Nat.add_zero]
end Nock.Verb
