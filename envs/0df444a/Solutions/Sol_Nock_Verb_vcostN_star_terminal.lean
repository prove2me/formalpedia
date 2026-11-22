-- Prove2me | solution 1 for Nock.Verb.vcostN_star_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:26:08.458453+00:00
-- url     : https://prove2.me/submissions/4d9b5851-b7ea-4ab4-b524-86e2858b8836

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_vcostN_star_eq
public import Theorems.Thm_Nock_Verb_vcostN_terminal

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F : Nat} {A B : Verb}
    (hA : isTerminal A = true) (hB : isTerminal B = true)
    (hdA : den F A = some A.noun) (hdB : den F B = some B.noun) :
    vcostN F (Verb.node .star A B) = ncost F A.noun B.noun := by
  simp only [vcostN_star_eq, hdA, hdB, vcostN_terminal A hA F, vcostN_terminal B hB F, Nat.add_zero]
end Nock.Verb
