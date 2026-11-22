-- Prove2me | solution 1 for Nock.Verb.vcostN_star_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:05:44.944465+00:00
-- url     : https://prove2.me/submissions/0ecf8fe0-316e-4bc7-bc55-bd0aaf49ab3c

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F : Nat} {l r : Verb} : vcostN F (Verb.node .star l r) =
    (match den F l, den F r with | some sa, some fo => ncost F sa fo | _, _ => 0)
      + vcostN F l + vcostN F r := rfl
end Nock.Verb
