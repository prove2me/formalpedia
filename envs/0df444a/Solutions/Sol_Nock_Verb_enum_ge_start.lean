-- Prove2me | solution 1 for Nock.Verb.enum_ge_start
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:19.969667+00:00
-- url     : https://prove2.me/submissions/cfab8190-d0b2-4c5d-83a1-fff898cd14af

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution (v : Verb) (c : Nat) : c ≤ (enum v c).1 := by
  induction v generalizing c with
  | leaf n => simp [enum]
  | node a l r ihl ihr =>
      simp only [enum]
      have h1 : c + 1 ≤ (enum l (c + 1)).1 := ihl (c + 1)
      have h2 : (enum l (c + 1)).1 ≤ (enum r (enum l (c + 1)).1).1 := ihr _
      omega
end Nock.Verb
