-- Prove2me | solution 1 for Nock.Verb.vcostN_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:27:16.923081+00:00
-- url     : https://prove2.me/submissions/b07106f1-a289-4b77-b7d2-5ce5b9624764

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_vcostN_succ
public import Theorems.Thm_Nock_Verb_RelP_refl
public import Theorems.Thm_Nock_Verb_Rel_refl
public import Theorems.Thm_Nock_Verb_den_mono


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F G : Nat} {v : Verb} {x : Noun}
    (hle : F ≤ G) (hok : editOk v = true) (hv : den F v = some x) : vcostN G v = vcostN F v := by
  induction hle with
  | refl => rfl
  | @step m h ih => rw [vcostN_succ hok (den_mono h hv)]; exact ih
end Nock.Verb
