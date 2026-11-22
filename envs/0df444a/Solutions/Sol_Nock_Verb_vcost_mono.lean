-- Prove2me | solution 1 for Nock.Verb.vcost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:56.600793+00:00
-- url     : https://prove2.me/submissions/1a93e1c2-f23a-4247-98a3-c594c5ef8b69

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_vcost_succ
public import Theorems.Thm_Nock_Verb_RelP_refl
public import Theorems.Thm_Nock_Verb_Rel_refl
public import Theorems.Thm_Nock_Verb_denP_mono


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F G : Nat} {v : Verb} {x : Noun}
    (hle : F ≤ G) (hok : editOk v = true) (hv : denP F v = some x) : vcost G v = vcost F v := by
  induction hle with
  | refl => rfl
  | @step m h ih => rw [vcost_succ hok (denP_mono h hv)]; exact ih
end Nock.Verb
