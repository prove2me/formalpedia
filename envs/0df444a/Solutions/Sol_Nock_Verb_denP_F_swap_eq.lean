-- Prove2me | solution 1 for Nock.Verb.denP_F_swap_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:20.703025+00:00
-- url     : https://prove2.me/submissions/58c3630d-bcb5-4f4b-beee-e04f6d76f9ae

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_Rel_denP
public import Theorems.Thm_Nock_Verb_denP_det


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F : Nat} {w w' : Verb} (hok : editOk w = true) (hrel : RelP w w')
    {a b : Noun} (ha : denP F w = some a) (hb : denP F w' = some b) : a = b := by
  have hiff := Rel_denP w.noun.size w w' (Nat.le_refl _) hrel hok a
  exact denP_det (hiff.1 ⟨F, ha⟩) ⟨F, hb⟩
end Nock.Verb
