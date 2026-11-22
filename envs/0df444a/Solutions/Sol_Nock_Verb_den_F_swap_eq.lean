-- Prove2me | solution 1 for Nock.Verb.den_F_swap_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:26:12.50179+00:00
-- url     : https://prove2.me/submissions/e924a432-adca-4b4b-8186-3b96b0461496

module
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureCompleteHint
public import Theorems.Thm_Nock_Verb_Rel_den
public import Theorems.Thm_Nock_Verb_den_det


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {F : Nat} {w w' : Verb} (hok : editOk w = true) (hrel : Rel w w')
    {a b : Noun} (ha : den F w = some a) (hb : den F w' = some b) : a = b := by
  have hiff := Rel_den w.noun.size w w' (Nat.le_refl _) hrel hok a
  exact den_det (hiff.1 ⟨F, ha⟩) ⟨F, hb⟩
end Nock.Verb
