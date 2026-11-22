-- Prove2me | solution 1 for Nock.Verb.isTerminal_of_map_ofNoun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:14:37.558859+00:00
-- url     : https://prove2.me/submissions/d1465314-73f8-43dc-be3c-7f0d844da094

module
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureComplete
public import Theorems.Thm_Nock_Verb_ofNoun_terminal


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {o : Option Noun} {r₀ : Verb}
    (h : o.map ofNoun = some r₀) : isTerminal r₀ = true := by
  rw [Option.map_eq_some_iff] at h; obtain ⟨w, _, rfl⟩ := h; exact ofNoun_terminal w
end Nock.Verb
