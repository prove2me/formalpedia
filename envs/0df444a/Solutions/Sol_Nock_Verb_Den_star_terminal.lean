-- Prove2me | solution 1 for Nock.Verb.Den_star_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:54.438167+00:00
-- url     : https://prove2.me/submissions/1cbf2d81-de82-4bc3-b1c6-2e29605b399a

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_Den_star
public import Theorems.Thm_Nock_Verb_Den_terminal_iff


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {n1 t x} (h1 : isTerminal n1 = true) (ht : isTerminal t = true) :
    Den (.node .star n1 t) x ↔ Ev n1.noun t.noun x := by
  rw [Den_star]
  constructor
  · rintro ⟨a, b, ha, hb, hev⟩
    rw [(Den_terminal_iff h1).1 ha] at hev
    rw [(Den_terminal_iff ht).1 hb] at hev
    exact hev
  · intro hev
    exact ⟨n1.noun, t.noun, (Den_terminal_iff h1).2 rfl, (Den_terminal_iff ht).2 rfl, hev⟩
end Nock.Verb
