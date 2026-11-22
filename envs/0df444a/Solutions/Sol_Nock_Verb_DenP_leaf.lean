-- Prove2me | solution 1 for Nock.Verb.DenP_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:13:02.930652+00:00
-- url     : https://prove2.me/submissions/dafc5d03-06b9-4ee6-8c16-2c965617258c

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {k x} : DenP (.leaf k) x ↔ x = .atom k := by
  constructor
  · rintro ⟨fuel, h⟩; simp only [denP] at h; exact (Option.some.inj h).symm
  · rintro rfl; exact ⟨0, by simp [denP]⟩
end Nock.Verb
