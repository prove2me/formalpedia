-- Prove2me | solution 1 for Nock.Verb.denP_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:31.872676+00:00
-- url     : https://prove2.me/submissions/e8a58b57-ecc8-49f9-b96a-255d30455e95

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_denP_mono

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v r1 r2} (h1 : DenP v r1) (h2 : DenP v r2) : r1 = r2 := by
  obtain ⟨f1, h1⟩ := h1; obtain ⟨f2, h2⟩ := h2
  have k1 := denP_mono (Nat.le_max_left f1 f2) h1
  have k2 := denP_mono (Nat.le_max_right f1 f2) h2
  exact Option.some.inj (k1.symm.trans k2)
end Nock.Verb
