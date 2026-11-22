-- Prove2me | solution 1 for Nock.Verb.den_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:34.56092+00:00
-- url     : https://prove2.me/submissions/22d7cbd0-2e64-403d-8234-83cf76a79d2f

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_den_mono

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v r1 r2} (h1 : Den v r1) (h2 : Den v r2) : r1 = r2 := by
  obtain ⟨f1, h1⟩ := h1; obtain ⟨f2, h2⟩ := h2
  have k1 := den_mono (Nat.le_max_left f1 f2) h1
  have k2 := den_mono (Nat.le_max_right f1 f2) h2
  exact Option.some.inj (k1.symm.trans k2)
end Nock.Verb
