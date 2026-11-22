-- Prove2me | solution 1 for Nock.Verb.den_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:23.593915+00:00
-- url     : https://prove2.me/submissions/3d03cf7c-0754-43ec-bd4e-2d8941626303

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
theorem _root_.solution {l r a b} (hl : Den l a) (hr : Den r b) :
    ∃ f, den f l = some a ∧ den f r = some b := by
  obtain ⟨fl, hl⟩ := hl; obtain ⟨fr, hr⟩ := hr
  exact ⟨max fl fr, den_mono (Nat.le_max_left _ _) hl, den_mono (Nat.le_max_right _ _) hr⟩
end Nock.Verb
