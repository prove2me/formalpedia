-- Prove2me | solution 1 for Nock.Verb.den_triple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:17.847243+00:00
-- url     : https://prove2.me/submissions/a18153c2-9065-4392-b1b6-e059cd64919a

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
theorem _root_.solution {a b c va vb vc} (ha : Den a va) (hb : Den b vb) (hc : Den c vc) :
    ∃ f, den f a = some va ∧ den f b = some vb ∧ den f c = some vc := by
  obtain ⟨fa, ha⟩ := ha; obtain ⟨fb, hb⟩ := hb; obtain ⟨fc, hc⟩ := hc
  refine ⟨max fa (max fb fc), den_mono (by omega) ha, den_mono (by omega) hb, den_mono (by omega)
    hc⟩
end Nock.Verb
