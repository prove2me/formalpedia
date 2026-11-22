-- Prove2me | solution 1 for Nock.Verb.denP_triple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:43.044893+00:00
-- url     : https://prove2.me/submissions/7880aa4d-33c0-426b-954f-0b69732e37ff

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
theorem _root_.solution {a b c va vb vc} (ha : DenP a va) (hb : DenP b vb) (hc : DenP c vc) :
    ∃ f, denP f a = some va ∧ denP f b = some vb ∧ denP f c = some vc := by
  obtain ⟨fa, ha⟩ := ha; obtain ⟨fb, hb⟩ := hb; obtain ⟨fc, hc⟩ := hc
  refine ⟨max fa (max fb fc), denP_mono (by omega) ha, denP_mono (by omega) hb,
    denP_mono (by omega) hc⟩
end Nock.Verb
