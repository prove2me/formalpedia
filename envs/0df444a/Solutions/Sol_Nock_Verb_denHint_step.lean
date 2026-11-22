-- Prove2me | solution 1 for Nock.Verb.denHint_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:52.434548+00:00
-- url     : https://prove2.me/submissions/f04a3be9-a157-40d5-a5c7-8c632e58ad9a

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_denHint_local
public import Theorems.Thm_Nock_Verb_nextHint_eq_some_iff
public import Theorems.Thm_Nock_Verb_Rel_den
public import Theorems.Thm_Nock_Verb_replaceAux_rel


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v v' : Verb} (hwf : editOk v = true) (h : nextHint v = some v') {r : Noun} :
    (∃ fuel, den fuel v = some r) ↔ (∃ fuel, den fuel v' = some r) := by
  obtain ⟨i, sub, r₀, hmax, hmap, hdom, hred, hv'⟩ := nextHint_eq_some_iff.1 h
  obtain ⟨w, hmapw, hpw⟩ := hmax.1
  have hpsub : Verb.isPending sub = true := (Option.some.inj (hmapw.symm.trans hmap)) ▸ hpw
  have hrel : Rel v v' := by
    rw [hv', replaceAt]
    apply replaceAux_rel i r₀ v 0
    intro s hs
    have hms : map i v = some s := hs
    have hss : s = sub := Option.some.inj (hms.symm.trans hmap)
    subst hss
    exact ⟨hpsub, fun x => denHint_local hdom hred⟩
  exact Rel_den v.noun.size v v' (Nat.le_refl _) hrel hwf r
end Nock.Verb
