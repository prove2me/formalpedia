-- Prove2me | solution 1 for Nock.Verb.den_stepP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:37.748993+00:00
-- url     : https://prove2.me/submissions/02af6e55-59c7-48d8-8858-1808de72e3c9

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_replaceAux_relP
public import Theorems.Thm_Nock_Verb_Rel_denP
public import Theorems.Thm_Nock_Verb_den_localP
public import Theorems.Thm_Nock_Verb_next_eq_some_iff


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v v' : Verb} (hwf : editOk v = true) (h : next v = some v') {r : Noun} :
    (∃ fuel, denP fuel v = some r) ↔ (∃ fuel, denP fuel v' = some r) := by
  obtain ⟨i, sub, r₀, hmax, hmap, hdom, hred, hv'⟩ := next_eq_some_iff.1 h
  obtain ⟨w, hmapw, hpw⟩ := hmax.1
  have hpsub : Verb.isPending sub = true := (Option.some.inj (hmapw.symm.trans hmap)) ▸ hpw
  have hrel : RelP v v' := by
    rw [hv', replaceAt]
    apply replaceAux_relP i r₀ v 0
    intro s hs
    have hms : map i v = some s := hs
    have hss : s = sub := Option.some.inj (hms.symm.trans hmap)
    subst hss
    exact ⟨hpsub, fun x => den_localP hdom hred⟩
  exact Rel_denP v.noun.size v v' (Nat.le_refl _) hrel hwf r
end Nock.Verb
