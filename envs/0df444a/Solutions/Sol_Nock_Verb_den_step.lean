-- Prove2me | solution 1 for Nock.Verb.den_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:20.516428+00:00
-- url     : https://prove2.me/submissions/b24fec16-3051-400a-b453-298e734337ba

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_replaceAux_rel
public import Theorems.Thm_Nock_Verb_Rel_den
public import Theorems.Thm_Nock_Verb_den_local
public import Theorems.Thm_Nock_Verb_next_eq_some_iff


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v v' : Verb} (hwf : editOk v = true) (h : next v = some v') {r : Noun} :
    (∃ fuel, den fuel v = some r) ↔ (∃ fuel, den fuel v' = some r) := by
  obtain ⟨i, sub, r₀, hmax, hmap, hdom, hred, hv'⟩ := next_eq_some_iff.1 h
  obtain ⟨w, hmapw, hpw⟩ := hmax.1
  have hpsub : Verb.isPending sub = true := (Option.some.inj (hmapw.symm.trans hmap)) ▸ hpw
  have hrel : Rel v v' := by
    rw [hv', replaceAt]
    apply replaceAux_rel i r₀ v 0
    intro s hs
    have hms : map i v = some s := hs
    have hss : s = sub := Option.some.inj (hms.symm.trans hmap)
    subst hss
    exact ⟨hpsub, fun x => den_local hdom hred⟩
  exact Rel_den v.noun.size v v' (Nat.le_refl _) hrel hwf r
end Nock.Verb
