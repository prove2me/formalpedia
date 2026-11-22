-- Prove2me | solution 1 for Nock.Verb.editOk_nextHint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:27.381725+00:00
-- url     : https://prove2.me/submissions/a45a7637-fb34-45fc-a92f-c52b19986eb4

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_editOk_redexHint
public import Theorems.Thm_Nock_Verb_nextHint_eq_some_iff
public import Theorems.Thm_Nock_Verb_editOk_enum
public import Theorems.Thm_Nock_Verb_editOk_replaceAux
public import Theorems.Thm_Nock_Verb_mem_nodes_of_map


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v v'} (h : nextHint v = some v') (hok : editOk v = true) :
    editOk v' = true := by
  obtain ⟨i, sub, r₀, hmax, hmap, hdom, hred, hv'⟩ := nextHint_eq_some_iff.1 h
  have hoksub : editOk sub = true := editOk_enum v 0 hok (i, sub) (mem_nodes_of_map hmap)
  have hokr0 : editOk r₀ = true := editOk_redexHint hred hoksub
  obtain ⟨w, hmapw, hpw⟩ := hmax.1
  have hpsub : Verb.isPending sub = true := (Option.some.inj (hmapw.symm.trans hmap)) ▸ hpw
  rw [hv', replaceAt]
  apply editOk_replaceAux i r₀ hokr0 v 0 hok
  intro s hs
  have hms : map i v = some s := hs
  exact (Option.some.inj (hms.symm.trans hmap)) ▸ hpsub
end Nock.Verb
