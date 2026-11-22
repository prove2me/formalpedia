-- Prove2me | solution 1 for Nock.Verb.editOk_redexHint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:51.115424+00:00
-- url     : https://prove2.me/submissions/e0a5f829-c586-431f-80a3-b3363d48cee8

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_editOk_hintExpand
public import Theorems.Thm_Nock_Verb_editOk_reduce


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {sub r₀} (hr : redexHint sub = some r₀) (hok : editOk sub = true) :
    editOk r₀ = true := by
  cases he : hintExpand sub with
  | some e =>
      have hre : r₀ = e := by
        unfold redexHint at hr; rw [he] at hr; exact (Option.some.inj hr).symm
      subst hre; exact editOk_hintExpand he
  | none =>
      have hr' : reduce sub = some r₀ := by unfold redexHint at hr; rw [he] at hr; exact hr
      exact editOk_reduce hr' hok
end Nock.Verb
