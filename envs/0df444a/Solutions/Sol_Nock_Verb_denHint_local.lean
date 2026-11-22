-- Prove2me | solution 1 for Nock.Verb.denHint_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:26.879379+00:00
-- url     : https://prove2.me/submissions/a65ac222-cc53-4b79-9bf4-1aff8428f537

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_reduce_none_of_isHintRedex
public import Theorems.Thm_Nock_Verb_denHint_expand
public import Theorems.Thm_Nock_Verb_den_local


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {sub r₀ x} (hd : inDomainHint sub = true) (hr : redexHint sub = some r₀) :
    (Den sub x ↔ Den r₀ x) := by
  cases he : hintExpand sub with
  | some e =>
      have hre : r₀ = e := by
        unfold redexHint at hr; rw [he] at hr; exact (Option.some.inj hr).symm
      subst hre; exact denHint_expand he
  | none =>
      have hr' : reduce sub = some r₀ := by unfold redexHint at hr; rw [he] at hr; exact hr
      have hin : inDomain sub = true := by
        rw [inDomainHint, Bool.or_eq_true] at hd
        rcases hd with h | h
        · exact h
        · have hnone := reduce_none_of_isHintRedex h
          rw [hnone] at hr'; exact absurd hr' (by simp)
      exact den_local hin hr'
end Nock.Verb
