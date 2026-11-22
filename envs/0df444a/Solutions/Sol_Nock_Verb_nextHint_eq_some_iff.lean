-- Prove2me | solution 1 for Nock.Verb.nextHint_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:28.122475+00:00
-- url     : https://prove2.me/submissions/4440a0fb-cbd8-407e-83be-145a3936d80e

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_getIndex_eq_some_iff


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {a b : Verb} : nextHint a = some b ↔
    ∃ i sub r, IsMaxPending dfsLt a i ∧ map i a = some sub ∧ inDomainHint sub = true
      ∧ redexHint sub = some r ∧ b = replaceAt i a r := by
  constructor
  · intro h
    unfold nextHint at h
    split at h
    · simp at h
    · rename_i i hgi
      split at h
      · simp at h
      · rename_i sub hmap
        split at h
        · rename_i hdom
          split at h
          · rename_i r hred
            exact ⟨i, sub, r, getIndex_eq_some_iff.1 hgi, hmap, hdom, hred, (Option.some.inj
              h).symm⟩
          · simp at h
        · simp at h
  · rintro ⟨i, sub, r, hmax, hmap, hdom, hred, hb⟩
    have hgi : getIndex a = some i := getIndex_eq_some_iff.2 hmax
    unfold nextHint
    simp only [hgi, hmap, hdom, hred, ite_true]
    rw [hb]
end Nock.Verb
