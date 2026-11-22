-- Prove2me | solution 1 for Nock.Verb.next_of_nextROM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:40.690279+00:00
-- url     : https://prove2.me/submissions/b5491ce6-465a-4a2d-8d71-0316534d397c

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_reduce_of_reduceROM

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {v w : Verb} (h : nextROM v = some w) : next v = some w := by
  unfold nextROM at h
  unfold next
  cases hg : getIndex v with
  | none => simp only [hg] at h ⊢; exact h
  | some i =>
      simp only [hg] at h ⊢
      cases hm : map i v with
      | none => simp only [hm] at h ⊢; exact h
      | some sub =>
          simp only [hm] at h ⊢
          by_cases hd : inDomain sub = true
          · simp only [if_pos hd] at h ⊢
            cases hr : reduceROM sub with
            | none => simp only [hr] at h; simp at h
            | some r =>
                simp only [hr] at h
                simp only [reduce_of_reduceROM hr]
                exact h
          · simp only [if_neg hd] at h ⊢; exact h
end Nock.Verb
