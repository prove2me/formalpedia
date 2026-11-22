-- Prove2me | solution 1 for Nock.Verb.next_eq_some_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:24.709822+00:00
-- url     : https://prove2.me/submissions/bdfa3e35-4d17-4a4d-a385-68bea5807c52

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_getIndex_eq_some_iff

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {a b : Verb} : next a = some b ↔ SelStep dfsLt a b := by
  constructor
  · intro h
    unfold next at h
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
    unfold next
    simp only [hgi, hmap, hdom, hred, ite_true]
    rw [hb]
end Nock.Verb
