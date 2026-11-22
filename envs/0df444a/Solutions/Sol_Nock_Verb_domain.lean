-- Prove2me | solution 1 for Nock.Verb.domain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:24.107832+00:00
-- url     : https://prove2.me/submissions/a5df39bf-2517-473e-a756-1c81e56beb14

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {c t : Verb} (h : Step c t) :
    ∃ i sub, getIndex c = some i ∧ map i c = some sub ∧ inDomain sub = true := by
  unfold Step next at h
  split at h
  · simp at h
  · rename_i i hg
    split at h
    · simp at h
    · rename_i sub hm
      split at h
      · rename_i hd
        exact ⟨i, sub, hg, hm, hd⟩
      · simp at h
end Nock.Verb
