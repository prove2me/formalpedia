-- Prove2me | solution 1 for Nock.Verb.editOk_children
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:00:34.777558+00:00
-- url     : https://prove2.me/submissions/75dd7f1e-d661-4d83-a715-66c0579b0baa

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {a l r} (h : editOk (.node a l r) = true) :
    editOk l = true ∧ editOk r = true := by
  simp only [editOk, Bool.and_eq_true] at h; exact ⟨h.1.2, h.2⟩
end Nock.Verb
